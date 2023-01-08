pub mod prelude {
	pub use super::{ReadStream, ReadStreamExt, Read, ReadExt, Reader};
	#[cfg(feature="beryl")]
	pub use super::Dump;
}

pub mod coverage;

#[derive(Debug, thiserror::Error)]
pub enum Error {
	#[error("out-of-bounds seek to {pos:#X} (size {size:#X})")]
	Seek { pos: usize, size: usize },
	#[error("out-of-bounds read of {pos:#X}+{len} (size {size:#X})")]
	Read { pos: usize, len: usize, size: usize },
	#[error("error at {pos:#X}: {source}")]
	Other { pos: usize, #[source] source: Box<dyn std::error::Error + Send + Sync> },
}

pub type Result<T, E=Error> = std::result::Result<T, E>;

impl Error {
	pub fn pos(&self) -> usize {
		match self {
			Error::Seek { pos, .. } => *pos,
			Error::Read { pos, .. } => *pos,
			Error::Other { pos, .. } => *pos,
		}
	}

	pub fn pos_mut(&mut self) -> &mut usize {
		match self {
			Error::Seek { pos, .. } => pos,
			Error::Read { pos, .. } => pos,
			Error::Other { pos, .. } => pos,
		}
	}
}

#[derive(Clone, Debug, thiserror::Error)]
#[error("mismatched {type_}. expected: {expected}, got: {got}", type_ = std::any::type_name::<T>())]
pub struct Check<T: std::fmt::Display> {
	pub expected: T,
	pub got: T,
}

#[derive(Clone, Debug, thiserror::Error)]
pub struct CheckBytes {
	pub expected: Vec<u8>,
	pub got: Vec<u8>,
}

impl std::fmt::Display for CheckBytes {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mut got = Vec::new();
		let mut exp = Vec::new();
		for (&g, &e) in std::iter::zip(&self.got, &self.expected) {
			got.extend(std::ascii::escape_default(g).map(char::from));
			exp.extend(std::ascii::escape_default(e).map(char::from));
			while got.len() < exp.len() { got.push('░') }
			while exp.len() < got.len() { exp.push('░') }
		}
		write!(f, "mismatched bytes.\n  expected: b\"{}\"\n  got:      b\"{}\"", String::from_iter(exp), String::from_iter(got))
	}
}

pub trait ReadStream {
	type Error;
	type ErrorState;

	fn fill(&mut self, buf: &mut [u8]) -> Result<(), Self::Error>;

	fn error_state(&self) -> Self::ErrorState;
	fn to_error(state: Self::ErrorState, err: Box<dyn std::error::Error + Send + Sync>) -> Self::Error;
}

macro_rules! primitives {
	($suf:ident, $conv:ident; { $($type:ident),* }) => { paste::paste! {
		$(
			fn [<$type $suf>](&mut self) -> Result<$type, Self::Error> {
				Ok($type::$conv(self.array()?))
			}
		)*
	} }
}

macro_rules! primitives_check {
	($suf:ident; { $($type:ident),* }) => { paste::paste! {
		$(
			fn [<check_ $type $suf>](&mut self, v: $type) -> Result<(), Self::Error> {
				let state = self.error_state();
				let u = self.[< $type $suf >]()?;
				if u != v {
					return Err(Self::to_error(state, Check {
						got: u,
						expected: v,
					}.into()))
				}
				Ok(())
			}
		)*
	} }
}

pub trait ReadStreamExt: ReadStream {
	fn array<const N: usize>(&mut self) -> Result<[u8; N], Self::Error> {
		let mut x = [0; N];
		self.fill(&mut x)?;
		Ok(x)
	}

	fn vec(&mut self, n: usize) -> Result<Vec<u8>, Self::Error> {
		let mut x = vec![0; n];
		self.fill(&mut x)?;
		Ok(x)
	}

	fn check(&mut self, v: &[u8]) -> Result<(), Self::Error> {
		let state = self.error_state();
		let u = self.vec(v.len())?;
		if u != v {
			return Err(Self::to_error(state, CheckBytes {
				got:      u,
				expected: v.to_owned(),
			}.into()))
		}
		Ok(())
	}

	primitives!(_le, from_le_bytes; { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
	primitives!(_be, from_be_bytes; { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
	primitives_check!(_le; { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
	primitives_check!(_be; { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
}
impl<T: ReadStream + ?Sized> ReadStreamExt for T {}

macro_rules! primitives_alias {
	(
		$mod:ident, $suf:ident;
		$trait:ident { $($type:ident),* }
	) => { paste::paste! {
		pub trait $trait: ReadStream {
			$(
				fn $type(&mut self) -> Result<$type, Self::Error> {
					self.[<$type $suf>]()
				}
			)*

			$(
				fn [<check_ $type>](&mut self, v: $type) -> Result<(), Self::Error> {
					self.[<check_ $type $suf>](v)
				}
			)*
		}
		impl<T> $trait for T where T: ReadStream + ?Sized {}

		pub mod $mod {
			pub use super::prelude::*;
			pub use super::$trait;
		}
	} }
}

primitives_alias!(le, _le; ReadLe { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
primitives_alias!(be, _be; ReadBe { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });

#[allow(clippy::len_without_is_empty)]
pub trait Read<'a>: ReadStream<Error=Error> + Clone {
	fn pos(&self) -> usize;
	fn len(&self) -> usize;
	fn seek(&mut self, pos: usize) -> Result<(), Self::Error>;
	fn slice(&mut self, len: usize) -> Result<&'a [u8], Self::Error>;
}

pub trait ReadExt<'a>: Read<'a> {
	fn remaining(&self) -> usize {
		self.len() - self.pos()
	}

	fn at(mut self, pos: usize) -> Result<Self, Self::Error> where Self: Sized {
		self.seek(pos)?;
		Ok(self)
	}

	fn align(&mut self, size: usize) -> Result<(), Self::Error> {
		self.slice((size-(self.pos()%size))%size)?;
		Ok(())
	}
}
impl<'a, T: Read<'a> + ?Sized> ReadExt<'a> for T {}

pub struct Io<T: std::io::Read>(T);

impl<T: std::io::Read> Io<T> {
	pub fn new(r: T) -> Self {
		Io(r)
	}

	pub fn inner(&self) -> &T {
		&self.0
	}

	pub fn inner_mut(&mut self) -> &mut T {
		&mut self.0
	}

	pub fn into_inner(self) -> T {
		self.0
	}
}

impl<T: std::io::Read> ReadStream for Io<T> {
	type Error = std::io::Error;
	type ErrorState = ();

	fn fill(&mut self, buf: &mut [u8]) -> Result<(), Self::Error> {
		self.0.read_exact(buf)
	}

	fn error_state(&self) { }

	fn to_error((): Self::ErrorState, err: Box<dyn std::error::Error + Send + Sync>) -> Self::Error {
		match err.downcast() {
			Ok(e) => *e,
			Err(err) => std::io::Error::new(std::io::ErrorKind::Other, err)
		}
	}
}

#[cfg(feature="beryl")]
pub trait Dump {
	fn dump(&self) -> beryl::Dump;
}

#[derive(Clone)]
pub struct Reader<'a> {
	data: &'a [u8],
	pos: usize,
}

impl<'a> Reader<'a> {
	pub fn new(data: &'a [u8]) -> Self {
		Self {
			data,
			pos: 0,
		}
	}
}

impl<'a> ReadStream for Reader<'a> {
	type Error = Error;

	type ErrorState = usize;

	fn fill(&mut self, buf: &mut [u8]) -> Result<(), Self::Error> {
		buf.copy_from_slice(self.slice(buf.len())?);
		Ok(())
	}

	fn error_state(&self) -> Self::ErrorState {
		self.pos()
	}

	fn to_error(pos: Self::ErrorState, err: Box<dyn std::error::Error + Send + Sync>) -> Self::Error {
		match err.downcast() {
			Ok(e) => *e,
			Err(err) => Error::Other { pos, source: err }
		}
	}
}

impl<'a> Read<'a> for Reader<'a> {
	fn slice(&mut self, len: usize) -> Result<&'a [u8]> {
		if len > self.remaining() {
			return Err(Error::Read { pos: self.pos(), len, size: self.len() });
		}
		let pos = self.pos;
		self.pos += len;
		Ok(&self.data[pos..pos+len])
	}

	fn pos(&self) -> usize {
		self.pos
	}

	fn len(&self) -> usize {
		self.data.len()
	}

	fn seek(&mut self, pos: usize) -> Result<()> {
		if pos > self.len() {
			return Err(Error::Seek { pos, size: self.len() })
		}
		self.pos = pos;
		Ok(())
	}
}

#[cfg(feature="beryl")]
impl Dump for Reader<'_> {
	fn dump(&self) -> beryl::Dump {
		let mut cursor = std::io::Cursor::new(&self.data);
		cursor.set_position(self.pos as u64);
		beryl::Dump::new(cursor, self.pos)
			.num_width_from(self.len())
	}
}
