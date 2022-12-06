pub mod prelude {
	pub use super::{In, InExt, Bytes};
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
	#[error("mismatched {type_} at {pos:#X}\n  got:      {got}\n  expected: {expected}")]
	Check { pos: usize, type_: String, got: String, expected: String },
}
pub type Result<T, E=Error> = std::result::Result<T, E>;

impl Error {
	pub fn pos(&self) -> usize {
		match self {
			Error::Seek { pos, .. } => *pos,
			Error::Read { pos, .. } => *pos,
			Error::Check { pos, .. } => *pos,
		}
	}
}

macro_rules! primitives {
	($suf:ident, $conv:ident; { $($type:ident),* }) => { paste::paste! {
		$(
			fn [<$type $suf>](&mut self) -> Result<$type> {
				Ok($type::$conv(self.array()?))
			}
		)*
	} }
}

macro_rules! primitives_check {
	($suf:ident; { $($type:ident),* }) => { paste::paste! {
		$(
			fn [<check_ $type $suf>](&mut self, v: $type) -> Result<()> {
				let pos = self.pos();
				let u = self.[< $type $suf >]()?;
				if u != v {
					let _ = self.seek(pos);
					return Err(Error::Check {
						pos,
						type_: stringify!($type).to_owned(),
						got: u.to_string(),
						expected: v.to_string(),
					})
				}
				Ok(())
			}
		)*
	} }
}

#[allow(clippy::len_without_is_empty)]
pub trait In<'a> {
	fn pos(&self) -> usize;
	fn len(&self) -> usize;
	fn seek(&mut self, pos: usize) -> Result<()>;
	fn slice(&mut self, len: usize) -> Result<&'a [u8]>;
}

#[cfg(feature="beryl")]
pub trait Dump {
	fn dump(&self) -> beryl::Dump;
}

pub trait InExt<'a>: In<'a> {
	fn remaining(&self) -> usize {
		self.len() - self.pos()
	}

	fn at(mut self, pos: usize) -> Result<Self> where Self: Sized {
		self.seek(pos)?;
		Ok(self)
	}

	fn array<const N: usize>(&mut self) -> Result<[u8; N]> {
		Ok(self.slice(N)?.try_into().unwrap())
	}

	fn align(&mut self, size: usize) -> Result<()> {
		self.slice((size-(self.pos()%size))%size)?;
		Ok(())
	}

	fn check(&mut self, v: &[u8]) -> Result<()> {
		let pos = self.pos();
		let u = self.slice(v.len())?;
		if u != v {
			let _ = self.seek(pos);
			let mut got = Vec::new();
			let mut exp = Vec::new();
			for (&g, &e) in std::iter::zip(u, v) {
				got.extend(std::ascii::escape_default(g).map(char::from));
				exp.extend(std::ascii::escape_default(e).map(char::from));
				while got.len() < exp.len() { got.push('░') }
				while exp.len() < got.len() { exp.push('░') }
			}
			return Err(Error::Check {
				pos,
				type_:    format!("[u8; {}]", v.len()),
				got:      format!("b\"{}\"", got.into_iter().collect::<String>()),
				expected: format!("b\"{}\"", exp.into_iter().collect::<String>()),
			})
		}
		Ok(())
	}

	primitives!(_le, from_le_bytes; { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
	primitives!(_be, from_be_bytes; { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
	primitives_check!(_le; { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
	primitives_check!(_be; { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
}

impl<'a, T> InExt<'a> for T where T: In<'a> + ?Sized {}

macro_rules! primitives_alias {
	(
		$mod:ident, $suf:ident;
		$trait:ident { $($type:ident),* }
	) => { paste::paste! {
		pub trait $trait<'a>: In<'a> {
			$(
				fn $type(&mut self) -> Result<$type> {
					self.[<$type $suf>]()
				}
			)*

			$(
				fn [<check_ $type>](&mut self, v: $type) -> Result<()> {
					self.[<check_ $type $suf>](v)
				}
			)*
		}
		impl<'a, T> $trait<'a> for T where T: In<'a> + ?Sized {}

		pub mod $mod {
			pub use super::prelude::*;
			pub use super::$trait;
		}
	} }
}

primitives_alias!(le, _le; InExtLe { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
primitives_alias!(be, _be; InExtBe { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });

#[derive(Clone)]
pub struct Bytes<'a> {
	data: &'a [u8],
	pos: usize,
}

impl<'a> Bytes<'a> {
	pub fn new(data: &'a [u8]) -> Self {
		Self {
			data,
			pos: 0,
		}
	}
}

impl<'a> In<'a> for Bytes<'a> {
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

	fn slice(&mut self, len: usize) -> Result<&'a [u8]> {
		if len > self.remaining() {
			return Err(Error::Read { pos: self.pos(), len, size: self.len() });
		}
		let pos = self.pos;
		self.pos += len;
		Ok(&self.data[pos..pos+len])
	}
}

#[cfg(feature="beryl")]
impl Dump for Bytes<'_> {
	fn dump(&self) -> beryl::Dump {
		let mut cursor = std::io::Cursor::new(&self.data);
		cursor.set_position(self.pos as u64);
		beryl::Dump::new(cursor, self.pos)
			.num_width_from(self.len())
	}
}
