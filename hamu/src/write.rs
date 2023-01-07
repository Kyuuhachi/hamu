use std::{
	hash::Hash,
	collections::HashMap,
	fmt::Debug,
	ops::Range,
	num::TryFromIntError,
};

pub mod prelude {
	pub use super::{WriteStream, WriteStremExt, Write, WriteExt, Label, Writer};
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
	#[error("undefined label '{label}'")]
	Undefined { label: String },
	#[error("failed to convert {value} to {type_}")]
	LabelSize {
		type_: &'static str,
		value: String,
	},
	#[error(transparent)]
	Other { error: Box<dyn std::error::Error + Send + Sync> },
}
pub type Result<T, E=Error> = std::result::Result<T, E>;

macro_rules! primitives {
	($suf: ident, $conv:ident; { $($type:ident),* }) => { paste::paste! {
		$(
			fn [<$type $suf>](&mut self, v: $type) {
				self.array(v.$conv());
			}
		)*
	} }
}

macro_rules! primitives_delay {
	($suf: ident, $conv:ident; { $($type:ident),* }) => { paste::paste! {
		$(
			fn [<delay_ $type $suf>](&mut self, k: Label) where Self: Write {
				self.delay(move |lookup| {
					let v = lookup(k.clone())?;
					let v = cast_usize::<$type>(v)?;
					Ok(v.$conv())
				});
			}
		)*
	} }
}

#[allow(clippy::len_without_is_empty)]
pub trait WriteStream {
	fn len(&self) -> usize;
	fn slice(&mut self, data: &[u8]);
}

pub trait Write: WriteStream {
	fn label(&mut self, label: LabelDef);
	fn delay<const N: usize, F>(&mut self, cb: F) where
		F: FnOnce(&dyn Fn(Label) -> Result<usize>) -> Result<[u8; N]> + 'static;
}

pub trait WriteStremExt: WriteStream {
	fn is_empty(&self) -> bool {
		self.len() == 0
	}

	fn array<const N: usize>(&mut self, data: [u8; N]) {
		self.slice(&data)
	}

	fn align(&mut self, size: usize) {
		self.slice(&vec![0;(size-(self.len()%size))%size]);
	}

	primitives!(_le, to_le_bytes; { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
	primitives!(_be, to_be_bytes; { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 });
}
impl<T> WriteStremExt for T where T: WriteStream + ?Sized {}

pub trait WriteExt: Write {
	fn here(&mut self) -> Label {
		let (l, l_) = Label::new();
		self.label(l_);
		l
	}

	primitives_delay!(_le, to_le_bytes; { u8, u16, u32, u64, u128 });
	primitives_delay!(_be, to_be_bytes; { u8, u16, u32, u64, u128 });
}
impl<T> WriteExt for T where T: Write + ?Sized {}

type Delayed = Box<dyn FnOnce(&dyn Fn(Label) -> Result<usize>, &mut [u8]) -> Result<()>>;

#[derive(Default)]
#[must_use]
pub struct Writer {
	data: Vec<u8>,
	delays: Vec<(Range<usize>, Delayed)>,
	labels: HashMap<LabelDef, usize>,
}

impl Writer {
	pub fn new() -> Self {
		Self {
			data: Vec::new(),
			delays: Vec::new(),
			labels: HashMap::new(),
		}
	}

	pub fn finish(mut self) -> Result<Vec<u8>> {
		for (range, cb) in self.delays {
			cb(
				&|k| {
					self.labels.get(&LabelDef(k.0))
						.copied()
						.ok_or_else(|| Error::Undefined {
							label: format!("{:?}", k),
						})
				},
				&mut self.data[range],
			)?;
		}
		Ok(self.data)
	}

	#[deprecated]
	pub fn concat(mut self, other: Writer) -> Self {
		self.append(other);
		self
	}

	pub fn append(&mut self, mut other: Writer) {
		let shift = self.len();
		self.data.append(&mut other.data);

		for (range, cb) in other.delays {
			let range = range.start+shift..range.end+shift;
			self.delays.push((range, cb))
		}

		for (k, v) in other.labels {
			self.labels.insert(k, v+shift);
		}
	}
}

impl WriteStream for Writer {
	fn len(&self) -> usize {
		self.data.len()
	}

	fn slice(&mut self, data: &[u8]) {
		self.data.extend(data)
	}
}

impl Write for Writer {
	fn label(&mut self, label: LabelDef) {
		self.labels.insert(label, self.len());
	}

	fn delay<const N: usize, F>(&mut self, cb: F) where
		F: FnOnce(&dyn Fn(Label) -> Result<usize>) -> Result<[u8; N]> + 'static,
	{
		let start = self.len();
		self.array([0; N]);
		let end = self.len();
		self.delays.push((start..end, Box::new(move |lookup, slice| {
			slice.copy_from_slice(&cb(lookup)?);
			Ok(())
		})));
	}
}

macro_rules! primitives_alias {
	(
		$mod:ident, $suf:ident;
		$trait:ident { $($type:ident),* };
		$delay_trait:ident { $($delay_type:ident),* }
	) => { paste::paste! {
		pub trait $trait: WriteStream {
			$(
				fn $type(&mut self, v: $type) {
					self.[<$type $suf>](v);
				}
			)*
		}
		impl<T> $trait for T where T: WriteStream + ?Sized {}

		pub trait $delay_trait: Write {
			$(
				fn [<delay_ $delay_type>](&mut self, k: Label) {
					self.[<delay_ $delay_type $suf>](k);
				}
			)*
		}
		impl<T> $delay_trait for T where T: Write + ?Sized {}

		pub mod $mod {
			pub use super::prelude::*;
			pub use super::$trait;
			pub use super::$delay_trait;
		}
	} }
}

primitives_alias!(
	le, _le;
	OutExtLe { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 };
	OutDelayExtLe { u8, u16, u32, u64, u128 }
);
primitives_alias!(
	be, _be;
	OutExtBe { u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, f32, f64 };
	OutDelayExtBe { u8, u16, u32, u64, u128 }
);

pub fn cast_usize<T: TryFrom<usize, Error=TryFromIntError>>(v: usize) -> Result<T> {
	T::try_from(v).map_err(|_| Error::LabelSize {
		type_: std::any::type_name::<T>(),
		value: format!("{:?}", v),
	})
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Label(u64);
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LabelDef(u64);

impl Debug for Label {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Label(0x{:04X})", self.0)
	}
}

impl Debug for LabelDef {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "LabelDef(0x{:04X})", self.0)
	}
}

impl Label {
	#[allow(clippy::new_without_default)]
	pub fn new() -> (Label, LabelDef) {
		use std::sync::atomic::{AtomicU64, Ordering};
		static COUNT: AtomicU64 = AtomicU64::new(0);
		let n = COUNT.fetch_add(1, Ordering::Relaxed);
		(Label(n), LabelDef(n))
	}

	pub fn known(n: u32) -> (Label, LabelDef) {
		let n = n as u64 | 0xFFFFFFFF00000000;
		(Label(n), LabelDef(n))
	}
}
