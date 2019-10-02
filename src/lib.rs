//! IEEE 754-2008 Decimal Floating-Point Library
//!
//! A pure Rust implementation of decimal floating point defined in
//! [IEEE 754-2008](https://en.wikipedia.org/wiki/IEEE_754-2008_revision) standard (binary
//! encoding variant).
#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]

mod consts;

mod d128_impl;
mod d32_impl;
mod d64_impl;

use std::marker::PhantomData;
pub use std::num::FpCategory;

#[derive(Debug)]
pub enum ParseDecimalError {
    Empty,
    Invalid,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rounding {
    Nearest = 0,
    Down = 1,
    Up = 2,
    Zero = 3,
    TiesAway = 4,
}

impl Default for Rounding {
    fn default() -> Self {
        Rounding::Nearest
    }
}

pub struct Status(u8);

impl Status {
    #[doc(hidden)]
    pub fn from_bits(bits: u8) -> Status {
        Status(bits)
    }
}

#[derive(Clone, Copy, Default, Debug)]
pub struct Flags(u8);

impl Flags {
    //    pub fn is_invalid(&self) -> bool {
    //        (self.0 & details::BID_INVALID_EXCEPTION) != 0
    //    }
    //
    //    pub fn is_denormal(&self) -> bool {
    //        (self.0 & details::BID_DENORMAL_EXCEPTION) != 0
    //    }
    //
    //    pub fn is_zero_divide(&self) -> bool {
    //        (self.0 & details::BID_ZERO_DIVIDE_EXCEPTION) != 0
    //    }
    //
    //    pub fn is_overflow(&self) -> bool {
    //        (self.0 & details::BID_OVERFLOW_EXCEPTION) != 0
    //    }
    //
    //    pub fn is_underflow(&self) -> bool {
    //        (self.0 & details::BID_UNDERFLOW_EXCEPTION) != 0
    //    }
    //
    //    pub fn is_inexact(&self) -> bool {
    //        (self.0 & details::BID_INEXACT_EXCEPTION) != 0
    //    }
    //
    //    pub fn is_clear(&self) -> bool {
    //        self.0 == 0
    //    }
}

pub trait Context: private::Sealed {
    fn op<T, F: FnOnce(Rounding) -> (T, Flags)>(cb: F) -> T;
}

mod private {
    pub trait Sealed {}

    impl Sealed for super::DefaultContext {}
}

/// A default implementation of context which always uses `Nearest` rounding and ignores exceptions
/// set by the floating point library.
pub struct DefaultContext;

impl Context for DefaultContext {
    fn op<T, F: FnOnce(Rounding) -> (T, Flags)>(cb: F) -> T {
        let (res, _flags) = cb(Default::default());
        res
    }
}

/// A 32-bit decimal floating point type, as specified by IEEE 754-2008.
#[repr(transparent)]
pub struct Decimal32<Ctx: Context>(u32, PhantomData<*const Ctx>);
pub type d32 = Decimal32<DefaultContext>;

/// A 64-bit decimal floating point type, as specified by IEEE 754-2008.
#[repr(transparent)]
pub struct Decimal64<Ctx: Context>(u64, PhantomData<*const Ctx>);
pub type d64 = Decimal64<DefaultContext>;

/// A 128-bit decimal floating point type, as specified by IEEE 754-2008.
#[repr(transparent)]
pub struct Decimal128<Ctx: Context>(u128, PhantomData<*const Ctx>);
pub type d128 = Decimal128<DefaultContext>;

#[derive(Debug)]
struct Unpacked<T> {
    coefficient: T,
    exponent: u16,
    sign: bool,
}

#[cfg(test)]
#[allow(unused_imports)]
mod tests {

    use super::{d128, DefaultContext, FpCategory};
    #[test]
    fn it_works() {
        let x = "0.0001".parse::<d128>().unwrap();
        println!("boo {:?} {:x}", x.classify(), x.to_bits());

        let x = "0".parse::<d128>().unwrap();
        println!("{:?} {:x}", x.classify(), x.to_bits());

        // 0 => 30300000000000000000000000000000
        //0.0 => 303e0000000000000000000000000000
        //        `

        /*let x: u128 = 0x303e00000000000000000000000004d1;
        let y: u128 = 0x303e00000000000000000000000011d4;
        let z: u128 = 0x303e00000000000000000000000016a5;

        let zz = super::d128_add(x, y);
        assert_eq!(z, zz);*/
    }
}
