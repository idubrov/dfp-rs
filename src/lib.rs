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
    /// Round to nearest, with ties rounding to the nearest even digit.
    Nearest,
    /// Round down (toward negative infinity; negative results thus round away from zero)
    Down,
    /// Round up (toward positive infinity; negative results thus round toward zero)
    Up,
    /// Round toward zero (truncation; it is similar to the common behavior of float-to-integer
    /// conversions, which convert −3.9 to −3 and 3.9 to 3)
    Zero,
    /// Round to nearest, where ties round away from zero
    TiesAway,
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
    fn op<T>(cb: impl FnOnce(Rounding) -> (T, Flags)) -> T {
        let (res, _flags) = cb(Self::rounding());
        res
    }
    fn rounding() -> Rounding;
}

mod private {
    pub trait Sealed {}
}

macro_rules! declare_context {
    ($name:ident, $rounding:ident, $doc:expr) => {
        #[doc = $doc]
        pub struct $name;

        impl Context for $name {
            fn rounding() -> Rounding {
                Rounding::$rounding
            }
        }

        impl private::Sealed for $name {}
    }
}

declare_context!(
    NearestRoundingContext,
    Nearest,
    "An implementation of context which always uses `Nearest` rounding and ignores exceptions"
);
declare_context!(
    DownRoundingContext,
    Down,
    "An implementation of context which always uses `Down` rounding and ignores exceptions"
);
declare_context!(
    UpRoundingContext,
    Up,
    "An implementation of context which always uses `Up` rounding and ignores exceptions"
);
declare_context!(
    ZeroRoundingContext,
    Zero,
    "An implementation of context which always uses `Zero` rounding and ignores exceptions"
);
declare_context!(
    TiesAwayRoundingContext,
    TiesAway,
    "An implementation of context which always uses `TiesAway` rounding and ignores exceptions"
);

/// A 32-bit decimal floating point type, as specified by IEEE 754-2008.
#[repr(transparent)]
pub struct Decimal32<Ctx: Context>(u32, PhantomData<*const Ctx>);
pub type d32 = Decimal32<NearestRoundingContext>;

/// A 64-bit decimal floating point type, as specified by IEEE 754-2008.
#[repr(transparent)]
pub struct Decimal64<Ctx: Context>(u64, PhantomData<*const Ctx>);
pub type d64 = Decimal64<NearestRoundingContext>;

/// A 128-bit decimal floating point type, as specified by IEEE 754-2008.
#[repr(transparent)]
pub struct Decimal128<Ctx: Context>(u128, PhantomData<*const Ctx>);
pub type d128 = Decimal128<NearestRoundingContext>;

#[derive(Debug)]
struct Unpacked<T> {
    coefficient: T,
    exponent: u16,
    sign: bool,
}

#[cfg(test)]
#[allow(unused_imports)]
mod tests {
    use super::FpCategory;
    #[test]
    fn it_works() {
        type d32 = crate::Decimal32<crate::DownRoundingContext>;
        //let x = "-99999999".parse::<d32>().unwrap();
        //println!("boo {:?} {:x}", x.classify(), x.to_bits());
        // 0 => 30300000000000000000000000000000
        //0.0 => 303e0000000000000000000000000000
        //        `

        type d128 = crate::Decimal128<crate::NearestRoundingContext>;
        let expected = d128::from_bits(0x3000314dc6448d9338c15b0a00000000);
        let unpacked: crate::Unpacked<_> = expected.into();
        eprintln!("{:?}", unpacked);
        let actual = "9.9999999999999999999999999999999995".parse::<d128>().unwrap();
        //3000314dc6448d9338c15b0a00000000

        //bid128_from_string 2 9.9999999999999999999999999999999995 [3000314dc6448d9338c15b0a00000000] 20
        /*let x: u128 = 0x303e00000000000000000000000004d1;
        let y: u128 = 0x303e00000000000000000000000011d4;
        let z: u128 = 0x303e00000000000000000000000016a5;

        let zz = super::d128_add(x, y);
        assert_eq!(z, zz);*/
    }
}
