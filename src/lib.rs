//! IEEE 754-2008 Decimal Floating-Point Library
//!
//! A pure Rust implementation of decimal floating point defined in
//! [IEEE 754-2008](https://en.wikipedia.org/wiki/IEEE_754-2008_revision) standard (binary
//! encoding variant).
#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]

mod raw;
#[cfg(test)]
mod tests;
mod traits;
mod u256_impl;
mod wide_ops;

use crate::traits::DecimalStorage;
use crate::u256_impl::u256;
use std::fmt::LowerHex;
use std::marker::PhantomData;
pub use std::num::FpCategory;
use std::ops::{Add, Mul, Sub};
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseDecimalError {
    kind: DecimalErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecimalErrorKind {
    Empty,
    Invalid,
}

impl ParseDecimalError {
    pub(crate) fn empty() -> ParseDecimalError {
        ParseDecimalError {
            kind: DecimalErrorKind::Empty,
        }
    }

    pub(crate) fn invalid() -> ParseDecimalError {
        ParseDecimalError {
            kind: DecimalErrorKind::Invalid,
        }
    }
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
    };
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

/// A template for a decimal floating point type, as specified by IEEE 754-2008.
#[repr(transparent)]
pub struct Decimal<T, Ctx: Context>(T, PhantomData<*const Ctx>);

/// A 32-bit decimal floating point type, as specified by IEEE 754-2008.
pub type d32 = Decimal<u32, NearestRoundingContext>;

/// A 64-bit decimal floating point type, as specified by IEEE 754-2008.
pub type d64 = Decimal<u64, NearestRoundingContext>;

/// A 128-bit decimal floating point type, as specified by IEEE 754-2008.
pub type d128 = Decimal<u128, NearestRoundingContext>;

impl<T, Ctx: crate::Context> Clone for Decimal<T, Ctx>
where
    T: Copy,
{
    fn clone(&self) -> Self {
        Decimal(self.0, PhantomData)
    }
}

impl<Ctx: crate::Context> Copy for Decimal<u32, Ctx> {}

impl<T, Ctx: crate::Context> std::fmt::Debug for Decimal<T, Ctx>
where
    T: LowerHex,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[0x{1:00$x}]", std::mem::size_of::<T>() * 2, self.0)
    }
}

impl<T: DecimalStorage, Ctx: Context> Decimal<T, Ctx> {
    /// Positive `NaN` constant (not a number)
    pub const NAN: Self = Decimal(T::NAN_MASK, PhantomData);

    /// Positive infinity constant
    pub const INFINITY: Self = Decimal(T::INFINITY_MASK, PhantomData);

    /// Negative infinity constant
    pub const NEG_INFINITY: Self = Decimal(T::NEG_INFINITY_MASK, PhantomData);

    /// Returns `true` if this value is `NaN` or `sNaN` and `false` otherwise.
    pub fn is_nan(&self) -> bool {
        (self.0 & T::NAN_MASK) == T::NAN_MASK
    }

    /// Returns `true` if this value is `sNaN` and `false` otherwise.
    pub fn is_snan(&self) -> bool {
        self.is_nan() && (self.0 & T::SIGNALING_NAN_MASK) == T::SIGNALING_NAN_MASK
    }

    /// Returns `true` if this value is positive infinity or negative infinity and `false`
    /// otherwise.
    pub fn is_infinite(&self) -> bool {
        (self.0 & T::NAN_MASK) == T::INFINITY_MASK
    }

    /// Returns `true` if this number is neither infinite nor `NaN`.
    pub fn is_finite(&self) -> bool {
        (self.0 & T::INFINITY_MASK) != T::INFINITY_MASK
    }

    /// Returns `true` if the number is neither zero, infinite, [subnormal][subnormal], or
    /// `NaN`.
    ///
    /// [subnormal]: https://en.wikipedia.org/wiki/Denormal_number
    pub fn is_normal(&self) -> bool {
        if !self.is_finite() {
            return false; // NaN or Infinite
        }
        let unpacked = self.unpack();
        if unpacked.coefficient == T::zero() {
            return false; // Zero or illegal
        }
        unpacked.is_normal_internal()
    }

    /// Returns `true` if the number is [subnormal][subnormal].
    ///
    /// [subnormal]: https://en.wikipedia.org/wiki/Denormal_number
    pub fn is_subnormal(&self) -> bool {
        if !self.is_finite() {
            return false; // NaN or Infinite
        }
        let unpacked = self.unpack();
        if unpacked.coefficient == T::zero() {
            return false; // Zero or illegal
        }
        !unpacked.is_normal_internal()
    }

    /// Returns the floating point category of the number. If only one property is going to
    /// be tested, it is generally faster to use the specific predicate instead.
    pub fn classify(self) -> FpCategory {
        if self.is_nan() {
            FpCategory::Nan
        } else if self.is_infinite() {
            FpCategory::Infinite
        } else {
            let unpacked = self.unpack();
            if unpacked.coefficient == T::zero() {
                FpCategory::Zero
            } else if unpacked.is_normal_internal() {
                FpCategory::Normal
            } else {
                FpCategory::Subnormal
            }
        }
    }

    /// Returns `true` if and only if `self` has a positive sign, including `+0.0`, `NaN`s
    /// with positive sign bit and positive infinity.
    pub fn is_sign_positive(&self) -> bool {
        !self.is_sign_negative()
    }

    /// Returns `true` if and only if `self` has a negative sign, including `-0.0`, `NaN`s
    /// with negative sign bit and negative infinity.
    pub fn is_sign_negative(&self) -> bool {
        (self.0 & T::SIGN_MASK) != T::zero()
    }

    /// Raw transmutation to the underlying type.
    pub fn to_bits(&self) -> T {
        self.0
    }

    /// Raw transmutation from the underlying type.
    pub fn from_bits(bits: T) -> Self {
        Decimal(bits, PhantomData)
    }

    /// Absolute value of the decimal (removes the sign).
    pub fn abs(self) -> Self {
        Self::from_bits(self.0 & !T::SIGN_MASK)
    }

    pub(crate) fn unpack(&self) -> raw::Unpacked<T> {
        raw::Unpacked::new(self.0)
    }

    /// Converts a string in base 10 to a float.
    /// Accepts an optional decimal exponent.
    ///
    /// This function accepts strings such as
    ///
    /// * '3.14'
    /// * '-3.14'
    /// * '2.5E10', or equivalently, '2.5e10'
    /// * '2.5E-10'
    /// * '5.'
    /// * '.5', or, equivalently,  '0.5'
    /// * 'inf', '-inf', 'NaN'
    ///
    /// Leading and trailing whitespace represent an error.
    ///
    /// # Arguments
    ///
    /// * src - A string
    /// * rounding - An explicit rounding mode to use
    ///
    /// # Return value
    ///
    /// `Err(ParseDecimalError)` if the string did not represent a valid
    /// number.  Otherwise, `Ok(n)` where `n` is the floating-point decimal
    /// number represented by `src`.
    pub fn parse_rounding(s: &str, rounding: Rounding) -> Result<Self, ParseDecimalError> {
        raw::parse_rounding(s, rounding).map(Self::from_bits)
    }
}

impl<T: DecimalStorage, Ctx: crate::Context> FromStr for Decimal<T, Ctx> {
    type Err = ParseDecimalError;

    fn from_str(s: &str) -> Result<Self, ParseDecimalError> {
        Self::parse_rounding(s, Ctx::rounding())
    }
}

impl<T: DecimalStorage, Ctx: crate::Context> Add for Decimal<T, Ctx> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::from_bits(raw::add(self.0, rhs.0, Ctx::rounding()))
    }
}

impl<T: DecimalStorage, Ctx: crate::Context> Sub for Decimal<T, Ctx> {
    type Output = Self;

    fn sub(self, mut rhs: Self) -> Self::Output {
        if !rhs.is_nan() {
            rhs.0 ^= T::SIGN_MASK;
        }
        Self::from_bits(raw::add(self.0, rhs.0, Ctx::rounding()))
    }
}

impl<T: DecimalStorage, Ctx: crate::Context> Mul for Decimal<T, Ctx> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::from_bits(raw::mul(self.0, rhs.0, Ctx::rounding()))
    }
}
