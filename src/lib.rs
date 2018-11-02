//! IEEE 754-2008 Decimal Floating-Point Library
//!
//! A pure Rust implementation of decimal floating point defined in
//! [IEEE 754-2008](https://en.wikipedia.org/wiki/IEEE_754-2008_revision) standard (binary
//! encoding variant).
#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]

mod consts;

use std::marker::PhantomData;
use consts::DecimalProps;
use std::fmt;
pub use std::num::FpCategory;

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

pub trait Context {
    fn op<T, F: FnOnce(Rounding) -> (T, Flags)>(cb: F) -> T;
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

macro_rules! gen_impl {
    ($name:ident, $ty:ident) => {
        impl <Ctx: $crate::Context> Clone for $name<Ctx> {
            fn clone(&self) -> Self {
                $name(self.0, PhantomData)
            }
        }

        impl <Ctx: $crate::Context> Copy for $name<Ctx> { }

        impl <Ctx: $crate::Context> fmt::Debug for $name<Ctx> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "[0x{1:00$x}]", $ty::BITS / 4, self.0)
            }
        }

        impl <Ctx: $crate::Context> $name<Ctx> {
            /// Returns `true` if this value is `NaN` and `false` otherwise.
            pub fn is_nan(self) -> bool {
                (self.0 & $ty::NAN_MASK) == $ty::NAN_MASK
            }

            /// Returns `true` if this value is positive infinity or negative infinity and `false`
            /// otherwise.
            pub fn is_infinite(self) -> bool {
                (self.0 & $ty::NAN_MASK) == $ty::INFINITY_MASK
            }

            /// Returns `true` if this number is neither infinite nor `NaN`.
            pub fn is_finite(self) -> bool {
                (self.0 & $ty::INFINITY_MASK) != $ty::INFINITY_MASK
            }

            /// Returns `true` if the number is neither zero, infinite, [subnormal][subnormal], or
            /// `NaN`.
            ///
            /// [subnormal]: https://en.wikipedia.org/wiki/Denormal_number
            pub fn is_normal(self) -> bool {
                if !self.is_finite() {
                    return false; // NaN or Infinite
                }
                let unpacked = self.unpack();
                if unpacked.coefficient == 0 {
                    return false; // Zero or illegal
                }
                Self::is_normal_internal(unpacked)
            }

            /// Returns `true` if the number is [subnormal][subnormal].
            ///
            /// [subnormal]: https://en.wikipedia.org/wiki/Denormal_number
            pub fn is_subnormal(self) -> bool {
                if !self.is_finite() {
                    return false; // NaN or Infinite
                }
                let unpacked = self.unpack();
                if unpacked.coefficient == 0 {
                    return false; // Zero or illegal
                }
                !Self::is_normal_internal(unpacked)
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
                    if unpacked.coefficient == 0 {
                        return FpCategory::Zero;
                    } else if Self::is_normal_internal(unpacked) {
                        FpCategory::Normal
                    } else {
                        FpCategory::Subnormal
                    }
                }
            }

            /// Returns `true` if and only if `self` has a positive sign, including `+0.0`, `NaN`s
            /// with positive sign bit and positive infinity.
            pub fn is_sign_positive(self) -> bool {
                !self.is_sign_negative()
            }

            /// Returns `true` if and only if `self` has a negative sign, including `-0.0`, `NaN`s
            /// with negative sign bit and negative infinity.
            pub fn is_sign_negative(self) -> bool {
                (self.0 & $ty::SIGN_MASK) != 0
            }

            /// Raw transmutation to the underlying type.
            pub fn to_bits(self) -> $ty {
                self.0
            }

            /// Raw transmutation from the underlying type.
            pub fn from_bits(bits: $ty) -> Self {
                $name(bits, PhantomData)
            }

            pub fn abs(self) -> Self {
                Self::from_bits(self.0 & !($ty::SIGN_MASK))
            }

            fn is_normal_internal(unpacked: Unpacked<$ty>) -> bool {
                if unpacked.exponent >= ($ty::COEFFICIENT_SIZE - 1) as u16 {
                    true // Normal
                } else {
                    // Check if coefficient is high enough for an exponent
                    let coeff = unpacked
                        .coefficient
                        .checked_mul($crate::consts::factors::$ty[unpacked.exponent as usize]);
                    // If overflowed, then it's guaranteed to be a "normal" number
                    coeff.map_or(true, |v| v >= ($ty::MAXIMUM_COEFFICIENT / 10))
                }
            }

            fn unpack(self) -> Unpacked<$ty> {
                debug_assert!(self.is_finite(), "can only unpack finite numbers");

                const ONE: $ty = 1 as $ty;
                const EXPONENT_MASK: $ty = (ONE << ($ty::EXPONENT_BITS + 2)) - 1;
                const LONG_COEFF_SHIFT: usize = $ty::COEFFICIENT_BITS + 3;
                const LONG_COEFF_MASK: $ty = (ONE << LONG_COEFF_SHIFT) - 1;

                const SHORT_COEFF_SHIFT: usize = $ty::COEFFICIENT_BITS + 1;
                const SHORT_COEFF_MASK: $ty = (ONE << SHORT_COEFF_SHIFT) - 1;
                const SHORT_COEFF_HIGH_BIT: $ty = ONE << LONG_COEFF_SHIFT;

                let sign = (self.0 & $ty::SIGN_MASK) != 0;
                let mut unpacked =
                    if (self.0 & $ty::SPECIAL_ENCODING_MASK) == $ty::SPECIAL_ENCODING_MASK {
                        Unpacked {
                            coefficient: (self.0 & SHORT_COEFF_MASK) | SHORT_COEFF_HIGH_BIT,
                            exponent: ((self.0 >> SHORT_COEFF_SHIFT) & EXPONENT_MASK) as u16,
                            sign,
                        }
                    } else {
                        Unpacked {
                            coefficient: self.0 & LONG_COEFF_MASK,
                            exponent: ((self.0 >> LONG_COEFF_SHIFT) & EXPONENT_MASK) as u16,
                            sign,
                        }
                    };
                // Treat illegal significants as 0
                if unpacked.coefficient >= $ty::MAXIMUM_COEFFICIENT {
                    unpacked.coefficient = 0;
                }

                unpacked
            }
        }
    };
}

gen_impl!(Decimal32, u32);
gen_impl!(Decimal64, u64);
gen_impl!(Decimal128, u128);


#[derive(Debug)]
struct Unpacked<T> {
    coefficient: T,
    exponent: u16,
    sign: bool,
}

#[cfg(test)]
mod tests {

    use super::{d128, FpCategory, DefaultContext};
    #[test]
    fn it_works() {

        let x = d128::from_bits(0x0001ed09bead87c0378d8e62ffffffff);
        assert_eq!(x.classify(), FpCategory::Normal);
        println!("HELLO {:?}", x);
//        `

        /*let x: u128 = 0x303e00000000000000000000000004d1;
        let y: u128 = 0x303e00000000000000000000000011d4;
        let z: u128 = 0x303e00000000000000000000000016a5;

        let zz = super::d128_add(x, y);
        assert_eq!(z, zz);*/
    }
}
