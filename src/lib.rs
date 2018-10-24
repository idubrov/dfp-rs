#![allow(dead_code)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]

pub use std::num::FpCategory;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rounding {
    Nearest = 0,
    Down = 1,
    Up = 2,
    Zero = 3,
    TiesAway = 4,
}

pub struct Status(u8);

impl Status {
    #[doc(hidden)]
    pub fn from_bits(bits: u8) -> Status {
        Status(bits)
    }
}

mod factors {
    pub const d32: [u32; 6] = [1, 10, 100, 1000, 10000, 100000];
    pub const d64: [u64; 15] = [
        1,
        10,
        100,
        1000,
        10000,
        100000,
        1000000,
        10000000,
        100000000,
        1000000000,
        10000000000,
        100000000000,
        1000000000000,
        10000000000000,
        100000000000000,
    ];
    pub const d128: [u128; 33] = [
        1,
        10,
        100,
        1000,
        10000,
        100000,
        1000000,
        10000000,
        100000000,
        1000000000,
        10000000000,
        100000000000,
        1000000000000,
        10000000000000,
        100000000000000,
        1000000000000000,
        10000000000000000,
        100000000000000000,
        1000000000000000000,
        10000000000000000000,
        100000000000000000000,
        1000000000000000000000,
        10000000000000000000000,
        100000000000000000000000,
        1000000000000000000000000,
        10000000000000000000000000,
        100000000000000000000000000,
        1000000000000000000000000000,
        10000000000000000000000000000,
        100000000000000000000000000000,
        1000000000000000000000000000000,
        10000000000000000000000000000000,
        100000000000000000000000000000000,
    ];
}

trait DecimalProps {
    // Total size (bits)
    const BITS: usize;
    // Exponent continuation field (bits)
    const EXPONENT_BITS: usize;
    // Coefficient continuation field (bits)
    const COEFFICIENT_BITS: usize;
    // Coefficient size (decimal digits)
    const COEFFICIENT_SIZE: usize;
    const MAXIMUM_COEFFICIENT: Self;

    const SIGN_MASK: Self;
    const SPECIAL_ENCODING_MASK: Self;
    const INFINITY_MASK: Self;
    const NAN_MASK: Self;
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct decimal<T>(T);

macro_rules! gen_impl {
    ($name:ident, $ty:ident) => {
        pub type $name = decimal<$ty>;

        impl decimal<$ty> {
            pub fn is_nan(self) -> bool {
                (self.0 & $ty::NAN_MASK) == $ty::NAN_MASK
            }

            pub fn is_infinite(self) -> bool {
                (self.0 & $ty::NAN_MASK) == $ty::INFINITY_MASK
            }

            pub fn is_finite(self) -> bool {
                (self.0 & $ty::INFINITY_MASK) != $ty::INFINITY_MASK
            }

            pub fn is_normal(self) -> bool {
                if !self.is_finite() {
                    return false; // NaN or Infinite
                }
                let unpacked = self.unpack();
                if unpacked.coefficient == 0 {
                    return false; // Zero or illegal
                }
                $name::is_normal_internal(unpacked)
            }

            pub fn is_subnormal(self) -> bool {
                if !self.is_finite() {
                    return false; // NaN or Infinite
                }
                let unpacked = self.unpack();
                if unpacked.coefficient == 0 {
                    return false; // Zero or illegal
                }
                !$name::is_normal_internal(unpacked)
            }

            fn is_normal_internal(unpacked: Unpacked<$ty>) -> bool {
                if unpacked.exponent >= ($ty::COEFFICIENT_SIZE - 1) as u16 {
                    true // Normal
                } else {
                    // Check if coefficient is high enough for an exponent
                    let coeff = unpacked
                        .coefficient
                        .checked_mul(::factors::$name[unpacked.exponent as usize]);
                    // If overflowed, then it's guaranteed to be a "normal" number
                    coeff.map_or(true, |v| v >= ($ty::MAXIMUM_COEFFICIENT / 10))
                }
            }

            pub fn classify(self) -> FpCategory {
                if self.is_nan() {
                    FpCategory::Nan
                } else if self.is_infinite() {
                    FpCategory::Infinite
                } else {
                    let unpacked = self.unpack();
                    if unpacked.coefficient == 0 {
                        return FpCategory::Zero;
                    } else if $name::is_normal_internal(unpacked) {
                        FpCategory::Normal
                    } else {
                        FpCategory::Subnormal
                    }
                }
            }

            pub fn is_sign_positive(self) -> bool {
                !self.is_sign_negative()
            }

            pub fn is_sign_negative(self) -> bool {
                (self.0 & $ty::SIGN_MASK) != 0
            }

            /// Raw transmutation to the underlying type.
            pub fn to_bits(self) -> $ty {
                self.0
            }

            /// Raw transmutation from the underlying type.
            pub fn from_bits(bits: $ty) -> Self {
                decimal(bits)
            }

            pub fn unpack(self) -> Unpacked<$ty> {
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

gen_impl!(d32, u32);
gen_impl!(d64, u64);
gen_impl!(d128, u128);

//
//trait FpDecimal: Clone + Copy {
//    type Bits;
//
//    fn is_nan(self) -> bool;
//    fn is_infinite(self) -> bool;
//    fn is_finite(self) -> bool;
//    fn is_normal(self) -> bool;
//    fn classify(self) -> FpCategory;
//    fn is_sign_positive(self) -> bool;
//    fn is_sign_negative(self) -> bool;
//    fn to_bits(self) -> Self::Bits;
//    fn from_bits(bits: Self::Bits) -> Self;
//}

// Internal constants

impl DecimalProps for u32 {
    const BITS: usize = 32;
    const EXPONENT_BITS: usize = 6;
    const COEFFICIENT_BITS: usize = 20;
    const COEFFICIENT_SIZE: usize = 7;
    const MAXIMUM_COEFFICIENT: u32 = 10_000_000;

    const SIGN_MASK: u32 = 0b10000000u32 << (Self::BITS - 8);
    const SPECIAL_ENCODING_MASK: u32 = 0b01100000u32 << (Self::BITS - 8);
    const INFINITY_MASK: Self = 0b01111000 << (Self::BITS - 8);
    const NAN_MASK: Self = 0b01111100 << (Self::BITS - 8);
}

impl DecimalProps for u64 {
    const BITS: usize = 64;
    const EXPONENT_BITS: usize = 8;
    const COEFFICIENT_BITS: usize = 50;
    const COEFFICIENT_SIZE: usize = 16;
    const MAXIMUM_COEFFICIENT: u64 = 10_000_000_000_000_000;

    const SIGN_MASK: u64 = 0b10000000u64 << (Self::BITS - 8);
    const SPECIAL_ENCODING_MASK: u64 = 0b01100000u64 << (Self::BITS - 8);
    const INFINITY_MASK: Self = 0b01111000 << (Self::BITS - 8);
    const NAN_MASK: Self = 0b01111100 << (Self::BITS - 8);
}

impl DecimalProps for u128 {
    const BITS: usize = 128;
    const EXPONENT_BITS: usize = 12;
    const COEFFICIENT_SIZE: usize = 34;
    const COEFFICIENT_BITS: usize = 110;
    const MAXIMUM_COEFFICIENT: u128 = 10_000_000_000_000_000_000_000_000_000_000_000;

    const SIGN_MASK: u128 = 0b10000000u128 << (Self::BITS - 8);
    const SPECIAL_ENCODING_MASK: u128 = 0b01100000u128 << (Self::BITS - 8);
    const INFINITY_MASK: Self = 0b01111000 << (Self::BITS - 8);
    const NAN_MASK: Self = 0b01111100 << (Self::BITS - 8);
}

#[derive(Debug)]
pub struct Unpacked<T> {
    coefficient: T,
    exponent: u16,
    sign: bool,
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        use super::decimal;
        let x: decimal<u32> = decimal(0x3292d688);
        println!("{:?}", x.unpack());

        let x: decimal<u32> = decimal(0x320004d1);
        println!("{:?}", x.unpack());

        let x: decimal<u32> = decimal(0x6cb8967f);
        println!("{:?}", x.unpack());

        /*let x: u128 = 0x303e00000000000000000000000004d1;
        let y: u128 = 0x303e00000000000000000000000011d4;
        let z: u128 = 0x303e00000000000000000000000016a5;

        let zz = super::d128_add(x, y);
        assert_eq!(z, zz);*/
    }
}
