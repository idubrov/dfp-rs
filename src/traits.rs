use crate::wide_ops::WideOps;
use num_traits::{
    FromPrimitive, NumAssignOps, One, PrimInt, ToPrimitive, WrappingAdd, WrappingSub, Zero,
};
use std::ops::{BitAnd, BitAndAssign, BitOrAssign, BitXorAssign, Div, Rem, Shr};

pub trait DecimalFactors: Sized + 'static {
    const FACTORS: &'static [Self];
}

/// Operations we need for backing numbers and their "wide" variants. For example, for 128-bit
/// decimal, this trait needs to be implemented both for backing `u128` number and also for the
/// "wide" `u256` (used in cases we need to run operation against wider coefficients, like in case
/// of multiplications / divisions).
pub trait BasicInt:
    DecimalFactors
    + PartialOrd
    + PartialEq
    + Ord
    + Eq
    + BitAnd<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
    + Shr<usize, Output = Self>
    + Zero
    + One
    + Clone
    + Copy
{
    const TEN: Self;
    fn leading_zeros(self) -> u32;
}

pub trait DecimalConsts: Copy + 'static {
    // Total size (bits)
    const BITS: u32;
    // Exponent continuation field (bits)
    const EXPONENT_BITS: usize;
    // Coefficient continuation field (bits)
    const COEFFICIENT_BITS: usize;
    // Maximum decimal digits in the coefficient
    const MAXIMUM_DIGITS: u16;
    const MAXIMUM_COEFFICIENT: Self;
    const BIAS: u16;
}

impl DecimalConsts for u32 {
    const BITS: u32 = 32;
    const EXPONENT_BITS: usize = 6;
    const COEFFICIENT_BITS: usize = 20;
    const MAXIMUM_DIGITS: u16 = 7;
    const MAXIMUM_COEFFICIENT: u32 = 10_000_000;
    const BIAS: u16 = 101;
}

impl DecimalFactors for u32 {
    const FACTORS: &'static [Self] = &[
        1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000,
    ];
}

impl DecimalConsts for u64 {
    const BITS: u32 = 64;
    const EXPONENT_BITS: usize = 8;
    const COEFFICIENT_BITS: usize = 50;
    const MAXIMUM_DIGITS: u16 = 16;
    const MAXIMUM_COEFFICIENT: u64 = 10_000_000_000_000_000;
    const BIAS: u16 = 398;
}

impl DecimalFactors for u64 {
    const FACTORS: &'static [Self] = &[
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
    ];
}

impl DecimalConsts for u128 {
    const BITS: u32 = 128;
    const EXPONENT_BITS: usize = 12;
    const COEFFICIENT_BITS: usize = 110;
    const MAXIMUM_DIGITS: u16 = 34;
    const MAXIMUM_COEFFICIENT: u128 = 10_000_000_000_000_000_000_000_000_000_000_000;
    const BIAS: u16 = 6176;
}

impl DecimalFactors for u128 {
    const FACTORS: &'static [Self] = &[
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
        1000000000000000000000000000000000,
        10000000000000000000000000000000000,
        100000000000000000000000000000000000,
        1000000000000000000000000000000000000,
        10000000000000000000000000000000000000,
        100000000000000000000000000000000000000,
    ];
}

/// Trait for type that could be used as a decimal backing storage (which in our implementation are
/// `u32`, `u64` and `u128`). Provides some derived constants used in the implementation.
pub trait DecimalStorage:
    'static
    + Sized
    + DecimalConsts
    + DecimalFactors
    + FromPrimitive
    + ToPrimitive
    + PrimInt
    + BasicInt
    + NumAssignOps
    + BitOrAssign
    + BitAndAssign
    + BitXorAssign
    + WrappingAdd
    + WrappingSub
    + WideOps
    + std::fmt::Display
    + std::fmt::Debug
{
    const SIGN_MASK: Self;

    /// Mask for "special encoding" (two bits after the sign bit). If the 2 bits after the sign bit
    /// are `11`, then we use a "short" coefficient representation with implicit `100` prefix.
    const SPECIAL_ENC_MASK: Self;
    const INFINITY_MASK: Self;
    const NEG_INFINITY_MASK: Self;
    const NAN_MASK: Self;
    const SIGNALING_NAN_MASK: Self;
    /// Add 2 -- two bits in front of the exponent bits are also part of the exponent, as long as they
    /// are not `11`.
    const EXPONENT_MASK: Self;
    const EXPONENT_MAX: u16;

    // If the most significant 4 bits of the significand are between 0 and 7, the encoded value
    // begins as follows:
    // s eemmm xxx   Coefficient begins with 0mmm
    const LONG_COEFF_SHIFT: usize;
    const LONG_COEFF_MASK: Self;

    // If the leading 4 bits of the significand are binary 1000 or 1001 (decimal 8 or 9), the
    // number begins as follows:
    // s 11eem xxx Coefficient begins with 100m
    const SHORT_COEFF_SHIFT: usize;
    const SHORT_COEFF_MASK: Self;
    const SHORT_COEFF_HIGH_BIT: Self;
}

macro_rules! declare_consts {
    ($name:ident) => {
        impl DecimalStorage for $name {
            const SIGN_MASK: Self = 0b1000_0000 << (Self::BITS - 8);

            /// Mask for "special encoding" (two bits after the sign bit). If the 2 bits after the sign bit
            /// are `11`, then we use a "short" coefficient representation with implicit `100` prefix.
            const SPECIAL_ENC_MASK: Self = 0b0110_0000 << (Self::BITS - 8);
            const INFINITY_MASK: Self = 0b0111_1000 << (Self::BITS - 8);
            const NEG_INFINITY_MASK: Self = Self::INFINITY_MASK | Self::SIGN_MASK;
            const NAN_MASK: Self = 0b0111_1100 << (Self::BITS - 8);
            const SIGNALING_NAN_MASK: Self = 0b0000_0010 << (Self::BITS - 8);
            /// Add 2 -- two bits in front of the exponent bits are also part of the exponent, as long as they
            /// are not `11`.
            const EXPONENT_MASK: Self = (1 << (Self::EXPONENT_BITS + 2)) - 1;
            // FIXME: make u16?
            const EXPONENT_MAX: u16 = (0b11 << Self::EXPONENT_BITS) - 1;

            // If the most significant 4 bits of the significand are between 0 and 7, the encoded value
            // begins as follows:
            // s eemmm xxx   Coefficient begins with 0mmm
            const LONG_COEFF_SHIFT: usize = Self::COEFFICIENT_BITS + 3;
            const LONG_COEFF_MASK: Self = (1 << Self::LONG_COEFF_SHIFT) - 1;

            // If the leading 4 bits of the significand are binary 1000 or 1001 (decimal 8 or 9), the
            // number begins as follows:
            // s 11eem xxx Coefficient begins with 100m
            const SHORT_COEFF_SHIFT: usize = Self::COEFFICIENT_BITS + 1;
            const SHORT_COEFF_MASK: Self = (1 << Self::SHORT_COEFF_SHIFT) - 1;
            const SHORT_COEFF_HIGH_BIT: Self = 1 << Self::LONG_COEFF_SHIFT;
        }

        impl BasicInt for $name {
            const TEN: $name = 10;
            fn leading_zeros(self) -> u32 {
                PrimInt::leading_zeros(self)
            }
        }
    };
}

declare_consts!(u32);
declare_consts!(u64);
declare_consts!(u128);
