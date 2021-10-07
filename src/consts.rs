use num_traits::{FromPrimitive, NumAssignOps, PrimInt, ToPrimitive, WrappingAdd, WrappingSub};
use std::ops::{BitAndAssign, BitOrAssign};

pub trait DecimalConsts: Copy + 'static {
    // Total size (bits)
    const BITS: u32;
    // Exponent continuation field (bits)
    const EXPONENT_BITS: usize;
    // Coefficient continuation field (bits)
    const COEFFICIENT_BITS: usize;
    // Coefficient length in decimal digits
    const COEFFICIENT_SIZE: u16;
    const TEN: Self;
    const MAXIMUM_COEFFICIENT: Self;
    // FIXME: u16
    const BIAS: isize;
    const FACTORS: &'static [Self];

    // Code used to generate constants. Note that need each smaller number has array that is prefix
    // of larger number, but with nuance that last elements are always positive (since we can never
    // have 8 digits for d32, for example).
    //
    // #[test]
    // fn generate() {
    //     type T = u32;
    //     println!("    1,");
    //     let mut min: T = 1;
    //     let limit = T::MAXIMUM_COEFFICIENT * 100;
    //     while min <= limit {
    //         let max = 2 * min - 1;
    //         let digits = min.to_string().len();
    //         if max >= T::pow(10, digits as u32) {
    //             println!("    {},", -(digits as isize));
    //         } else {
    //             println!("    {},", digits);
    //         };
    //         min *= 2;
    //     }
    // }

    /// Each array is a lookup table to determine how many decimal digits do we need to represent
    /// coefficient with the given amount of binary digits. If value in the array is negative, it
    /// indicates that we might need `digits` or we might need `digits + 1` digits. If number is less
    /// than `factors[digits]`, then we need `digits`, otherwise we need `digits + 1`. For example, if
    /// we have 4 bits, we could have `0x1001` (which is `9`) or we could have `0x1010`, which is `10`.
    /// For this case, entry (entry under index `[4]`) will be `-1`.
    ///
    /// Note that we have table to up to 100x of the maximum coefficient -- we use increased
    /// precision during some intermediate computations on unpacked values.
    const DIGITS: &'static [i8];
}

impl DecimalConsts for u32 {
    const BITS: u32 = 32;
    const EXPONENT_BITS: usize = 6;
    const COEFFICIENT_BITS: usize = 20;
    const COEFFICIENT_SIZE: u16 = 7;
    const TEN: u32 = 10;
    const MAXIMUM_COEFFICIENT: u32 = 10_000_000;
    const BIAS: isize = 101;
    const FACTORS: &'static [Self] = &[
        1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000,
    ];
    const DIGITS: &'static [i8] = &[
        1, 1, 1, 1, -1, 2, 2, -2, 3, 3, -3, 4, 4, 4, -4, 5, 5, -5, 6, 6, -6, 7, 7, 7, -7, 8, 8, -8,
        9, 9, -9,
    ];
}

impl DecimalConsts for u64 {
    const BITS: u32 = 64;
    const EXPONENT_BITS: usize = 8;
    const COEFFICIENT_BITS: usize = 50;
    const COEFFICIENT_SIZE: u16 = 16;
    const TEN: u64 = 10;
    const MAXIMUM_COEFFICIENT: u64 = 10_000_000_000_000_000;
    const BIAS: isize = 398;
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
    ];
    const DIGITS: &'static [i8] = &[
        1, 1, 1, 1, -1, 2, 2, -2, 3, 3, -3, 4, 4, 4, -4, 5, 5, -5, 6, 6, -6, 7, 7, 7, -7, 8, 8, -8,
        9, 9, -9, 10, 10, 10, -10, 11, 11, -11, 12, 12, -12, 13, 13, 13, -13, 14, 14, -14, 15, 15,
        -15, 16, 16, 16, -16, 17, 17, -17, 18, 18, -18,
    ];
}

impl DecimalConsts for u128 {
    const BITS: u32 = 128;
    const EXPONENT_BITS: usize = 12;
    const COEFFICIENT_BITS: usize = 110;
    const COEFFICIENT_SIZE: u16 = 34;
    const TEN: u128 = 10;
    const MAXIMUM_COEFFICIENT: u128 = 10_000_000_000_000_000_000_000_000_000_000_000;
    const BIAS: isize = 6176;
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
    ];
    const DIGITS: &'static [i8] = &[
        1, 1, 1, 1, -1, 2, 2, -2, 3, 3, -3, 4, 4, 4, -4, 5, 5, -5, 6, 6, -6, 7, 7, 7, -7, 8, 8, -8,
        9, 9, -9, 10, 10, 10, -10, 11, 11, -11, 12, 12, -12, 13, 13, 13, -13, 14, 14, -14, 15, 15,
        -15, 16, 16, 16, -16, 17, 17, -17, 18, 18, -18, 19, 19, 19, -19, 20, 20, -20, 21, 21, -21,
        22, 22, 22, -22, 23, 23, -23, 24, 24, -24, 25, 25, 25, -25, 26, 26, -26, 27, 27, -27, 28,
        28, 28, -28, 29, 29, -29, 30, 30, -30, 31, 31, -31, 32, 32, 32, -32, 33, 33, -33, 34, 34,
        -34, 35, 35, 35, -35, 36, 36, -36,
    ];
}

/// Trait for type that could be used as a decimal backing storage (which in our implementation are
/// `u32`, `u64` and `u128`). Provides some derived constants used in the implementation.
pub trait DecimalStorage:
    'static
    + Sized
    + DecimalConsts
    + FromPrimitive
    + ToPrimitive
    + PrimInt
    + NumAssignOps
    + BitOrAssign
    + BitAndAssign
    + WrappingAdd
    + WrappingSub
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
    // FIXME: make u16?
    const EXPONENT_MAX: isize;

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
            const EXPONENT_MAX: isize = (0b11 << Self::EXPONENT_BITS) - 1;

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
    };
}

declare_consts!(u32);
declare_consts!(u64);
declare_consts!(u128);
