pub trait DecimalProps<const Factors: usize, const Digits: usize>: Copy {
    // Total size (bits)
    const BITS: usize;
    // Exponent continuation field (bits)
    const EXPONENT_BITS: usize;
    // Coefficient continuation field (bits)
    const COEFFICIENT_BITS: usize;
    // Coefficient length in decimal digits
    const COEFFICIENT_SIZE: u16;
    const MAXIMUM_COEFFICIENT: Self;
    const BIAS: isize;
    const FACTORS: [Self; Factors];

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
    const DIGITS: [i8; Digits];
}

impl DecimalProps<10, 31> for u32 {
    const BITS: usize = 32;
    const EXPONENT_BITS: usize = 6;
    const COEFFICIENT_BITS: usize = 20;
    const COEFFICIENT_SIZE: u16 = 7;
    const MAXIMUM_COEFFICIENT: u32 = 10_000_000;
    const BIAS: isize = 101;
    const FACTORS: [Self; 10] = [
        1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000,
    ];
    const DIGITS: [i8; 31] = [
        1, 1, 1, 1, -1, 2, 2, -2, 3, 3, -3, 4, 4, 4, -4, 5, 5, -5, 6, 6, -6, 7, 7, 7, -7, 8, 8, -8,
        9, 9, -9,
    ];
}

impl DecimalProps<19, 61> for u64 {
    const BITS: usize = 64;
    const EXPONENT_BITS: usize = 8;
    const COEFFICIENT_BITS: usize = 50;
    const COEFFICIENT_SIZE: u16 = 16;
    const MAXIMUM_COEFFICIENT: u64 = 10_000_000_000_000_000;
    const BIAS: isize = 398;
    const FACTORS: [Self; 19] = [
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
    const DIGITS: [i8; 61] = [
        1, 1, 1, 1, -1, 2, 2, -2, 3, 3, -3, 4, 4, 4, -4, 5, 5, -5, 6, 6, -6, 7, 7, 7, -7, 8, 8, -8,
        9, 9, -9, 10, 10, 10, -10, 11, 11, -11, 12, 12, -12, 13, 13, 13, -13, 14, 14, -14, 15, 15,
        -15, 16, 16, 16, -16, 17, 17, -17, 18, 18, -18,
    ];
}

impl DecimalProps<37, 121> for u128 {
    const BITS: usize = 128;
    const EXPONENT_BITS: usize = 12;
    const COEFFICIENT_BITS: usize = 110;
    const COEFFICIENT_SIZE: u16 = 34;
    const MAXIMUM_COEFFICIENT: u128 = 10_000_000_000_000_000_000_000_000_000_000_000;
    const BIAS: isize = 6176;
    const FACTORS: [Self; 37] = [
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
    const DIGITS: [i8; 121] = [
        1, 1, 1, 1, -1, 2, 2, -2, 3, 3, -3, 4, 4, 4, -4, 5, 5, -5, 6, 6, -6, 7, 7, 7, -7, 8, 8, -8,
        9, 9, -9, 10, 10, 10, -10, 11, 11, -11, 12, 12, -12, 13, 13, 13, -13, 14, 14, -14, 15, 15,
        -15, 16, 16, 16, -16, 17, 17, -17, 18, 18, -18, 19, 19, 19, -19, 20, 20, -20, 21, 21, -21,
        22, 22, 22, -22, 23, 23, -23, 24, 24, -24, 25, 25, 25, -25, 26, 26, -26, 27, 27, -27, 28,
        28, 28, -28, 29, 29, -29, 30, 30, -30, 31, 31, -31, 32, 32, 32, -32, 33, 33, -33, 34, 34,
        -34, 35, 35, 35, -35, 36, 36, -36,
    ];
}
