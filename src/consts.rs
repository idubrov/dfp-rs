pub trait DecimalProps {
    // Total size (bits)
    const BITS: usize;
    // Exponent continuation field (bits)
    const EXPONENT_BITS: usize;
    // Coefficient continuation field (bits)
    const COEFFICIENT_BITS: usize;
    // Coefficient size (decimal digits)
    const COEFFICIENT_SIZE: usize;
    const MAXIMUM_COEFFICIENT: Self;
    const BIAS: Self;

    const SIGN_MASK: Self;
    const SPECIAL_ENCODING_MASK: Self;
    const INFINITY_MASK: Self;
    const NAN_MASK: Self;
}

impl DecimalProps for u32 {
    const BITS: usize = 32;
    const EXPONENT_BITS: usize = 6;
    const COEFFICIENT_BITS: usize = 20;
    const COEFFICIENT_SIZE: usize = 7;
    const MAXIMUM_COEFFICIENT: u32 = 10_000_000;
    const BIAS: u32 = 101;

    const SIGN_MASK: u32 = 0b10000000u32 << (Self::BITS - 8);
    const SPECIAL_ENCODING_MASK: u32 = 0b01100000u32 << (Self::BITS - 8);
    const INFINITY_MASK: Self = 0b01111000u32 << (Self::BITS - 8);
    const NAN_MASK: Self = 0b01111100u32 << (Self::BITS - 8);
}

impl DecimalProps for u64 {
    const BITS: usize = 64;
    const EXPONENT_BITS: usize = 8;
    const COEFFICIENT_BITS: usize = 50;
    const COEFFICIENT_SIZE: usize = 16;
    const MAXIMUM_COEFFICIENT: u64 = 10_000_000_000_000_000;
    const BIAS: u64 = 398;

    const SIGN_MASK: u64 = 0b10000000u64 << (Self::BITS - 8);
    const SPECIAL_ENCODING_MASK: u64 = 0b01100000u64 << (Self::BITS - 8);
    const INFINITY_MASK: Self = 0b01111000u64 << (Self::BITS - 8);
    const NAN_MASK: Self = 0b01111100u64 << (Self::BITS - 8);
}

impl DecimalProps for u128 {
    const BITS: usize = 128;
    const EXPONENT_BITS: usize = 12;
    const COEFFICIENT_BITS: usize = 110;
    const COEFFICIENT_SIZE: usize = 34;
    const MAXIMUM_COEFFICIENT: u128 = 10_000_000_000_000_000_000_000_000_000_000_000;
    const BIAS: u128 = 6176;

    const SIGN_MASK: u128 = 0b10000000u128 << (Self::BITS - 8);
    const SPECIAL_ENCODING_MASK: u128 = 0b01100000u128 << (Self::BITS - 8);
    const INFINITY_MASK: Self = 0b01111000u128 << (Self::BITS - 8);
    const NAN_MASK: Self = 0b01111100u128 << (Self::BITS - 8);
}

pub mod factors {
    pub const u32: [u32; 6] = [1, 10, 100, 1000, 10000, 100000];
    pub const u64: [u64; 15] = [
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
    pub const u128: [u128; 33] = [
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
