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
}

impl DecimalProps for u32 {
    const BITS: usize = 32;
    const EXPONENT_BITS: usize = 6;
    const COEFFICIENT_BITS: usize = 20;
    const COEFFICIENT_SIZE: usize = 7;
    const MAXIMUM_COEFFICIENT: u32 = 10_000_000;
    const BIAS: u32 = 101;
}

impl DecimalProps for u64 {
    const BITS: usize = 64;
    const EXPONENT_BITS: usize = 8;
    const COEFFICIENT_BITS: usize = 50;
    const COEFFICIENT_SIZE: usize = 16;
    const MAXIMUM_COEFFICIENT: u64 = 10_000_000_000_000_000;
    const BIAS: u64 = 398;
}

impl DecimalProps for u128 {
    const BITS: usize = 128;
    const EXPONENT_BITS: usize = 12;
    const COEFFICIENT_BITS: usize = 110;
    const COEFFICIENT_SIZE: usize = 34;
    const MAXIMUM_COEFFICIENT: u128 = 10_000_000_000_000_000_000_000_000_000_000_000;
    const BIAS: u128 = 6176;
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
