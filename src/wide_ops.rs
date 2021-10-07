use crate::traits::BasicInt;
use crate::u256;

/// "Wide" multiplication and division.
pub trait WideOps: Sized {
    type Wide: BasicInt;
    fn wide_mul(self, rhs: Self) -> Self::Wide;
    fn wide_div_rem(value: Self::Wide, divisor: Self) -> (Self, Self);
    fn split(value: Self::Wide) -> (Self, Self);
}

impl WideOps for u32 {
    type Wide = u64;

    fn wide_mul(self, rhs: u32) -> u64 {
        u64::from(self) * u64::from(rhs)
    }
    fn wide_div_rem(value: u64, divisor: u32) -> (u32, u32) {
        let quotient = value / u64::from(divisor);
        debug_assert!(quotient <= u64::from(u32::MAX));
        let remainder = (value % u64::from(divisor)) as u32;
        (quotient as u32, remainder)
    }

    fn split(value: u64) -> (u32, u32) {
        ((value >> 32) as u32, value as u32)
    }
}

impl WideOps for u64 {
    type Wide = u128;

    fn wide_mul(self, rhs: u64) -> u128 {
        u128::from(self) * u128::from(rhs)
    }

    fn wide_div_rem(value: u128, divisor: u64) -> (u64, u64) {
        let quotient = value / u128::from(divisor);
        debug_assert!(quotient <= u128::from(u64::MAX));
        let remainder = (value % u128::from(divisor)) as u64;
        (quotient as u64, remainder)
    }

    fn split(value: u128) -> (u64, u64) {
        ((value >> 64) as u64, value as u64)
    }
}

impl WideOps for u128 {
    type Wide = u256;

    fn wide_mul(self, rhs: u128) -> u256 {
        u256::from(self) * u256::from(rhs)
    }

    fn wide_div_rem(value: u256, divisor: u128) -> (u128, u128) {
        let quotient = value / u256::from(divisor);
        debug_assert!(quotient <= u256::from(u128::MAX));
        let remainder = (value % u256::from(divisor)).as_u128();
        (quotient.as_u128(), remainder)
    }

    fn split(value: u256) -> (u128, u128) {
        let lo = u128::from(value.0[1]) << 64 | u128::from(value.0[0]);
        let hi = u128::from(value.0[3]) << 64 | u128::from(value.0[2]);
        (hi, lo)
    }
}

trait Split {
    fn hi(self) -> u128;
    fn lo(self) -> u128;
}
impl Split for u128 {
    fn hi(self) -> u128 {
        self >> 64
    }

    fn lo(self) -> u128 {
        self & 0xffff_ffff_ffff_ffff
    }
}
