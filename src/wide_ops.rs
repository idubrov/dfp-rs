use crate::traits::BasicInt;
use crate::u256;

/// "Wide" multiplication and division.
pub trait WideOps: Sized {
    type Wide: BasicInt;
    fn wide_mul(self, rhs: Self) -> Self::Wide;
    fn wide_div_rem(value: Self::Wide, divisor: Self) -> (Self, Self);
    fn wide(hi: Self, lo: Self) -> Self::Wide;
    fn split(value: Self::Wide) -> (Self, Self);
}

impl WideOps for u32 {
    type Wide = u64;

    fn wide_mul(self, rhs: u32) -> u64 {
        let result = u64::from(self) * u64::from(rhs);
        let hi = (result >> 32) as u32;
        let lo = result as u32;
        return Self::wide(hi, lo);
    }
    fn wide_div_rem(value: u64, divisor: u32) -> (u32, u32) {
        let quotient = value / u64::from(divisor);
        debug_assert!(quotient <= u64::from(u32::MAX));
        let remainder = (value % u64::from(divisor)) as u32;
        (quotient as u32, remainder)
    }

    fn wide(hi: Self, lo: Self) -> u64 {
        (u64::from(hi) << 32) | u64::from(lo)
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

    fn wide(hi: Self, lo: Self) -> u128 {
        (u128::from(hi) << 64) | u128::from(lo)
    }

    fn split(value: u128) -> (u64, u64) {
        ((value >> 64) as u64, value as u64)
    }
}

impl WideOps for u128 {
    type Wide = u256;

    fn wide_mul(self, rhs: u128) -> u256 {
        let lhs = self;
        let tmp0 = lhs.hi() * rhs.lo();
        let tmp1 = rhs.hi() * lhs.lo();
        let lowest = lhs.lo() * rhs.lo();
        let intermediate = lowest.hi() + tmp0.lo() + tmp1.lo();
        let hi = lhs.hi() * rhs.hi() + tmp0.hi() + tmp1.hi() + intermediate.hi();
        let lo = (intermediate.lo() << 64) + lowest.lo();
        return Self::wide(hi, lo);
    }

    fn wide_div_rem(value: u256, divisor: u128) -> (u128, u128) {
        let quotient = value / u256::from(divisor);
        debug_assert!(quotient <= u256::from(u128::MAX));
        let remainder = (value % u256::from(divisor)).as_u128();
        (quotient.as_u128(), remainder)

        // // We only can have results that will fit u128
        // debug_assert!(value.hi < divisor, "unsupported");
        //
        // if value.hi == 0 {
        //     // Fast path, can use regular 128 arithmetic
        //     let quotent = value.lo / divisor;
        //     let remainder = value.lo % divisor;
        //     return (quotent, remainder);
        // }
        //
        // assert_ne!(divisor, 0, "division by zero");
        //
        // let divident_bits = 256 - value.hi.leading_zeros();
        // let divisor_bits = 128 - divisor.leading_zeros();
        //
        // // When shift is 128, we know that `hi` is less than `divisor`, so the first digit of
        // // result will necessarily be `0`. Therefore, just use shift of `127`.
        // let shift = (divident_bits - divisor_bits).min(127);
        //
        // let mut remainder = value;
        // let mut divisor256 = u256::new(0, divisor) << shift;
        // let mut mask = 1u128 << shift;
        // let mut quotent: u128 = 0;
        // loop {
        //     // Can finish with "fast" implementation.
        //     if remainder.hi == 0 {
        //         quotent |= remainder.lo / divisor;
        //         remainder.lo %= divisor;
        //         break;
        //     }
        //
        //     if remainder >= divisor256 {
        //         remainder -= divisor256;
        //         quotent |= mask;
        //     }
        //
        //     mask >>= 1;
        //     if mask == 0 {
        //         break;
        //     }
        //     divisor256 = divisor256 >> 1;
        // }
        // (quotent, remainder.lo)
    }

    fn wide(hi: Self, lo: Self) -> u256 {
        (u256::from(hi) << 128) | u256::from(lo)
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
        self & 0xffffffff_ffffffff
    }
}
