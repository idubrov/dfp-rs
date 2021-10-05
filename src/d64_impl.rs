// **NOTE**: THIS FILE IS AUTO-GENERATED FROM d32_impl.rs. DO NOT MODIFY!
use crate::consts::DecimalProps;
use crate::{Decimal, FpCategory, ParseDecimalError, Rounding, Unpacked};
use std::fmt;
use std::marker::PhantomData;
use std::ops::Add;
use std::str::FromStr;

const SIGN_MASK: u64 = 0b1000_0000 << (u64::BITS - 8);

/// Mask for "special encoding" (two bits after the sign bit). If the 2 bits after the sign bit
/// are `11`, then we use a "short" coefficient representation with implicit `100` prefix.
const SPECIAL_ENC_MASK: u64 = 0b0110_0000 << (u64::BITS - 8);
const INFINITY_MASK: u64 = 0b0111_1000 << (u64::BITS - 8);
const NAN_MASK: u64 = 0b0111_1100 << (u64::BITS - 8);
const SIGNALING_NAN_MASK: u64 = 0b0000_0010 << (u64::BITS - 8);
/// Add 2 -- two bits in front of the exponent bits are also part of the exponent, as long as they
/// are not `11`.
const EXPONENT_MASK: u64 = (1 << (u64::EXPONENT_BITS + 2)) - 1;
// FIXME: make u16?
const EXPONENT_MAX: isize = (0b11 << u64::EXPONENT_BITS) - 1;

// If the most significant 4 bits of the significand are between 0 and 7, the encoded value
// begins as follows:
// s eemmm xxx   Coefficient begins with 0mmm
const LONG_COEFF_SHIFT: usize = u64::COEFFICIENT_BITS + 3;
const LONG_COEFF_MASK: u64 = (1 << LONG_COEFF_SHIFT) - 1;

// If the leading 4 bits of the significand are binary 1000 or 1001 (decimal 8 or 9), the
// number begins as follows:
// s 11eem xxx Coefficient begins with 100m
const SHORT_COEFF_SHIFT: usize = u64::COEFFICIENT_BITS + 1;
const SHORT_COEFF_MASK: u64 = (1 << SHORT_COEFF_SHIFT) - 1;
const SHORT_COEFF_HIGH_BIT: u64 = 1 << LONG_COEFF_SHIFT;

impl<Ctx: crate::Context> Clone for Decimal<u64, Ctx> {
    fn clone(&self) -> Self {
        Decimal(self.0, PhantomData)
    }
}

impl<Ctx: crate::Context> Copy for Decimal<u64, Ctx> {}

impl<Ctx: crate::Context> fmt::Debug for Decimal<u64, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[0x{1:00$x}]", (u64::BITS as usize) / 4, self.0)
    }
}

impl Unpacked<u64> {
    pub(crate) fn pack_with_rounding<Ctx: crate::Context>(mut self) -> Decimal<u64, Ctx> {
        // FIXME: incorrect rounding...
        if self.coefficient >= u64::MAXIMUM_COEFFICIENT * 100 {
            let digit = self.coefficient % 1000;
            self.coefficient /= 1000;
            let round_up = match Ctx::rounding() {
                Rounding::Nearest if digit == 500 => is_odd(self.coefficient),
                Rounding::Nearest => digit > 500,
                Rounding::Down => digit != 0 && self.sign,
                Rounding::Up => digit != 0 && !self.sign,
                Rounding::Zero => false,
                Rounding::TiesAway => digit >= 500,
            };
            if round_up {
                self.coefficient += 1;
            }
            self.exponent += 3;
            if self.coefficient == u64::MAXIMUM_COEFFICIENT {
                // Essentially, divide coefficient by 10 -- it's too big now!
                self.coefficient = u64::FACTORS[usize::from(u64::COEFFICIENT_SIZE) - 1];
                self.exponent += 1;
            }
        } else if self.coefficient >= u64::MAXIMUM_COEFFICIENT * 10 {
            let digit = self.coefficient % 100;
            self.coefficient /= 100;
            let round_up = match Ctx::rounding() {
                Rounding::Nearest if digit == 50 => is_odd(self.coefficient),
                Rounding::Nearest => digit > 50,
                Rounding::Down => digit != 0 && self.sign,
                Rounding::Up => digit != 0 && !self.sign,
                Rounding::Zero => false,
                Rounding::TiesAway => digit >= 50,
            };
            if round_up {
                self.coefficient += 1;
            }
            self.exponent += 2;
            if self.coefficient == u64::MAXIMUM_COEFFICIENT {
                // Essentially, divide coefficient by 10 -- it's too big now!
                self.coefficient = u64::FACTORS[usize::from(u64::COEFFICIENT_SIZE) - 1];
                self.exponent += 1;
            }
        } else if self.coefficient >= u64::MAXIMUM_COEFFICIENT {
            let digit = self.coefficient % 10;
            self.coefficient /= 10;
            let round_up = match Ctx::rounding() {
                Rounding::Nearest if digit == 5 => is_odd(self.coefficient),
                Rounding::Nearest => digit > 5,
                Rounding::Down => digit != 0 && self.sign,
                Rounding::Up => digit != 0 && !self.sign,
                Rounding::Zero => false,
                Rounding::TiesAway => digit >= 5,
            };
            if round_up {
                self.coefficient += 1;
            }
            self.exponent += 1;
            if self.coefficient == u64::MAXIMUM_COEFFICIENT {
                // Essentially, divide coefficient by 10 -- it's too big now!
                self.coefficient = u64::FACTORS[usize::from(u64::COEFFICIENT_SIZE) - 1];
                self.exponent += 1;
            }
        }
        // Round to infinity, value is too large
        if self.exponent as isize > EXPONENT_MAX {
            let rounding = Ctx::rounding();
            if rounding == Rounding::Zero
                || (rounding == Rounding::Down && !self.sign)
                || (rounding == Rounding::Up && self.sign)
            {
                self.coefficient = u64::MAXIMUM_COEFFICIENT - 1;
                self.exponent = EXPONENT_MAX as u16;
            } else {
                return infinity(self.sign);
            }
        }
        // Round to infinity, value is too large
        if self.exponent as isize > EXPONENT_MAX {
            let rounding = Ctx::rounding();
            if rounding == Rounding::Zero
                || (rounding == Rounding::Down && !self.sign)
                || (rounding == Rounding::Up && self.sign)
            {
                self.coefficient = u64::MAXIMUM_COEFFICIENT - 1;
                self.exponent = EXPONENT_MAX as u16;
            } else {
                return infinity(self.sign);
            }
        }
        self.pack()
    }

    /// Pack back into a decimal. This variant does not handle any rounding or any out-of-bounds
    /// values (will panic in debug mode). `pack_with_rounding` handles rounding to make sure
    /// value could be represented.
    fn pack<Ctx: crate::Context>(self: Self) -> Decimal<u64, Ctx> {
        debug_assert!(
            self.coefficient < u64::MAXIMUM_COEFFICIENT,
            "coefficient is too large"
        );
        debug_assert!(
            self.exponent < (0b11 << u64::EXPONENT_BITS),
            "exponent is too large"
        );

        let mut value: u64 = if self.sign { SIGN_MASK } else { 0 };
        if (self.coefficient & SHORT_COEFF_HIGH_BIT) == SHORT_COEFF_HIGH_BIT {
            value |= SPECIAL_ENC_MASK;
            value |= self.coefficient & SHORT_COEFF_MASK;
            value |= u64::from(self.exponent) << SHORT_COEFF_SHIFT;
        } else {
            value |= self.coefficient & LONG_COEFF_MASK;
            value |= u64::from(self.exponent) << LONG_COEFF_SHIFT;
        }
        Decimal(value, PhantomData)
    }
}

impl<Ctx: crate::Context> From<Decimal<u64, Ctx>> for Unpacked<u64> {
    fn from(value: Decimal<u64, Ctx>) -> Self {
        value.unpack()
    }
}

impl<Ctx: crate::Context> Decimal<u64, Ctx> {
    /// Positive `NaN` constant (not a number)
    pub const NAN: Self = Decimal(NAN_MASK, PhantomData);

    /// Positive infinity constant
    pub const INFINITY: Self = Decimal(INFINITY_MASK, PhantomData);

    /// Negative infinity constant
    pub const NEG_INFINITY: Self = Decimal(INFINITY_MASK | SIGN_MASK, PhantomData);

    /// Returns `true` if this value is `NaN` or `sNaN` and `false` otherwise.
    pub fn is_nan(&self) -> bool {
        (self.0 & NAN_MASK) == NAN_MASK
    }

    /// Returns `true` if this value is `sNaN` and `false` otherwise.
    pub fn is_snan(&self) -> bool {
        self.is_nan() && (self.0 & SIGNALING_NAN_MASK) == SIGNALING_NAN_MASK
    }

    /// Returns `true` if this value is positive infinity or negative infinity and `false`
    /// otherwise.
    pub fn is_infinite(&self) -> bool {
        (self.0 & NAN_MASK) == INFINITY_MASK
    }

    /// Returns `true` if this number is neither infinite nor `NaN`.
    pub fn is_finite(&self) -> bool {
        (self.0 & INFINITY_MASK) != INFINITY_MASK
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
        if unpacked.coefficient == 0 {
            return false; // Zero or illegal
        }
        Self::is_normal_internal(unpacked)
    }

    /// Returns `true` if the number is [subnormal][subnormal].
    ///
    /// [subnormal]: https://en.wikipedia.org/wiki/Denormal_number
    pub fn is_subnormal(&self) -> bool {
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
                FpCategory::Zero
            } else if Self::is_normal_internal(unpacked) {
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
        (self.0 & SIGN_MASK) != 0
    }

    /// Raw transmutation to the underlying type.
    pub fn to_bits(&self) -> u64 {
        self.0
    }

    /// Raw transmutation from the underlying type.
    pub fn from_bits(bits: u64) -> Self {
        Decimal(bits, PhantomData)
    }

    pub fn abs(self) -> Self {
        Self::from_bits(self.0 & !SIGN_MASK)
    }

    fn is_normal_internal(unpacked: Unpacked<u64>) -> bool {
        if unpacked.exponent >= (u64::COEFFICIENT_SIZE - 1) as u16 {
            true // Normal
        } else {
            // Check if coefficient is high enough for an exponent
            let coeff = unpacked
                .coefficient
                .checked_mul(u64::FACTORS[unpacked.exponent as usize]);
            // If overflowed, then it's guaranteed to be a "normal" number
            coeff.map_or(true, |v| v >= (u64::MAXIMUM_COEFFICIENT / 10))
        }
    }

    pub(crate) fn unpack(self) -> Unpacked<u64> {
        debug_assert!(self.is_finite(), "can only unpack finite numbers");

        let sign = (self.0 & SIGN_MASK) != 0;
        let mut unpacked = if (self.0 & SPECIAL_ENC_MASK) == SPECIAL_ENC_MASK {
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
        if unpacked.coefficient >= u64::MAXIMUM_COEFFICIENT {
            unpacked.coefficient = 0;
        }

        unpacked
    }

    /// Normalize NaN (keep "payload" in significand)
    pub(crate) fn normalize_nan(self) -> Self {
        debug_assert!(self.is_nan());
        const PAYLOAD_MASK: u64 = (1 << u64::COEFFICIENT_BITS) - 1;
        let coefficient = self.0 & PAYLOAD_MASK;
        // Why divide by 10? Not sure. Intel's implementation does not like payloads larger than
        // 1_000_000 (for 32-bit decimal) even though we can fit up to 9_999_999. I think, the
        // reason is that we only use `COEFFICIENT_BITS` of payload bits rather than full
        // coefficient mask (`LONG_COEFF_MASK` or `SHORT_COEFF_MASK`).
        return if coefficient < u64::MAXIMUM_COEFFICIENT / 10 {
            // Keep the payload -- fits into the range
            Self::from_bits(self.0 & (NAN_MASK | SIGN_MASK | PAYLOAD_MASK))
        } else {
            // Reset payload to `0`
            Self::from_bits(self.0 & (NAN_MASK | SIGN_MASK))
        };
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
        let mut bytes = s.as_bytes();
        // Sign mask of the number; 0 for positive numbers
        let mut sign: u64 = 0;

        if bytes.is_empty() {
            return Err(ParseDecimalError::empty());
        }
        if bytes.first() == Some(&b'-') {
            sign = SIGN_MASK;
            bytes = &bytes[1..];
        } else if bytes.first() == Some(&b'+') {
            bytes = &bytes[1..];
        };
        if bytes.is_empty() {
            return Err(ParseDecimalError::invalid());
        }

        if bytes == b"inf" {
            return Ok(Self::from_bits(INFINITY_MASK | sign));
        }

        if bytes == b"NaN" || bytes == b"qNaN" {
            return Ok(Self::from_bits(NAN_MASK | sign));
        }

        if bytes == b"sNaN" {
            return Ok(Self::from_bits(NAN_MASK | sign | SIGNALING_NAN_MASK));
        }

        // Drop leading zeroes
        while bytes.first() == Some(&b'0') {
            bytes = &bytes[1..];
        }

        // Negative exponent for power of 10 (negative since it's easier this way)
        let mut exponent: isize = 0;
        let mut has_point = false;

        // Count zeroes after the decimal point
        if bytes.first() == Some(&b'.') {
            has_point = true;
            bytes = &bytes[1..];

            while bytes.first() == Some(&b'0') {
                bytes = &bytes[1..];
                exponent += 1;
            }
            // FIXME: handle when exponent is too large!
        }

        // The result is zero, with `zeroes` leading zeroes
        if bytes.is_empty() {
            let exp = u64::BIAS - exponent.min(u64::BIAS);
            let value = ((exp as u64) << (u64::COEFFICIENT_BITS + 3)) | sign;
            return Ok(Self::from_bits(value));
        }

        let mut coefficient: u64 = 0;
        let mut coeff_digits = 0;
        while !bytes.is_empty() && (bytes[0] == b'.' || bytes[0].is_ascii_digit()) {
            if has_point {
                if bytes[0] == b'.' {
                    return Err(ParseDecimalError::invalid());
                }
                exponent += 1;
            } else if bytes[0] == b'.' {
                has_point = true;
                bytes = &bytes[1..];
                continue;
            }

            coeff_digits += 1;
            let digit = bytes[0] - b'0';
            if coeff_digits <= u64::COEFFICIENT_SIZE {
                coefficient *= 10;
                coefficient += u64::from(digit);
            } else if coeff_digits == u64::COEFFICIENT_SIZE + 1 {
                // We are at the first digit that will be rounded off
                let round_up = match rounding {
                    Rounding::Nearest if digit == 5 => {
                        // FIXME: invalid! should look ahead for first non-zero!
                        let ahead = bytes.get(1).copied().unwrap_or(b'0');
                        is_odd(coefficient) || ahead > b'0' && ahead <= b'9'
                    }
                    Rounding::Nearest => digit > 5,
                    // FIXME: should check that remaining digits are non-zero!
                    Rounding::Down => sign != 0,
                    // FIXME: should check that remaining digits are non-zero!
                    Rounding::Up => sign == 0,
                    Rounding::Zero => false,
                    Rounding::TiesAway => digit >= 5,
                };
                if round_up {
                    coefficient += 1;
                }
                if coefficient == u64::MAXIMUM_COEFFICIENT {
                    // Essentially, divide coefficient by 10 -- it's too big now!
                    coefficient = u64::FACTORS[usize::from(u64::COEFFICIENT_SIZE) - 1];
                    exponent -= 1;
                }
                exponent -= 1;
            } else {
                exponent -= 1;
            }
            bytes = &bytes[1..];
        }

        if !bytes.is_empty() {
            // FIXME: handle `.e10` invalid case
            if bytes[0] != b'E' && bytes[0] != b'e' {
                return Err(ParseDecimalError::invalid());
            }
            bytes = &bytes[1..];
            let end = bytes
                .iter()
                .position(|c| *c != b'-' && *c != b'+' && !c.is_ascii_digit())
                .unwrap_or_else(|| bytes.len());
            if end == 0 {
                return Err(ParseDecimalError::invalid());
            }
            exponent -= std::str::from_utf8(&bytes[..end])
                .unwrap()
                .parse::<isize>()
                .unwrap();
            bytes = &bytes[end..];
        }

        if !bytes.is_empty() {
            return Err(ParseDecimalError::invalid());
        }

        let mut exponent: isize = (u64::BIAS as isize) - exponent;

        // Bring exponent into proper range by scaling the coefficient
        if exponent < 0 {
            let exp = (-exponent) as usize;
            if exp < u64::FACTORS.len() {
                scale_coefficient(sign != 0, &mut coefficient, exp, rounding);
            } else {
                coefficient = 0;
            }
            exponent = 0;
        } else if exponent > EXPONENT_MAX {
            // FIXME: need test case for proper rounding in this case!
            let delta = (exponent - EXPONENT_MAX) as usize;
            let can_accomodate_digits = u64::COEFFICIENT_SIZE - n_digits(coefficient);
            if coefficient == 0 {
                exponent = EXPONENT_MAX;
            } else if delta > usize::from(can_accomodate_digits) {
                // Cannot accomodate extra digits, return infinity
                return Ok(infinity(sign != 0));
            } else {
                coefficient *= u64::FACTORS[delta];
                exponent = EXPONENT_MAX;
            }
        }
        let unpacked = Unpacked {
            coefficient,
            exponent: exponent as u16,
            sign: sign != 0,
        };
        Ok(unpacked.pack())
    }
}

fn is_odd(value: u64) -> bool {
    value % 2 == 1
}

fn scale_coefficient(is_negative: bool, coefficient: &mut u64, factor: usize, rounding: Rounding) {
    let remainder = *coefficient % u64::FACTORS[factor];
    let half = u64::FACTORS[factor] / 2;
    *coefficient /= u64::FACTORS[factor];
    let round_up = match rounding {
        Rounding::Nearest => remainder > half || (remainder == half && is_odd(*coefficient)),
        Rounding::Down => is_negative && remainder >= half,
        Rounding::Up => !is_negative && remainder >= half,
        Rounding::Zero => false,
        Rounding::TiesAway => remainder >= half,
    };
    if round_up {
        *coefficient += 1;
    }
}

impl<Ctx: crate::Context> FromStr for Decimal<u64, Ctx> {
    type Err = ParseDecimalError;

    fn from_str(s: &str) -> Result<Self, ParseDecimalError> {
        Self::parse_rounding(s, Ctx::rounding())
    }
}

fn n_digits(coefficient: u64) -> u16 {
    let bits = u64::BITS - u64::leading_zeros(coefficient);
    let digits = u64::DIGITS[bits as usize];
    if digits >= 0 {
        return digits as u16;
    }
    let digits = (-digits) as u16;
    return if coefficient < u64::FACTORS[usize::from(digits)] {
        digits
    } else {
        digits + 1
    };
}

fn increase_precision(value: &mut Unpacked<u64>, exponent: u16) {
    // How many extra decimal digits can we use for scaling
    let max_extra = u64::COEFFICIENT_SIZE - n_digits(value.coefficient);
    let factor: u16 = (value.exponent - exponent).min(max_extra);
    value.coefficient *= u64::FACTORS[factor as usize];
    value.exponent -= factor;
}

fn infinity<Ctx: crate::Context>(negative: bool) -> Decimal<u64, Ctx> {
    if negative {
        Decimal::<u64, Ctx>::NEG_INFINITY
    } else {
        Decimal::<u64, Ctx>::INFINITY
    }
}

impl<Ctx: crate::Context> Add for Decimal<u64, Ctx> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let lhs = self;

        if lhs.is_nan() {
            return lhs.normalize_nan();
        } else if rhs.is_nan() {
            return rhs.normalize_nan();
        } else if lhs.is_infinite()
            && rhs.is_infinite()
            && lhs.is_sign_positive() != rhs.is_sign_positive()
        {
            // Opposite signed infinity
            return Self::NAN;
        } else if lhs.is_infinite() {
            return infinity(lhs.is_sign_negative());
        } else if rhs.is_infinite() {
            return infinity(rhs.is_sign_negative());
        }

        // Now we can unpack numbers as they are not NaN or Infinite
        let mut lhs_unpacked = self.unpack();
        let mut rhs_unpacked = rhs.unpack();

        // Handle zeroes
        if lhs_unpacked.coefficient == 0 && rhs_unpacked.coefficient == 0 {
            // Pick the zero with smallest exponent
            let sign = if lhs_unpacked.sign != rhs_unpacked.sign {
                Ctx::rounding() == Rounding::Down
            } else {
                lhs_unpacked.sign
            };
            let result = Unpacked {
                coefficient: 0,
                exponent: lhs_unpacked.exponent.min(rhs_unpacked.exponent),
                sign,
            };
            return result.pack();
        } else if lhs_unpacked.coefficient == 0 {
            if lhs_unpacked.exponent >= rhs_unpacked.exponent {
                return rhs;
            }
            // Need to rescale lhs to lhs exponent (or as much as we can without losing digits)
            increase_precision(&mut rhs_unpacked, lhs_unpacked.exponent);
            return rhs_unpacked.pack();
        } else if rhs_unpacked.coefficient == 0 {
            if rhs_unpacked.exponent >= lhs_unpacked.exponent {
                return lhs;
            }
            // Need to rescale lhs to lhs exponent (or as much as we can without losing digits)
            increase_precision(&mut lhs_unpacked, rhs_unpacked.exponent);
            return lhs_unpacked.pack();
        }

        // Done with handling zeros

        // make `a` to be the number with bigger exponent
        let (mut a, mut b) = if lhs_unpacked.exponent < rhs_unpacked.exponent {
            (rhs_unpacked, lhs_unpacked)
        } else {
            (lhs_unpacked, rhs_unpacked)
        };

        increase_precision(&mut a, b.exponent);

        let mut diff_exp = a.exponent - b.exponent;

        // We can accommodate up to 2 more digits in our coefficient storage without overflow
        // (temporarily, we won't be able to represent it as a decimal in the end).
        // Increase precision of `a` by up to two digits, to trigger rounding in the end.
        // Two digits are necessary so we don't get case where we take `1_000_000`, add one more digit
        // to get `10_000_000`, then subtract "epsilon" (very small) `b` and get `9_999_999` which
        // would skip rounding (as it fits as-is).
        match diff_exp {
            0 => {}
            1 => {
                a.coefficient *= 10;
                a.exponent -= 1;
                diff_exp -= 1;
            }
            _ => {
                a.coefficient *= 100;
                a.exponent -= 2;
                diff_exp -= 2;
            }
        }

        // Scale down `b`
        if diff_exp > u64::COEFFICIENT_SIZE {
            // Too big of a difference, even after scaling `a` difference in exponent is more
            // than we have coefficient digits (so, `b` is essentially zero compared to `a`).
            b.coefficient = 0;
            b.exponent += diff_exp;
        } else if diff_exp != 0 {
            let tie = b.coefficient % u64::FACTORS[usize::from(diff_exp)];
            b.coefficient /= u64::FACTORS[usize::from(diff_exp)];
            if b.coefficient % 5 == 0 && tie > 0 {
                // round up, to remove tie break
                b.coefficient += 1;
            }
            b.exponent += diff_exp;
        }
        // We know `b` wasn't zero, so in case it is smaller than the scaling factor, keep some
        // "small" value epsilon of 1. Since we scaled `a` by at least two digits more, this will
        // be rounded.
        if b.coefficient == 0 {
            b.coefficient = 1;
        }

        debug_assert_eq!(
            a.exponent, b.exponent,
            "Both numbers must be in the same scale"
        );

        let different_sign = lhs.is_sign_positive() != rhs.is_sign_positive();
        if different_sign {
            b.coefficient = 0u64.wrapping_sub(b.coefficient);
        }

        a.coefficient = a.coefficient.wrapping_add(b.coefficient);
        if a.coefficient & (1 << (u64::BITS - 1)) != 0 {
            a.sign = !a.sign;
            a.coefficient = 0u64.wrapping_sub(a.coefficient);
        } else if a.coefficient == 0 {
            a.sign = Ctx::rounding() == Rounding::Down;
        }
        a.pack_with_rounding()
    }
}
