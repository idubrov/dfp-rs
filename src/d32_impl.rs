use crate::consts::factors;
use crate::consts::DecimalProps;
use crate::{Decimal, FpCategory, ParseDecimalError, Rounding, Unpacked};
use std::fmt;
use std::marker::PhantomData;
use std::str::FromStr;

const SIGN_MASK: u32 = 0b1000_0000 << (u32::BITS - 8);

/// Mask for "special encoding" (two bits after the sign bit). If the 2 bits after the sign bit
/// are `11`, then we use a "short" coefficient representation with implicit `100` prefix.
const SPECIAL_ENC_MASK: u32 = 0b0110_0000 << (u32::BITS - 8);
const INFINITY_MASK: u32 = 0b0111_1000 << (u32::BITS - 8);
const NAN_MASK: u32 = 0b0111_1100 << (u32::BITS - 8);
const SIGNALING_NAN_MASK: u32 = 0b0000_0010 << (u32::BITS - 8);
/// Add 2 -- two bits in front of the exponent bits are also part of the exponent, as long as they
/// are not `11`.
const EXPONENT_MASK: u32 = (1 << (u32::EXPONENT_BITS + 2)) - 1;
const EXPONENT_MAX: isize = (0b11 << u32::EXPONENT_BITS) - 1;

// If the most significant 4 bits of the significand are between 0 and 7, the encoded value
// begins as follows:
// s eemmm xxx   Coefficient begins with 0mmm
const LONG_COEFF_SHIFT: usize = u32::COEFFICIENT_BITS + 3;
const LONG_COEFF_MASK: u32 = (1 << LONG_COEFF_SHIFT) - 1;

// If the leading 4 bits of the significand are binary 1000 or 1001 (decimal 8 or 9), the
// number begins as follows:
// s 11eem xxx Coefficient begins with 100m
const SHORT_COEFF_SHIFT: usize = u32::COEFFICIENT_BITS + 1;
const SHORT_COEFF_MASK: u32 = (1 << SHORT_COEFF_SHIFT) - 1;
const SHORT_COEFF_HIGH_BIT: u32 = 1 << LONG_COEFF_SHIFT;

impl<Ctx: crate::Context> Clone for Decimal<u32, Ctx> {
    fn clone(&self) -> Self {
        Decimal(self.0, PhantomData)
    }
}

impl<Ctx: crate::Context> Copy for Decimal<u32, Ctx> {}

impl<Ctx: crate::Context> fmt::Debug for Decimal<u32, Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[0x{1:00$x}]", (u32::BITS as usize) / 4, self.0)
    }
}

impl<Ctx: crate::Context> From<Decimal<u32, Ctx>> for Unpacked<u32> {
    fn from(value: Decimal<u32, Ctx>) -> Self {
        debug_assert!(value.is_finite(), "can only unpack finite numbers");

        let sign = (value.0 & SIGN_MASK) != 0;
        let mut unpacked = if (value.0 & SPECIAL_ENC_MASK) == SPECIAL_ENC_MASK {
            Unpacked {
                coefficient: (value.0 & SHORT_COEFF_MASK) | SHORT_COEFF_HIGH_BIT,
                exponent: ((value.0 >> SHORT_COEFF_SHIFT) & EXPONENT_MASK) as u16,
                sign,
            }
        } else {
            Unpacked {
                coefficient: value.0 & LONG_COEFF_MASK,
                exponent: ((value.0 >> LONG_COEFF_SHIFT) & EXPONENT_MASK) as u16,
                sign,
            }
        };

        // Treat illegal significants as 0
        if unpacked.coefficient >= u32::MAXIMUM_COEFFICIENT {
            unpacked.coefficient = 0;
        }

        unpacked
    }
}

impl<Ctx: crate::Context> From<Unpacked<u32>> for Decimal<u32, Ctx> {
    fn from(unpacked: Unpacked<u32>) -> Self {
        debug_assert!(
            unpacked.coefficient < u32::MAXIMUM_COEFFICIENT,
            "coefficient is too large"
        );
        debug_assert!(
            unpacked.exponent < (0b11 << u32::EXPONENT_BITS),
            "exponent is too large"
        );

        let mut value: u32 = if unpacked.sign { SIGN_MASK } else { 0 };
        if (unpacked.coefficient & SHORT_COEFF_HIGH_BIT) == SHORT_COEFF_HIGH_BIT {
            value |= SPECIAL_ENC_MASK;
            value |= unpacked.coefficient & SHORT_COEFF_MASK;
            value |= u32::from(unpacked.exponent) << SHORT_COEFF_SHIFT;
        } else {
            value |= unpacked.coefficient & LONG_COEFF_MASK;
            value |= u32::from(unpacked.exponent) << LONG_COEFF_SHIFT;
        }
        Decimal(value, PhantomData)
    }
}

impl<Ctx: crate::Context> Decimal<u32, Ctx> {
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
    pub fn to_bits(&self) -> u32 {
        self.0
    }

    /// Raw transmutation from the underlying type.
    pub fn from_bits(bits: u32) -> Self {
        Decimal(bits, PhantomData)
    }

    pub fn abs(self) -> Self {
        Self::from_bits(self.0 & !SIGN_MASK)
    }

    fn is_normal_internal(unpacked: Unpacked<u32>) -> bool {
        if unpacked.exponent >= (u32::COEFFICIENT_SIZE - 1) as u16 {
            true // Normal
        } else {
            // Check if coefficient is high enough for an exponent
            let coeff = unpacked
                .coefficient
                .checked_mul(crate::consts::factors::u32[unpacked.exponent as usize]);
            // If overflowed, then it's guaranteed to be a "normal" number
            coeff.map_or(true, |v| v >= (u32::MAXIMUM_COEFFICIENT / 10))
        }
    }

    pub(crate) fn unpack(self) -> Unpacked<u32> {
        self.into()
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
        let mut sign: u32 = 0;

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
            let exp = u32::BIAS - exponent.min(u32::BIAS);
            let value = ((exp as u32) << (u32::COEFFICIENT_BITS + 3)) | sign;
            return Ok(Self::from_bits(value));
        }

        let mut coefficient: u32 = 0;
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
            if coeff_digits <= u32::COEFFICIENT_SIZE {
                coefficient *= 10;
                coefficient += u32::from(digit);
            } else if coeff_digits == u32::COEFFICIENT_SIZE + 1 {
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
                if coefficient == u32::MAXIMUM_COEFFICIENT {
                    // Essentially, divide coefficient by 10 -- it's too big now!
                    coefficient = crate::consts::factors::u32[u32::COEFFICIENT_SIZE - 1];
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

        let mut exponent: isize = (u32::BIAS as isize) - exponent;

        // Bring exponent into proper range by scaling the coefficient
        if exponent < 0 {
            let exp = (-exponent) as usize;
            if exp < factors::u32.len() {
                scale_coefficient(sign != 0, &mut coefficient, exp, rounding);
            } else {
                coefficient = 0;
            }
            exponent = 0;
        } else if exponent > EXPONENT_MAX {
            // FIXME: need test case for proper rounding in this case!
            let delta = (EXPONENT_MAX - exponent) as usize;
            if delta < crate::consts::factors::u32.len() {
                panic!("need to re-scale coefficient?")
            }
            exponent = EXPONENT_MAX;
        }
        let unpacked = Unpacked {
            coefficient,
            exponent: exponent as u16,
            sign: sign != 0,
        };
        Ok(unpacked.into())
    }
}

fn is_odd(value: u32) -> bool {
    value % 2 == 1
}

fn scale_coefficient(is_negative: bool, coefficient: &mut u32, factor: usize, rounding: Rounding) {
    let remainder = *coefficient % factors::u32[factor];
    let half = factors::u32[factor] / 2;
    *coefficient /= factors::u32[factor];
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

impl<Ctx: crate::Context> FromStr for Decimal<u32, Ctx> {
    type Err = ParseDecimalError;

    fn from_str(s: &str) -> Result<Self, ParseDecimalError> {
        Self::parse_rounding(s, Ctx::rounding())
    }
}
