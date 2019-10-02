// **NOTE**: THIS FILE IS AUTO-GENERATED FROM d128_impl.rs. DO NOT MODIFY!
use crate::consts::DecimalProps;
use crate::Decimal32;
use crate::{FpCategory, ParseDecimalError, Unpacked};
use std::fmt;
use std::marker::PhantomData;
use std::str::FromStr;

const SIGN_MASK: u32 = 0b10000000 << (u32::BITS - 8);
const SPECIAL_ENC_MASK: u32 = 0b01100000 << (u32::BITS - 8);
const INFINITY_MASK: u32 = 0b01111000 << (u32::BITS - 8);
const NAN_MASK: u32 = 0b01111100 << (u32::BITS - 8);

impl<Ctx: crate::Context> Clone for Decimal32<Ctx> {
    fn clone(&self) -> Self {
        Decimal32(self.0, PhantomData)
    }
}

impl<Ctx: crate::Context> Copy for Decimal32<Ctx> {}

impl<Ctx: crate::Context> fmt::Debug for Decimal32<Ctx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[0x{1:00$x}]", u32::BITS / 4, self.0)
    }
}

impl<Ctx: crate::Context> Decimal32<Ctx> {
    /// Returns `true` if this value is `NaN` and `false` otherwise.
    pub fn is_nan(self) -> bool {
        (self.0 & NAN_MASK) == NAN_MASK
    }

    /// Returns `true` if this value is positive infinity or negative infinity and `false`
    /// otherwise.
    pub fn is_infinite(self) -> bool {
        (self.0 & NAN_MASK) == INFINITY_MASK
    }

    /// Returns `true` if this number is neither infinite nor `NaN`.
    pub fn is_finite(self) -> bool {
        (self.0 & INFINITY_MASK) != INFINITY_MASK
    }

    /// Returns `true` if the number is neither zero, infinite, [subnormal][subnormal], or
    /// `NaN`.
    ///
    /// [subnormal]: https://en.wikipedia.org/wiki/Denormal_number
    pub fn is_normal(self) -> bool {
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
    pub fn is_subnormal(self) -> bool {
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
                return FpCategory::Zero;
            } else if Self::is_normal_internal(unpacked) {
                FpCategory::Normal
            } else {
                FpCategory::Subnormal
            }
        }
    }

    /// Returns `true` if and only if `self` has a positive sign, including `+0.0`, `NaN`s
    /// with positive sign bit and positive infinity.
    pub fn is_sign_positive(self) -> bool {
        !self.is_sign_negative()
    }

    /// Returns `true` if and only if `self` has a negative sign, including `-0.0`, `NaN`s
    /// with negative sign bit and negative infinity.
    pub fn is_sign_negative(self) -> bool {
        (self.0 & SIGN_MASK) != 0
    }

    /// Raw transmutation to the underlying type.
    pub fn to_bits(self) -> u32 {
        self.0
    }

    /// Raw transmutation from the underlying type.
    pub fn from_bits(bits: u32) -> Self {
        Decimal32(bits, PhantomData)
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

    fn unpack(self) -> Unpacked<u32> {
        debug_assert!(self.is_finite(), "can only unpack finite numbers");

        const EXPONENT_MASK: u32 = (1 << (u32::EXPONENT_BITS + 2)) - 1;
        const LONG_COEFF_SHIFT: usize = u32::COEFFICIENT_BITS + 3;
        const LONG_COEFF_MASK: u32 = (1 << LONG_COEFF_SHIFT) - 1;

        const SHORT_COEFF_SHIFT: usize = u32::COEFFICIENT_BITS + 1;
        const SHORT_COEFF_MASK: u32 = (1 << SHORT_COEFF_SHIFT) - 1;
        const SHORT_COEFF_HIGH_BIT: u32 = 1 << LONG_COEFF_SHIFT;

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
        if unpacked.coefficient >= u32::MAXIMUM_COEFFICIENT {
            unpacked.coefficient = 0;
        }

        unpacked
    }
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
///
/// # Return value
///
/// `Err(ParseDecimalError)` if the string did not represent a valid
/// number.  Otherwise, `Ok(n)` where `n` is the floating-point decimal
/// number represented by `src`.
impl<Ctx: crate::Context> FromStr for Decimal32<Ctx> {
    type Err = ParseDecimalError;

    fn from_str(s: &str) -> Result<Self, ParseDecimalError> {
        let mut bytes = s.as_bytes();
        let mut sign: u32 = 0;

        if bytes.is_empty() {
            return Err(ParseDecimalError::Empty);
        }
        if bytes.first() == Some(&b'-') {
            sign = SIGN_MASK;
            bytes = &bytes[1..];
        } else if bytes.first() == Some(&b'+') {
            bytes = &bytes[1..];
        };
        if bytes.is_empty() {
            return Err(ParseDecimalError::Invalid);
        }

        if bytes == b"inf" {
            return Ok(Self::from_bits(INFINITY_MASK | sign));
        }

        if bytes == b"NaN" {
            return Ok(Self::from_bits(NAN_MASK));
        }

        while bytes.first() == Some(&b'0') {
            bytes = &bytes[1..];
        }

        let mut zeroes = 0;
        let mut has_point = false;
        if bytes.first() == Some(&b'.') {
            has_point = true;
            bytes = &bytes[1..];

            while bytes.first() == Some(&b'0') {
                bytes = &bytes[1..];
                zeroes += 1;
            }
        }

        if bytes.is_empty() {
            let exp = if u32::BIAS < zeroes {
                0
            } else {
                u32::BIAS - zeroes
            };
            let value = (exp << (u32::COEFFICIENT_BITS + 3)) | sign;
            return Ok(Self::from_bits(value));
        }

        while bytes
            .first()
            .map_or(false, |b| *b == b'.' || (*b >= b'0' && *b <= b'9'))
        {
            zeroes += 1;
            if bytes[0] == b'.' {
                if has_point {
                    return Err(ParseDecimalError::Invalid);
                }
                has_point = true;
                zeroes = 0;
            }
            bytes = &bytes[1..];
        }
        unimplemented!()
    }
}
