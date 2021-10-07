use crate::consts::DecimalStorage;
use crate::{ParseDecimalError, Rounding};

#[derive(Debug, PartialEq, Clone, Copy)]
pub struct Unpacked<T> {
    pub coefficient: T,
    pub exponent: u16,
    /// `true` if number is negative
    pub sign: bool,
}

impl<T: DecimalStorage> Unpacked<T> {
    pub fn new(value: T) -> Self {
        debug_assert!(
            (value & T::INFINITY_MASK) != T::INFINITY_MASK,
            "can only unpack finite numbers"
        );

        let sign = (value & T::SIGN_MASK) != T::zero();
        let mut unpacked = if (value & T::SPECIAL_ENC_MASK) == T::SPECIAL_ENC_MASK {
            Self {
                coefficient: (value & T::SHORT_COEFF_MASK) | T::SHORT_COEFF_HIGH_BIT,
                exponent: ((value >> T::SHORT_COEFF_SHIFT) & T::EXPONENT_MASK)
                    .to_u16()
                    .unwrap(),
                sign,
            }
        } else {
            Self {
                coefficient: value & T::LONG_COEFF_MASK,
                exponent: ((value >> T::LONG_COEFF_SHIFT) & T::EXPONENT_MASK)
                    .to_u16()
                    .unwrap(),
                sign,
            }
        };

        // Treat illegal significants as 0
        if unpacked.coefficient >= T::MAXIMUM_COEFFICIENT {
            unpacked.coefficient = T::zero();
        }

        unpacked
    }

    /// Pack back into a decimal. This variant does not handle any rounding or any out-of-bounds
    /// values (will panic in debug mode). `pack_with_rounding` handles rounding to make sure
    /// value could be represented.
    fn pack(self: Self) -> T {
        debug_assert!(
            self.coefficient < T::MAXIMUM_COEFFICIENT,
            "coefficient '{}' is too large for {}-bit decimal",
            self.coefficient,
            T::BITS,
        );
        debug_assert!(
            self.exponent < (0b11 << T::EXPONENT_BITS),
            "exponent '{}' is too large for {}-bit decimal",
            self.coefficient,
            T::BITS,
        );

        let mut value: T = if self.sign { T::SIGN_MASK } else { T::zero() };
        if (self.coefficient & T::SHORT_COEFF_HIGH_BIT) == T::SHORT_COEFF_HIGH_BIT {
            value |= T::SPECIAL_ENC_MASK;
            value |= self.coefficient & T::SHORT_COEFF_MASK;
            value |= T::from_u16(self.exponent).unwrap() << T::SHORT_COEFF_SHIFT;
        } else {
            value |= self.coefficient & T::LONG_COEFF_MASK;
            value |= T::from_u16(self.exponent).unwrap() << T::LONG_COEFF_SHIFT;
        }
        value
    }

    pub fn is_normal_internal(self) -> bool {
        if self.exponent >= (T::COEFFICIENT_SIZE - 1) as u16 {
            true // Normal
        } else {
            // Check if coefficient is high enough for an exponent
            let coeff = self
                .coefficient
                .checked_mul(&T::FACTORS[self.exponent as usize]);
            // If overflowed, then it's guaranteed to be a "normal" number
            coeff.map_or(true, |v| v >= (T::MAXIMUM_COEFFICIENT / T::TEN))
        }
    }

    pub fn n_digits(&self) -> u16 {
        let bits = T::BITS - T::leading_zeros(self.coefficient);
        let digits = T::DIGITS[bits as usize];
        if digits >= 0 {
            return digits as u16;
        }
        let digits = (-digits) as u16;
        return if self.coefficient < T::FACTORS[usize::from(digits)] {
            digits
        } else {
            digits + 1
        };
    }

    pub fn round_and_pack(mut self, rounding: Rounding) -> T {
        let digits = self.n_digits();

        // We could have up to 3 extra digits here. 2 digits could come in cases we scale one
        // operand by `100` plus 1 extra digit for overflow (`999_999_900` plus `123`, for example).
        if digits > T::COEFFICIENT_SIZE {
            let extra = digits - T::COEFFICIENT_SIZE;
            self.apply_rounding(extra, rounding);
        }

        // Round to infinity, value is too large
        if self.exponent as isize > T::EXPONENT_MAX {
            if rounding == Rounding::Zero
                || (rounding == Rounding::Down && !self.sign)
                || (rounding == Rounding::Up && self.sign)
            {
                self.coefficient = T::MAXIMUM_COEFFICIENT - T::one();
                self.exponent = T::EXPONENT_MAX as u16;
            } else {
                return infinity(self.sign);
            }
        }
        self.pack()
    }

    /// Increase precision of the value up to the given exponent. Keeps value in the range of allowed
    /// coefficient limits. For example, if we have 32-bit decimal `999_999` and exponent difference
    /// is `5`, we could only scale number by one digit (since it is already using 6 out of 7 allowed
    /// decimal digits).
    fn increase_precision(&mut self, exponent: u16) {
        // How many extra decimal digits can we use for scaling
        let max_extra = T::COEFFICIENT_SIZE - self.n_digits();
        let factor: u16 = (self.exponent - exponent).min(max_extra);
        self.coefficient *= T::FACTORS[factor as usize];
        self.exponent -= factor;
    }

    /// Round last `extra` digits from the number
    fn apply_rounding(&mut self, extra: u16, rounding: Rounding) {
        let factor = T::FACTORS[usize::from(extra)];
        let half_factor = factor >> 1;
        let remainder = self.coefficient % factor;
        self.coefficient /= factor;
        let round_up = match rounding {
            Rounding::Nearest if remainder == half_factor => is_odd(self.coefficient),
            Rounding::Nearest => remainder > half_factor,
            Rounding::Down => remainder != T::zero() && self.sign,
            Rounding::Up => remainder != T::zero() && !self.sign,
            Rounding::Zero => false,
            Rounding::TiesAway => remainder >= half_factor,
        };
        if round_up {
            self.coefficient += T::one();
            // Overflow, need to remove one more digit. Since we added `1`, it can only be the
            // upper bound itself. Divide it by 10.
            if self.coefficient == T::MAXIMUM_COEFFICIENT {
                self.coefficient /= T::TEN;
                self.exponent += 1;
            }
        }
        self.exponent += extra;
    }
}

pub fn is_odd<T: DecimalStorage>(value: T) -> bool {
    value & T::one() == T::one()
}

pub fn infinity<T: DecimalStorage>(negative: bool) -> T {
    if negative {
        T::NEG_INFINITY_MASK
    } else {
        T::INFINITY_MASK
    }
}

pub fn sign<T: DecimalStorage>(negative: bool) -> T {
    if negative {
        T::SIGN_MASK
    } else {
        T::zero()
    }
}

/// Take the zero with the smallest exponent (most "precise" zero). Take the sign depending on rounding.
pub fn min_zero<T>(lhs: Unpacked<T>, rhs: Unpacked<T>, rounding: Rounding) -> Unpacked<T> {
    // Pick the zero with smallest exponent
    let sign = if lhs.sign != rhs.sign {
        rounding == Rounding::Down
    } else {
        lhs.sign
    };
    Unpacked {
        exponent: lhs.exponent.min(rhs.exponent),
        sign,
        ..lhs
    }
}

/// Normalize NaN (keep "payload" in significand)
pub fn normalize_nan<T: DecimalStorage>(value: T) -> T {
    debug_assert_eq!(value & T::NAN_MASK, T::NAN_MASK, "must be NaN");

    let payload_mask = (T::one() << T::COEFFICIENT_BITS) - T::one();
    let coefficient = value & payload_mask;
    // Why divide by 10? Not sure. Intel's implementation does not like payloads larger than
    // 1_000_000 (for 32-bit decimal) even though we can fit up to 9_999_999. I think, the
    // reason is that we only use `COEFFICIENT_BITS` of payload bits rather than full
    // coefficient mask (`LONG_COEFF_MASK` or `SHORT_COEFF_MASK`).
    return if coefficient < T::MAXIMUM_COEFFICIENT / T::TEN {
        // Keep the payload -- fits into the range
        value & (T::NAN_MASK | T::SIGN_MASK | payload_mask)
    } else {
        // Reset payload to `0`
        value & (T::NAN_MASK | T::SIGN_MASK)
    };
}

pub fn parse_rounding<T: DecimalStorage>(
    s: &str,
    rounding: Rounding,
) -> Result<T, ParseDecimalError> {
    let mut bytes = s.as_bytes();
    // Sign mask of the number; 0 for positive numbers
    let mut unpacked = Unpacked {
        coefficient: T::zero(),
        exponent: 0,
        sign: false,
    };

    if bytes.is_empty() {
        return Err(ParseDecimalError::empty());
    }
    if bytes.first() == Some(&b'-') {
        unpacked.sign = true;
        bytes = &bytes[1..];
    } else if bytes.first() == Some(&b'+') {
        bytes = &bytes[1..];
    };
    if bytes.is_empty() {
        return Err(ParseDecimalError::invalid());
    }

    if bytes == b"inf" {
        return Ok(T::INFINITY_MASK | sign(unpacked.sign));
    }

    if bytes == b"NaN" || bytes == b"qNaN" {
        return Ok(T::NAN_MASK | sign(unpacked.sign));
    }

    if bytes == b"sNaN" {
        return Ok(T::NAN_MASK | sign(unpacked.sign) | T::SIGNALING_NAN_MASK);
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
        let exp = T::BIAS - exponent.min(T::BIAS);
        let value =
            ((T::from_u16(exp as u16).unwrap()) << (T::COEFFICIENT_BITS + 3)) | sign(unpacked.sign);
        return Ok(value);
    }

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
        if coeff_digits <= T::COEFFICIENT_SIZE {
            unpacked.coefficient *= T::TEN;
            unpacked.coefficient += T::from_u8(digit).unwrap();
        } else if coeff_digits == T::COEFFICIENT_SIZE + 1 {
            // We are at the first digit that will be rounded off
            let round_up = match rounding {
                Rounding::Nearest if digit == 5 => {
                    // FIXME: invalid! should look ahead for first non-zero!
                    let ahead = bytes.get(1).copied().unwrap_or(b'0');
                    is_odd(unpacked.coefficient) || ahead > b'0' && ahead <= b'9'
                }
                Rounding::Nearest => digit > 5,
                // FIXME: should check that remaining digits are non-zero!
                Rounding::Down => unpacked.sign,
                // FIXME: should check that remaining digits are non-zero!
                Rounding::Up => !unpacked.sign,
                Rounding::Zero => false,
                Rounding::TiesAway => digit >= 5,
            };
            if round_up {
                unpacked.coefficient += T::one();
            }
            if unpacked.coefficient == T::MAXIMUM_COEFFICIENT {
                // Essentially, divide coefficient by 10 -- it's too big now!
                unpacked.coefficient = T::FACTORS[usize::from(T::COEFFICIENT_SIZE) - 1];
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

    let mut exponent: isize = (T::BIAS as isize) - exponent;

    // Bring exponent into proper range by scaling the coefficient
    if exponent < 0 {
        // FIXME: might trim exponent here... should compare before going from isize to u16
        let exp = (-exponent) as u16;
        if exp < T::COEFFICIENT_SIZE {
            unpacked.apply_rounding(exp, rounding);
        } else {
            unpacked.coefficient = T::zero();
        }
        exponent = 0;
    } else if exponent > T::EXPONENT_MAX {
        // FIXME: need test case for proper rounding in this case!
        let delta = (exponent - T::EXPONENT_MAX) as usize;
        let can_accomodate_digits = T::COEFFICIENT_SIZE - unpacked.n_digits();
        if unpacked.coefficient == T::zero() {
            exponent = T::EXPONENT_MAX;
        } else if delta > usize::from(can_accomodate_digits) {
            // Cannot accomodate extra digits, return infinity
            return Ok(infinity(unpacked.sign));
        } else {
            unpacked.coefficient *= T::FACTORS[delta];
            exponent = T::EXPONENT_MAX;
        }
    }
    unpacked.exponent = exponent as u16;
    Ok(unpacked.pack())
}

/// Add two decimal numbers with rounding.
pub fn add<T: DecimalStorage>(lhs: T, rhs: T, rounding: Rounding) -> T {
    let lhs_is_nan = (lhs & T::NAN_MASK) == T::NAN_MASK;
    let rhs_is_nan = (rhs & T::NAN_MASK) == T::NAN_MASK;
    let lhs_is_infinite = (lhs & T::NAN_MASK) == T::INFINITY_MASK;
    let rhs_is_infinite = (rhs & T::NAN_MASK) == T::INFINITY_MASK;
    let lhs_sign = (lhs & T::SIGN_MASK) != T::zero();
    let rhs_sign = (rhs & T::SIGN_MASK) != T::zero();
    if lhs_is_nan {
        return normalize_nan(lhs);
    } else if rhs_is_nan {
        return normalize_nan(rhs);
    } else if lhs_is_infinite && rhs_is_infinite && lhs_sign != rhs_sign {
        // Opposite signed infinity
        return T::NAN_MASK;
    } else if lhs_is_infinite {
        return infinity(lhs_sign);
    } else if rhs_is_infinite {
        return infinity(rhs_sign);
    }

    // Now we can unpack numbers as they are not NaN or Infinite
    let mut lhs_unpacked = Unpacked::new(lhs);
    let mut rhs_unpacked = Unpacked::new(rhs);

    // Handle zeroes
    if lhs_unpacked.coefficient == T::zero() && rhs_unpacked.coefficient == T::zero() {
        // Pick the zero with smallest exponent
        return min_zero(lhs_unpacked, rhs_unpacked, rounding).pack();
    } else if lhs_unpacked.coefficient == T::zero() {
        if lhs_unpacked.exponent >= rhs_unpacked.exponent {
            return rhs;
        }
        // Need to rescale lhs to lhs exponent (or as much as we can without losing digits)
        rhs_unpacked.increase_precision(lhs_unpacked.exponent);
        return rhs_unpacked.pack();
    } else if rhs_unpacked.coefficient == T::zero() {
        if rhs_unpacked.exponent >= lhs_unpacked.exponent {
            return lhs;
        }
        // Need to rescale lhs to lhs exponent (or as much as we can without losing digits)
        lhs_unpacked.increase_precision(rhs_unpacked.exponent);
        return lhs_unpacked.pack();
    }

    // Done with handling zeros

    // make `a` to be the number with bigger exponent
    let (mut a, mut b) = if lhs_unpacked.exponent < rhs_unpacked.exponent {
        (rhs_unpacked, lhs_unpacked)
    } else {
        (lhs_unpacked, rhs_unpacked)
    };

    a.increase_precision(b.exponent);

    let mut diff_exp = a.exponent - b.exponent;

    // We can accommodate up to 2 more digits in our coefficient storage without overflow
    // (temporarily, we won't be able to represent it as a decimal in the end, but we will do
    // rounding). Increase precision of `a` by up to two digits, to trigger rounding in the end.
    // Two digits are necessary so we don't get case where we take `1_000_000`, add one more digit
    // to get `10_000_000`, then subtract "epsilon" (very small) `b` and get `9_999_999` which
    // would skip rounding (as it fits as-is into 7 allowed decimal digits).
    match diff_exp {
        0 => {}
        1 => {
            a.coefficient *= T::TEN;
            a.exponent -= 1;
            diff_exp -= 1;
        }
        _ => {
            a.coefficient *= T::TEN * T::TEN;
            a.exponent -= 2;
            diff_exp -= 2;
        }
    }

    // Scale down `b`. Check for necessity of removing a tie break. We know that last two digits
    // of `a` are zeros (because we would only need to scale `b` if scale difference is too big,
    // in which case we add two more digits to `a`). If last digit of `b` is `0` or `5`, this
    // will create a "tie" during certain rounding modes (`Nearest`, `TiesAway`) which would
    // depend on digits in `b` we rounded off here. Check that condition and remove tie by
    // adding a small "epsilon" of `1` to `b`.
    if diff_exp > T::COEFFICIENT_SIZE {
        // We know `b` wasn't zero, so this is a "tie" scenario -- use small "epsilon" of `1`.
        b.coefficient = T::one();
    } else if diff_exp != 0 {
        let factor = T::FACTORS[usize::from(diff_exp)];
        let tie = b.coefficient % factor;
        b.coefficient /= factor;
        if b.coefficient % (T::TEN >> 1) == T::zero() && tie > T::zero() {
            // break the tie
            b.coefficient += T::one();
        }
    }
    b.exponent += diff_exp;

    debug_assert_eq!(
        a.exponent, b.exponent,
        "Both numbers must be in the same scale"
    );

    let different_sign = lhs_unpacked.sign != rhs_unpacked.sign;
    if different_sign {
        a.coefficient = a.coefficient.wrapping_sub(&b.coefficient);
    } else {
        a.coefficient = a.coefficient.wrapping_add(&b.coefficient);
    }
    if a.coefficient & (T::one() << (T::BITS as usize - 1)) != T::zero() {
        a.sign = !a.sign;
        a.coefficient = T::zero().wrapping_sub(&a.coefficient);
    } else if a.coefficient == T::zero() {
        a.sign = rounding == Rounding::Down;
    }
    a.round_and_pack(rounding)
}
