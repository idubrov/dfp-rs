use crate::traits::{BasicInt, DecimalStorage};
use crate::{ParseDecimalError, Rounding};

// Code used to generate lookup table.
// #[test]
// fn generate() {
//     println!("    1,");
//     let mut min: crate::u256_impl::u256 = 1.into();
//     for _ in 0..256 {
//         let next = min << 1;
//         let digits = min.to_string().len();
//         let next_digits = next.to_string().len();
//         if digits != next_digits {
//             println!("    {},", -(digits as isize));
//         } else {
//             println!("    {},", digits);
//         };
//         min = next;
//     }
// }

/// Lookup table to determine how many decimal digits do we need to represent coefficient with the
/// given amount of binary digits. If value in the array is negative, it indicates that we might
/// need `digits` or we might need `digits + 1` digits. If number is less than `factors[digits]`,
/// then we need `digits`, otherwise we need `digits + 1`. For example, if we have 4 bits, we could
/// have `0x1001` (which is `9`) or we could have `0x1010`, which is `10`. For this case, entry
/// (entry under index `[4]`) will be `-1`.
const DIGITS: [i8; 257] = [
    1, 1, 1, 1, -1, 2, 2, -2, 3, 3, -3, 4, 4, 4, -4, 5, 5, -5, 6, 6, -6, 7, 7, 7, -7, 8, 8, -8, 9,
    9, -9, 10, 10, 10, -10, 11, 11, -11, 12, 12, -12, 13, 13, 13, -13, 14, 14, -14, 15, 15, -15,
    16, 16, 16, -16, 17, 17, -17, 18, 18, -18, 19, 19, 19, -19, 20, 20, -20, 21, 21, -21, 22, 22,
    22, -22, 23, 23, -23, 24, 24, -24, 25, 25, 25, -25, 26, 26, -26, 27, 27, -27, 28, 28, 28, -28,
    29, 29, -29, 30, 30, -30, 31, 31, -31, 32, 32, 32, -32, 33, 33, -33, 34, 34, -34, 35, 35, 35,
    -35, 36, 36, -36, 37, 37, -37, 38, 38, 38, -38, 39, 39, -39, 40, 40, -40, 41, 41, 41, -41, 42,
    42, -42, 43, 43, -43, 44, 44, 44, -44, 45, 45, -45, 46, 46, -46, 47, 47, 47, -47, 48, 48, -48,
    49, 49, -49, 50, 50, 50, -50, 51, 51, -51, 52, 52, -52, 53, 53, 53, -53, 54, 54, -54, 55, 55,
    -55, 56, 56, 56, -56, 57, 57, -57, 58, 58, -58, 59, 59, -59, 60, 60, 60, -60, 61, 61, -61, 62,
    62, -62, 63, 63, 63, -63, 64, 64, -64, 65, 65, -65, 66, 66, 66, -66, 67, 67, -67, 68, 68, -68,
    69, 69, 69, -69, 70, 70, -70, 71, 71, -71, 72, 72, 72, -72, 73, 73, -73, 74, 74, -74, 75, 75,
    75, -75, 76, 76, -76, 77, 77, -77,
];

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
    fn pack(self) -> T {
        debug_assert!(
            self.coefficient < T::MAXIMUM_COEFFICIENT,
            "coefficient '{}' is too large for {}-bit decimal",
            self.coefficient,
            T::BITS,
        );
        debug_assert!(
            self.exponent < (0b11 << T::EXPONENT_BITS),
            "exponent '{}' is too large for {}-bit decimal",
            self.exponent,
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

    /// Fit coefficient by rounding
    pub fn fit_coefficient(&mut self, rounding: Rounding) {
        let digits = n_digits(self.coefficient);

        // We could have up to 3 extra digits here. 2 digits could come in cases we scale one
        // operand by `100` plus 1 extra digit for overflow (`999_999_900` plus `123`, for example).
        if digits > T::COEFFICIENT_SIZE {
            let extra = digits - T::COEFFICIENT_SIZE;
            self.apply_rounding(extra, rounding);
        }
    }

    /// Increase precision of the value up to the given exponent. Keeps value in the range of allowed
    /// coefficient limits. For example, if we have 32-bit decimal `999_999` and exponent difference
    /// is `5`, we could only scale number by one digit (since it is already using 6 out of 7 allowed
    /// decimal digits).
    fn increase_precision(&mut self, exponent: u16) {
        // How many extra decimal digits can we use for scaling
        let max_extra = T::COEFFICIENT_SIZE - n_digits(self.coefficient);
        let factor: u16 = (self.exponent - exponent).min(max_extra);
        self.coefficient *= T::FACTORS[factor as usize];
        self.exponent -= factor;
    }
}

impl<T: BasicInt> Unpacked<T> {
    /// Round last `extra` digits from the number
    fn apply_rounding(&mut self, digits_to_round: u16, rounding: Rounding) {
        if digits_to_round == 0 {
            // Nothing to do
            return;
        }
        let idx = usize::from(digits_to_round);
        let (quotent, remainder, half_factor) = if idx >= T::FACTORS.len() {
            // Just take some arbitrary large number
            // FIXME: is this correct?
            let half_factor = (*T::FACTORS.last().unwrap()) >> 1;
            (T::zero(), self.coefficient, half_factor)
        } else {
            let factor = T::FACTORS[usize::from(digits_to_round)];
            (
                self.coefficient / factor,
                self.coefficient % factor,
                factor >> 1,
            )
        };
        self.coefficient = quotent;
        let round_up = match rounding {
            Rounding::Nearest if remainder == half_factor => is_odd(self.coefficient),
            Rounding::Nearest => remainder > half_factor,
            Rounding::Down => remainder != T::zero() && self.sign,
            Rounding::Up => remainder != T::zero() && !self.sign,
            Rounding::Zero => false,
            Rounding::TiesAway => remainder >= half_factor,
        };
        if round_up {
            let digits = n_digits(self.coefficient);
            self.coefficient = self.coefficient + T::one();
            let digits2 = n_digits(self.coefficient);
            // Overflow, need to remove one more digit. Since we added `1`, it can only be the
            // upper bound itself. Divide it by 10.
            // FIXME: don't need to do that if we were rounding for exponent...
            if digits != digits2 {
                self.coefficient = self.coefficient / T::TEN;
                self.exponent += 1;
            }
        }
        self.exponent += digits_to_round;
    }
}

/// Get amount of decimal digits necessary to represent given coefficient.
pub fn n_digits<T: BasicInt>(coefficient: T) -> u16 {
    let bits = (8 * std::mem::size_of::<T>() as u32) - T::leading_zeros(coefficient);
    let digits = DIGITS[bits as usize];
    if digits >= 0 {
        return digits as u16;
    }
    let digits = (-digits) as u16;
    if coefficient < T::FACTORS[usize::from(digits)] {
        digits
    } else {
        digits + 1
    }
}

pub fn is_odd<T: BasicInt>(value: T) -> bool {
    value & T::one() == T::one()
}

pub fn infinity<T: DecimalStorage>(sign: bool) -> T {
    if sign {
        T::NEG_INFINITY_MASK
    } else {
        T::INFINITY_MASK
    }
}

pub fn rounded_infinity<T: DecimalStorage>(sign: bool, rounding: Rounding) -> T {
    if rounding == Rounding::Zero
        || (rounding == Rounding::Down && !sign)
        || (rounding == Rounding::Up && sign)
    {
        // Round to maximum representable value
        let rounded = Unpacked {
            coefficient: T::MAXIMUM_COEFFICIENT - T::one(),
            exponent: T::EXPONENT_MAX as u16,
            sign,
        };
        rounded.pack()
    } else {
        infinity(sign)
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
    if coefficient < T::MAXIMUM_COEFFICIENT / T::TEN {
        // Keep the payload -- fits into the range
        value & (T::NAN_MASK | T::SIGN_MASK | payload_mask)
    } else {
        // Reset payload to `0`
        value & (T::NAN_MASK | T::SIGN_MASK)
    }
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

    // Exponent as per its final representation (biased)
    let mut exponent2 = T::BIAS as isize;
    let mut has_point = false;

    // Count zeroes after the decimal point
    if bytes.first() == Some(&b'.') {
        has_point = true;
        bytes = &bytes[1..];

        while bytes.first() == Some(&b'0') {
            bytes = &bytes[1..];
            exponent2 -= 1;
        }
        // FIXME: handle when exponent is too small!
    }

    // The result is zero, with `zeroes` leading zeroes
    if bytes.is_empty() {
        let value = ((T::from_u16(exponent2 as u16).unwrap()) << (T::COEFFICIENT_BITS + 3))
            | sign(unpacked.sign);
        return Ok(value);
    }

    let mut coeff_digits = 0;
    while !bytes.is_empty() && (bytes[0] == b'.' || bytes[0].is_ascii_digit()) {
        if has_point {
            if bytes[0] == b'.' {
                return Err(ParseDecimalError::invalid());
            }
            exponent2 -= 1;
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
                exponent2 += 1;
            }
            exponent2 += 1;
        } else {
            exponent2 += 1;
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
        exponent2 += std::str::from_utf8(&bytes[..end])
            .unwrap()
            .parse::<isize>()
            .unwrap();
        bytes = &bytes[end..];
    }

    if !bytes.is_empty() {
        return Err(ParseDecimalError::invalid());
    }

    // Bring exponent into proper range by scaling the coefficient
    if exponent2 < 0 {
        // FIXME: might trim exponent here... should compare before going from isize to u16
        let scale = (-exponent2) as u16;
        if scale < T::COEFFICIENT_SIZE {
            unpacked.apply_rounding(scale, rounding);
        } else {
            unpacked.coefficient = T::zero();
        }
        unpacked.exponent = 0;
    } else if exponent2 > T::EXPONENT_MAX as isize {
        // FIXME: need test case for proper rounding in this case!
        let delta = (exponent2 as usize) - usize::from(T::EXPONENT_MAX);
        let can_accomodate_digits = T::COEFFICIENT_SIZE - n_digits(unpacked.coefficient);
        if unpacked.coefficient == T::zero() {
            unpacked.exponent = T::EXPONENT_MAX;
        } else if delta > usize::from(can_accomodate_digits) {
            // Cannot accomodate extra digits, return infinity
            return Ok(infinity(unpacked.sign));
        } else {
            unpacked.coefficient *= T::FACTORS[delta];
            unpacked.exponent = T::EXPONENT_MAX;
        }
    } else {
        unpacked.exponent = exponent2 as u16;
    }
    Ok(unpacked.pack())
}

/// Add two decimal numbers with rounding.
pub fn add<T: DecimalStorage>(lhs_raw: T, rhs_raw: T, rounding: Rounding) -> T {
    let lhs_is_nan = (lhs_raw & T::NAN_MASK) == T::NAN_MASK;
    let rhs_is_nan = (rhs_raw & T::NAN_MASK) == T::NAN_MASK;
    let lhs_is_infinite = (lhs_raw & T::NAN_MASK) == T::INFINITY_MASK;
    let rhs_is_infinite = (rhs_raw & T::NAN_MASK) == T::INFINITY_MASK;
    let lhs_sign = (lhs_raw & T::SIGN_MASK) != T::zero();
    let rhs_sign = (rhs_raw & T::SIGN_MASK) != T::zero();
    if lhs_is_nan {
        return normalize_nan(lhs_raw);
    } else if rhs_is_nan {
        return normalize_nan(rhs_raw);
    } else if lhs_is_infinite && rhs_is_infinite && lhs_sign != rhs_sign {
        // Opposite signed infinity
        return T::NAN_MASK;
    } else if lhs_is_infinite {
        return infinity(lhs_sign);
    } else if rhs_is_infinite {
        return infinity(rhs_sign);
    }

    // Now we can unpack numbers as they are not NaN or Infinite
    let mut lhs = Unpacked::new(lhs_raw);
    let mut rhs = Unpacked::new(rhs_raw);

    // Handle zeroes
    if lhs.coefficient == T::zero() && rhs.coefficient == T::zero() {
        // Pick the zero with smallest exponent
        return min_zero(lhs, rhs, rounding).pack();
    } else if lhs.coefficient == T::zero() {
        if lhs.exponent >= rhs.exponent {
            return rhs_raw;
        }
        // Need to rescale lhs to lhs exponent (or as much as we can without losing digits)
        rhs.increase_precision(lhs.exponent);
        return rhs.pack();
    } else if rhs.coefficient == T::zero() {
        if rhs.exponent >= lhs.exponent {
            return lhs_raw;
        }
        // Need to rescale lhs to lhs exponent (or as much as we can without losing digits)
        lhs.increase_precision(rhs.exponent);
        return lhs.pack();
    }

    // Done with handling zeros

    // make `a` to be the number with bigger exponent
    let (mut a, mut b) = if lhs.exponent < rhs.exponent {
        (rhs, lhs)
    } else {
        (lhs, rhs)
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

    let different_sign = lhs.sign != rhs.sign;
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
    a.fit_coefficient(rounding);

    if a.exponent > T::EXPONENT_MAX {
        // Round to infinity, exponent is too large
        // Note that we only add to exponent when our value doesn't fit into coefficient (otherwise
        // we could have pushed some of the exponent into the coefficient).
        rounded_infinity(a.sign, rounding)
    } else {
        a.pack()
    }
}

pub fn mul<T: DecimalStorage>(lhs_raw: T, rhs_raw: T, rounding: Rounding) -> T where {
    let lhs_is_nan = (lhs_raw & T::NAN_MASK) == T::NAN_MASK;
    let rhs_is_nan = (rhs_raw & T::NAN_MASK) == T::NAN_MASK;
    let lhs_is_infinite = (lhs_raw & T::NAN_MASK) == T::INFINITY_MASK;
    let rhs_is_infinite = (rhs_raw & T::NAN_MASK) == T::INFINITY_MASK;
    let lhs_sign = (lhs_raw & T::SIGN_MASK) != T::zero();
    let rhs_sign = (rhs_raw & T::SIGN_MASK) != T::zero();
    if lhs_is_nan {
        return normalize_nan(lhs_raw);
    } else if rhs_is_nan {
        return normalize_nan(rhs_raw);
    } else if lhs_is_infinite || rhs_is_infinite {
        let lhs_is_zero = !lhs_is_infinite && Unpacked::new(lhs_raw).coefficient == T::zero();
        let rhs_is_zero = !rhs_is_infinite && Unpacked::new(rhs_raw).coefficient == T::zero();
        if lhs_is_zero || rhs_is_zero {
            return T::NAN_MASK;
        } else {
            return infinity(lhs_sign != rhs_sign);
        }
    }

    let lhs = Unpacked::new(lhs_raw);
    let rhs = Unpacked::new(rhs_raw);

    if lhs.coefficient == T::zero() || rhs.coefficient == T::zero() {
        let exp = (lhs.exponent + rhs.exponent).max(T::BIAS);
        let result = Unpacked {
            coefficient: T::zero(),
            exponent: (exp - T::BIAS).min(T::EXPONENT_MAX),
            sign: lhs.sign != rhs.sign,
        };
        return result.pack();
    }

    let mut wide = Unpacked {
        coefficient: lhs.coefficient.wide_mul(rhs.coefficient),
        // Note: will subtract bias later
        exponent: lhs.exponent + rhs.exponent,
        sign: lhs.sign != rhs.sign,
    };

    let mut to_round = 0;

    // Round enough digits that the result fits into exponent (if exponent is too small)
    if wide.exponent < T::BIAS {
        to_round = T::BIAS - wide.exponent;
    }

    // Round enough digits that the coefficient fits into our smaller size
    let digits = n_digits(wide.coefficient);
    if digits > T::COEFFICIENT_SIZE {
        to_round = to_round.max(digits - T::COEFFICIENT_SIZE);
    }
    let rounding_for_exponent = wide.exponent < T::BIAS;
    wide.apply_rounding(to_round, rounding);
    wide.exponent -= T::BIAS;

    // We rounded because exponent was too small. However, after rounding we gained one extra digit.
    // Put this digit back into the exponent.
    if rounding_for_exponent && wide.exponent == 1 {
        wide.coefficient = wide.coefficient * T::Wide::TEN;
        wide.exponent -= 1;
    }

    let (hi, lo) = T::split(wide.coefficient);
    debug_assert_eq!(hi, T::zero());
    let result = Unpacked {
        coefficient: lo,
        exponent: wide.exponent,
        sign: wide.sign,
    };
    if result.exponent > T::EXPONENT_MAX {
        // Round to infinity, exponent is too large
        // Note that we only add to exponent when our value doesn't fit into coefficient (otherwise
        // we could have pushed some of the exponent into the coefficient).
        rounded_infinity(result.sign, rounding)
    } else {
        result.pack()
    }
}
