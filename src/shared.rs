use crate::{Rounding, Unpacked};

/// Take the zero with the smallest exponent (most "precise" zero). Take the sign depending on rounding.
pub(crate) fn min_zero<T>(lhs: Unpacked<T>, rhs: Unpacked<T>, rounding: Rounding) -> Unpacked<T> {
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
