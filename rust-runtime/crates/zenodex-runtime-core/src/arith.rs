//! Explicit checked arithmetic helpers.
//!
//! Every arithmetic operation in a transition path goes through one of these so
//! overflow becomes a typed [`RejectedReason::ArithmeticOverflow`] rather than a
//! panic or a silent wrap.

use crate::error::RejectedReason;

/// Checked addition; maps overflow to [`RejectedReason::ArithmeticOverflow`].
#[inline]
pub fn checked_add(a: u128, b: u128) -> Result<u128, RejectedReason> {
    a.checked_add(b).ok_or(RejectedReason::ArithmeticOverflow)
}

/// Checked multiplication; maps overflow to [`RejectedReason::ArithmeticOverflow`].
#[inline]
pub fn checked_mul(a: u128, b: u128) -> Result<u128, RejectedReason> {
    a.checked_mul(b).ok_or(RejectedReason::ArithmeticOverflow)
}

/// `floor(value * numerator / denominator)` with a checked multiply.
///
/// `denominator` must be non-zero (it is a compile-time constant at every call
/// site); a zero denominator is reported as an overflow rather than panicking.
#[inline]
pub fn mul_div_floor(
    value: u128,
    numerator: u128,
    denominator: u128,
) -> Result<u128, RejectedReason> {
    if denominator == 0 {
        return Err(RejectedReason::ArithmeticOverflow);
    }
    Ok(checked_mul(value, numerator)? / denominator)
}

/// Python-compatible floor division for signed integers.
///
/// Rust's `/` truncates toward zero. Python's `//` floors toward negative
/// infinity, so negative, non-even divisions need one extra step down.
#[inline]
pub fn floor_div_i128(numerator: i128, denominator: i128) -> Option<i128> {
    if denominator == 0 {
        return None;
    }
    let q = numerator / denominator;
    let r = numerator % denominator;
    if r != 0 && ((r < 0) != (denominator < 0)) {
        q.checked_sub(1)
    } else {
        Some(q)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_and_mul_ok() {
        assert_eq!(checked_add(2, 3).unwrap(), 5);
        assert_eq!(checked_mul(4, 5).unwrap(), 20);
    }

    #[test]
    fn add_overflow_is_rejected() {
        assert_eq!(
            checked_add(u128::MAX, 1),
            Err(RejectedReason::ArithmeticOverflow)
        );
    }

    #[test]
    fn mul_overflow_is_rejected() {
        assert_eq!(
            checked_mul(u128::MAX, 2),
            Err(RejectedReason::ArithmeticOverflow)
        );
    }

    #[test]
    fn mul_div_floor_truncates() {
        assert_eq!(mul_div_floor(12_347, 6_000, 10_000).unwrap(), 7_408);
        assert_eq!(mul_div_floor(0, 6_000, 10_000).unwrap(), 0);
        assert_eq!(
            mul_div_floor(10, 10_000, 0),
            Err(RejectedReason::ArithmeticOverflow)
        );
    }

    #[test]
    fn floor_div_i128_matches_python_rounding() {
        assert_eq!(floor_div_i128(7, 3), Some(2));
        assert_eq!(floor_div_i128(-7, 3), Some(-3));
        assert_eq!(floor_div_i128(7, -3), Some(-3));
        assert_eq!(floor_div_i128(-7, -3), Some(2));
        assert_eq!(floor_div_i128(-6, 3), Some(-2));
        assert_eq!(floor_div_i128(1, 0), None);
    }
}
