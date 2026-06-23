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
    let q = numerator.checked_div(denominator)?;
    let r = numerator.checked_rem(denominator)?;
    if r != 0 && ((r < 0) != (denominator < 0)) {
        q.checked_sub(1)
    } else {
        Some(q)
    }
}

#[cfg(kani)]
mod kani_contracts {
    use super::*;

    /// TOTALITY (D-1, proved over the full i128 x i128 domain): `floor_div_i128`
    /// never panics, overflows, or traps for any `(numerator, denominator)`.
    /// `checked_div` and `checked_rem` turn the `i128::MIN / -1` and
    /// divide-by-zero cases into `None` before Rust can trap. This is the
    /// no-panic-on-consensus-path CBC contract as a machine proof.
    #[kani::proof]
    fn floor_div_i128_is_total() {
        let n: i128 = kani::any();
        let d: i128 = kani::any();
        let _ = floor_div_i128(n, d);
        // The corner that motivated the guard, and the div-by-zero guard.
        assert_eq!(floor_div_i128(i128::MIN, -1), None);
        assert_eq!(floor_div_i128(n, 0), None);
    }

    // NOTE on floor *correctness* (vs the totality proof above): asserting the
    // floor relationship `n == q*d + r, sign(r)==sign(d), |r|<|d|` requires relating
    // a SYMBOLIC 128-bit quotient back to the dividend via multiplication. That is
    // intractable for Kani's bit-blasting SAT backend even for concrete divisors
    // (the quotient stays a symbolic 128-bit value), so it is NOT machine-proved
    // here. The floor semantics (incl. negative operands and the MIN/-1 edge) are
    // covered by the unit tests in `mod tests`; Kani contributes the property unit
    // tests cannot: TOTALITY over the entire i128 x i128 domain.

    /// TOTALITY: `mul_div_floor` never panics for any inputs. The `denominator
    /// == 0` guard and `checked_mul` make overflow/div-by-zero typed rejects.
    #[kani::proof]
    fn mul_div_floor_is_total() {
        let _ = mul_div_floor(kani::any(), kani::any(), kani::any());
    }

    /// TOTALITY + EXACTNESS: `checked_add` is total and returns `Ok` iff the native
    /// checked op is `Some` (fail-closed on overflow, never wrap/panic). (Only the
    /// addition is asserted symbolically; `checked_mul`'s 128-bit multiply is left
    /// to `mul_div_floor_is_total` totality + unit tests, as symbolic 128-bit
    /// multiplication is not tractable for the bit-blasting SAT backend.)
    #[kani::proof]
    fn checked_add_total_and_exact() {
        let a: u128 = kani::any();
        let b: u128 = kani::any();
        assert_eq!(checked_add(a, b).ok(), a.checked_add(b));
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
        assert_eq!(floor_div_i128(i128::MIN, -1), None);
    }
}
