#![forbid(unsafe_code)]

//! Heap-free arithmetic refinement for FCIS M6 B08.
//!
//! The production candidate stores amounts as `BigUint` values admitted by
//! `AmountU256`, with `0 <= amount < 2^256`. This crate deliberately models a
//! strict refinement subset: Kani explores `u16` amounts and weights while
//! checked `u32` intermediates carry every product. The embedding is
//! `x: u16 -> BigUint::from(x)`, so every accepted model value is an admitted
//! production amount. Full mathematical U256 obligations are checked by the
//! companion SMT-LIB model.

pub const DENOMINATOR: u32 = 10_000;
pub const FIXED_WEIGHTS: [u16; 3] = [3_333, 3_333, 3_334];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Quota {
    pub base: u32,
    pub fraction: u32,
    pub quotient_product: u32,
    pub residual_product: u32,
}

/// Compute one Euclidean quota using checked machine intermediates.
pub fn quota_for(amount: u16, weight: u16) -> Option<Quota> {
    let weight_value = u32::from(weight);
    if weight_value > DENOMINATOR {
        return None;
    }
    let amount_value = u32::from(amount);
    let quotient = amount_value / DENOMINATOR;
    let residual = amount_value % DENOMINATOR;
    let quotient_product = quotient.checked_mul(weight_value)?;
    let residual_product = residual.checked_mul(weight_value)?;
    let base = quotient_product.checked_add(residual_product / DENOMINATOR)?;
    let residual_bound = DENOMINATOR.checked_mul(DENOMINATOR)?;
    if residual_product >= residual_bound || base > amount_value {
        return None;
    }
    let fraction = residual_product % DENOMINATOR;
    Some(Quota {
        base,
        fraction,
        quotient_product,
        residual_product,
    })
}

/// Validate the fixed three-role local relation and return its amounts.
pub fn fixed_allocation(amount: u16, bonuses: [u8; 3]) -> Option<[u32; 3]> {
    let quotas = [
        quota_for(amount, FIXED_WEIGHTS[0])?,
        quota_for(amount, FIXED_WEIGHTS[1])?,
        quota_for(amount, FIXED_WEIGHTS[2])?,
    ];
    let fractions = [quotas[0].fraction, quotas[1].fraction, quotas[2].fraction];
    let fraction_sum = fractions
        .iter()
        .try_fold(0_u32, |sum, fraction| sum.checked_add(*fraction))?;
    if fraction_sum % DENOMINATOR != 0 {
        return None;
    }
    let seats = fraction_sum / DENOMINATOR;
    if seats > 2 {
        return None;
    }
    let mut selected = 0_u32;
    for index in 0..3 {
        if bonuses[index] > 1 || (bonuses[index] == 1 && fractions[index] == 0) {
            return None;
        }
        selected = selected.checked_add(u32::from(bonuses[index]))?;
    }
    if selected != seats {
        return None;
    }
    let amounts = [
        quotas[0].base.checked_add(u32::from(bonuses[0]))?,
        quotas[1].base.checked_add(u32::from(bonuses[1]))?,
        quotas[2].base.checked_add(u32::from(bonuses[2]))?,
    ];
    let total = amounts
        .iter()
        .try_fold(0_u32, |sum, value| sum.checked_add(*value))?;
    if total != u32::from(amount) {
        return None;
    }
    Some(amounts)
}

/// Compute a selector score after validating the production signed bounds.
pub fn selector_score(deficit: i32, fraction: u32) -> Option<i64> {
    let denominator = i32::try_from(DENOMINATOR).ok()?;
    if deficit <= -denominator || deficit >= denominator || fraction >= DENOMINATOR {
        return None;
    }
    i64::from(deficit).checked_add(i64::from(fraction))
}

#[cfg(kani)]
mod kani_contracts {
    use super::*;

    /// The model embeds into production U256 through `BigUint::from(amount)`.
    /// Kani proves the strict u16 refinement subset with checked u32 products.
    #[kani::proof]
    fn euclidean_machine_bounds_hold() {
        let quotient: u16 = kani::any();
        let residual: u16 = kani::any();
        let weight: u16 = kani::any();
        kani::assume(u32::from(quotient) <= u32::from(u16::MAX) / DENOMINATOR);
        kani::assume(u32::from(residual) < DENOMINATOR);
        kani::assume(u32::from(weight) <= DENOMINATOR);

        let quotient_value = u32::from(quotient);
        let residual_value = u32::from(residual);
        let weight_value = u32::from(weight);
        let amount = quotient_value * DENOMINATOR + residual_value;
        let quotient_product = quotient_value * weight_value;
        let residual_product = residual_value * weight_value;
        let base = quotient_product + residual_product / DENOMINATOR;
        assert!(quotient_product <= amount);
        assert!(residual_product < DENOMINATOR * DENOMINATOR);
        assert!(base <= amount);
    }

    #[kani::proof]
    fn valid_fixed_allocation_is_bounded() {
        let amount: u16 = kani::any();
        let bonuses: [u8; 3] = kani::any();
        if let Some(values) = fixed_allocation(amount, bonuses) {
            for value in values {
                assert!(value <= u32::from(amount));
            }
        }
    }

    #[kani::proof]
    fn selector_score_is_inside_admitted_range() {
        let deficit: i32 = kani::any();
        let fraction: u32 = kani::any();
        let denominator = DENOMINATOR as i32;
        kani::assume(deficit > -denominator);
        kani::assume(deficit < denominator);
        kani::assume(fraction < DENOMINATOR);
        let score = selector_score(deficit, fraction);
        assert!(score.is_some());
        if let Some(value) = score {
            assert!(value > -i64::from(DENOMINATOR));
            assert!(value < 2 * i64::from(DENOMINATOR));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn maximum_model_amount_has_checked_quota() {
        let quota = quota_for(u16::MAX, DENOMINATOR as u16).expect("valid full-weight quota");
        assert_eq!(quota.base, u32::from(u16::MAX));
        assert_eq!(quota.fraction, 0);
        assert_eq!(
            quota.quotient_product,
            u32::from(u16::MAX / DENOMINATOR as u16) * DENOMINATOR
        );
    }

    #[test]
    fn supported_bonus_preserves_allocation_bound() {
        let values = fixed_allocation(1, [0, 0, 1]).expect("one residual seat");
        assert_eq!(values, [0, 0, 1]);
    }

    #[test]
    fn unsupported_bonus_is_rejected() {
        assert!(fixed_allocation(1, [2, 0, 0]).is_none());
        assert!(fixed_allocation(1, [0, 0, 0]).is_none());
    }

    #[test]
    fn score_bounds_are_typed_and_closed() {
        assert_eq!(selector_score(-9_999, 9_999), Some(0));
        assert_eq!(selector_score(-10_000, 0), None);
        assert_eq!(selector_score(9_999, 10_000), None);
    }
}
