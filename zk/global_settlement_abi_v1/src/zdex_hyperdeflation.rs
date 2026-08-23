//! Deterministic ZDEX burn and denomination-rescale transitions.
//!
//! These functions establish only the supplied state transition. Receipt,
//! release-profile, complete-bucket, and publication authority belong to
//! separate verifier and settlement layers.

use crate::canonical::{AbiErrorV1, AbiResultV1};
use crate::zdex_hyperdeflation_results::{
    ZDEXPrecisionRescaleAcceptedV1, ZDEXPrecisionRescaleRejectedV1, ZDEXPrecisionRescaleResultV1,
    ZDEXPurchaseAndBurnAcceptedV1, ZDEXPurchaseAndBurnRejectedV1, ZDEXPurchaseAndBurnResultV1,
};
use crate::zdex_hyperdeflation_types::{
    ZDEXAmountBucketV1, ZDEXBucketScaleV1, ZDEXBurnCapacityV1, ZDEXBurnEffectV1,
    ZDEXBurnRejectCodeV1, ZDEXBurnRouteContextV1, ZDEXHyperdeflationPolicyV1,
    ZDEXPrecisionEffectV1, ZDEXPrecisionRejectCodeV1, ZDEXPrecisionRescaleCommandV1,
    ZDEXPurchaseAndBurnCommandV1, ZDEXSupplyStateV1, MAX_DECIMAL_SCALE_STEP_V1,
};

pub fn retained_supply_atoms_v1(
    live_supply_atoms: u128,
    policy: &ZDEXHyperdeflationPolicyV1,
) -> AbiResultV1<u128> {
    policy.validate()?;
    if live_supply_atoms == 0 {
        return Err(AbiErrorV1::InvalidBounds("ZDEX retained supply input"));
    }
    let numerator = u128::from(policy.retained_numerator);
    let denominator = u128::from(policy.retained_denominator);
    let quotient = live_supply_atoms / denominator;
    let remainder = live_supply_atoms % denominator;
    let quotient_part = quotient
        .checked_mul(numerator)
        .ok_or(AbiErrorV1::InvalidBounds("ZDEX retained quotient"))?;
    let remainder_product = remainder
        .checked_mul(numerator)
        .ok_or(AbiErrorV1::InvalidBounds("ZDEX retained remainder"))?;
    let rounded_remainder = if remainder_product == 0 {
        0
    } else {
        (remainder_product
            .checked_sub(1)
            .ok_or(AbiErrorV1::InvalidBounds("ZDEX retained remainder"))?
            / denominator)
            .checked_add(1)
            .ok_or(AbiErrorV1::InvalidBounds("ZDEX retained remainder"))?
    };
    let retained = quotient_part
        .checked_add(rounded_remainder)
        .ok_or(AbiErrorV1::InvalidBounds("ZDEX retained supply"))?;
    if retained == 0 || retained > live_supply_atoms {
        return Err(AbiErrorV1::InvalidBounds("ZDEX retained supply"));
    }
    Ok(retained)
}

pub fn compute_zdex_burn_capacity_v1(
    policy: &ZDEXHyperdeflationPolicyV1,
    state: &ZDEXSupplyStateV1,
    context: &ZDEXBurnRouteContextV1,
    source_bucket_id: &str,
) -> AbiResultV1<Option<ZDEXBurnCapacityV1>> {
    policy.validate()?;
    state.validate()?;
    context.validate()?;
    let Some(source_atoms) = state.bucket_atoms(source_bucket_id)? else {
        return Ok(None);
    };
    let retained_supply_atoms = retained_supply_atoms_v1(state.live_supply_atoms, policy)?;
    let capacity = ZDEXBurnCapacityV1 {
        retained_supply_atoms,
        ratio_headroom_atoms: state
            .live_supply_atoms
            .checked_sub(retained_supply_atoms)
            .ok_or(AbiErrorV1::InvalidBounds("ZDEX ratio headroom"))?,
        source_headroom_atoms: source_atoms.saturating_sub(context.source_reserve_floor_atoms),
        epoch_headroom_atoms: state
            .remaining_epoch_burn_cap_atoms
            .min(context.remaining_epoch_burn_cap_atoms),
        route_headroom_atoms: context.route_safe_output_cap_atoms,
        maximum_burn_atoms: 0,
    };
    let capacity = ZDEXBurnCapacityV1 {
        maximum_burn_atoms: capacity
            .ratio_headroom_atoms
            .min(capacity.source_headroom_atoms)
            .min(capacity.epoch_headroom_atoms)
            .min(capacity.route_headroom_atoms),
        ..capacity
    };
    capacity.validate()?;
    Ok(Some(capacity))
}

pub fn transition_zdex_purchase_and_burn_v1(
    policy: &ZDEXHyperdeflationPolicyV1,
    state: &ZDEXSupplyStateV1,
    context: &ZDEXBurnRouteContextV1,
    command: &ZDEXPurchaseAndBurnCommandV1,
) -> AbiResultV1<ZDEXPurchaseAndBurnResultV1> {
    policy.validate()?;
    state.validate()?;
    context.validate()?;
    command.validate()?;
    if policy.asset_id != state.asset_id
        || policy.policy_root()? != state.policy_root
        || context.policy_root != policy.policy_root()?
    {
        return burn_reject_v1(ZDEXBurnRejectCodeV1::POLICY_MISMATCH, state);
    }
    if state.decimals > policy.maximum_decimals {
        return burn_reject_v1(ZDEXBurnRejectCodeV1::STATE_OUTSIDE_POLICY, state);
    }
    if command.expected_pre_state_root != state.state_root()? {
        return burn_reject_v1(ZDEXBurnRejectCodeV1::STALE_STATE, state);
    }
    if command.expected_precision_epoch != state.precision_epoch {
        return burn_reject_v1(ZDEXBurnRejectCodeV1::PRECISION_EPOCH_MISMATCH, state);
    }
    if context.burn_budget_epoch != state.burn_budget_epoch {
        return burn_reject_v1(ZDEXBurnRejectCodeV1::BURN_BUDGET_EPOCH_MISMATCH, state);
    }
    if command.purchased_zdex_atoms == 0 {
        return burn_reject_v1(ZDEXBurnRejectCodeV1::ZERO_PURCHASE, state);
    }
    if command.purchased_zdex_atoms > i128::MAX.unsigned_abs() {
        return burn_reject_v1(ZDEXBurnRejectCodeV1::EFFECT_WIDTH_EXCEEDED, state);
    }
    if command.expected_purchase_occurrence_root != context.purchase_occurrence_root
        || command.source_bucket_id != context.burn_source_bucket_id
        || command.purchased_zdex_atoms != context.purchased_zdex_atoms
    {
        return burn_reject_v1(ZDEXBurnRejectCodeV1::PURCHASE_BINDING_MISMATCH, state);
    }
    let Some(capacity) =
        compute_zdex_burn_capacity_v1(policy, state, context, &command.source_bucket_id)?
    else {
        return burn_reject_v1(ZDEXBurnRejectCodeV1::SOURCE_BUCKET_UNKNOWN, state);
    };
    if let Some(code) = exhausted_burn_code_v1(&capacity) {
        return burn_reject_v1(code, state);
    }
    if command.purchased_zdex_atoms > capacity.maximum_burn_atoms {
        return burn_reject_v1(ZDEXBurnRejectCodeV1::PURCHASE_EXCEEDS_BURN_CAPACITY, state);
    }
    apply_burn_v1(policy, state, context, command, capacity)
}

fn apply_burn_v1(
    policy: &ZDEXHyperdeflationPolicyV1,
    state: &ZDEXSupplyStateV1,
    context: &ZDEXBurnRouteContextV1,
    command: &ZDEXPurchaseAndBurnCommandV1,
    capacity: ZDEXBurnCapacityV1,
) -> AbiResultV1<ZDEXPurchaseAndBurnResultV1> {
    let burn_atoms = command.purchased_zdex_atoms;
    let post_state = ZDEXSupplyStateV1 {
        asset_id: state.asset_id.clone(),
        policy_root: state.policy_root.clone(),
        decimals: state.decimals,
        precision_epoch: state.precision_epoch,
        live_supply_atoms: state
            .live_supply_atoms
            .checked_sub(burn_atoms)
            .ok_or(AbiErrorV1::Conservation("ZDEX burn supply"))?,
        buckets: burned_bucket_projection_v1(state, &command.source_bucket_id, burn_atoms)?,
        burn_budget_epoch: state.burn_budget_epoch,
        remaining_epoch_burn_cap_atoms: state
            .remaining_epoch_burn_cap_atoms
            .checked_sub(burn_atoms)
            .ok_or(AbiErrorV1::Conservation("ZDEX epoch burn capacity"))?,
    };
    let accepted = ZDEXPurchaseAndBurnAcceptedV1 {
        policy: policy.clone(),
        route_context: context.clone(),
        pre_state: state.clone(),
        post_state,
        capacity,
        effect: ZDEXBurnEffectV1 {
            purchase_occurrence_root: context.purchase_occurrence_root.clone(),
            source_bucket_id: command.source_bucket_id.clone(),
            source_debit_atoms: burn_atoms,
            authorized_burn_atoms: burn_atoms,
            authorized_issue_atoms: 0,
        },
    };
    accepted.validate()?;
    Ok(ZDEXPurchaseAndBurnResultV1::Accepted(Box::new(accepted)))
}

pub(crate) fn burned_bucket_projection_v1(
    state: &ZDEXSupplyStateV1,
    source_bucket_id: &str,
    burn_atoms: u128,
) -> AbiResultV1<Vec<ZDEXAmountBucketV1>> {
    let Some(source_atoms) = state.bucket_atoms(source_bucket_id)? else {
        return Err(AbiErrorV1::InvalidBinding("ZDEX burn source bucket"));
    };
    if burn_atoms == 0 || burn_atoms > source_atoms {
        return Err(AbiErrorV1::InvalidBounds("ZDEX burn source debit"));
    }
    let remaining_atoms = source_atoms
        .checked_sub(burn_atoms)
        .ok_or(AbiErrorV1::InvalidBounds("ZDEX burn source debit"))?;
    Ok(state
        .buckets
        .iter()
        .filter_map(|bucket| {
            if bucket.bucket_id != source_bucket_id {
                Some(bucket.clone())
            } else if remaining_atoms > 0 {
                Some(ZDEXAmountBucketV1 {
                    bucket_id: bucket.bucket_id.clone(),
                    amount_atoms: remaining_atoms,
                })
            } else {
                None
            }
        })
        .collect())
}

fn exhausted_burn_code_v1(capacity: &ZDEXBurnCapacityV1) -> Option<ZDEXBurnRejectCodeV1> {
    if capacity.ratio_headroom_atoms == 0 {
        Some(ZDEXBurnRejectCodeV1::PRECISION_RESCALE_REQUIRED)
    } else if capacity.source_headroom_atoms == 0 {
        Some(ZDEXBurnRejectCodeV1::SOURCE_RESERVE_FLOOR_REACHED)
    } else if capacity.epoch_headroom_atoms == 0 {
        Some(ZDEXBurnRejectCodeV1::EPOCH_BURN_CAP_REACHED)
    } else if capacity.route_headroom_atoms == 0 {
        Some(ZDEXBurnRejectCodeV1::ROUTE_OUTPUT_CAP_ZERO)
    } else {
        None
    }
}

fn burn_reject_v1(
    code: ZDEXBurnRejectCodeV1,
    state: &ZDEXSupplyStateV1,
) -> AbiResultV1<ZDEXPurchaseAndBurnResultV1> {
    let rejected = ZDEXPurchaseAndBurnRejectedV1 {
        code,
        pre_state: state.clone(),
        post_state: state.clone(),
        effects: vec![],
    };
    rejected.validate()?;
    Ok(ZDEXPurchaseAndBurnResultV1::Rejected(Box::new(rejected)))
}

pub fn transition_zdex_precision_rescale_v1(
    policy: &ZDEXHyperdeflationPolicyV1,
    state: &ZDEXSupplyStateV1,
    command: &ZDEXPrecisionRescaleCommandV1,
) -> AbiResultV1<ZDEXPrecisionRescaleResultV1> {
    policy.validate()?;
    state.validate()?;
    command.validate()?;
    if policy.asset_id != state.asset_id || policy.policy_root()? != state.policy_root {
        return precision_reject_v1(ZDEXPrecisionRejectCodeV1::POLICY_MISMATCH, state);
    }
    if command.expected_pre_state_root != state.state_root()? {
        return precision_reject_v1(ZDEXPrecisionRejectCodeV1::STALE_STATE, state);
    }
    if command.expected_precision_epoch != state.precision_epoch {
        return precision_reject_v1(ZDEXPrecisionRejectCodeV1::PRECISION_EPOCH_MISMATCH, state);
    }
    if command.additional_decimals == 0 {
        return precision_reject_v1(ZDEXPrecisionRejectCodeV1::ZERO_DECIMAL_STEP, state);
    }
    if command.additional_decimals > policy.maximum_decimal_step
        || command.additional_decimals > MAX_DECIMAL_SCALE_STEP_V1
    {
        return precision_reject_v1(
            ZDEXPrecisionRejectCodeV1::DECIMAL_STEP_EXCEEDS_POLICY,
            state,
        );
    }
    let Some(next_decimals) = state.decimals.checked_add(command.additional_decimals) else {
        return precision_reject_v1(ZDEXPrecisionRejectCodeV1::MAXIMUM_DECIMALS_EXCEEDED, state);
    };
    if next_decimals > policy.maximum_decimals {
        return precision_reject_v1(ZDEXPrecisionRejectCodeV1::MAXIMUM_DECIMALS_EXCEEDED, state);
    }
    if state.precision_epoch == u64::MAX {
        return precision_reject_v1(ZDEXPrecisionRejectCodeV1::EPOCH_COUNTER_EXHAUSTED, state);
    }
    let scale_exponent = u32::try_from(command.additional_decimals)
        .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX decimal scale exponent"))?;
    let scale_factor = 10_u128
        .checked_pow(scale_exponent)
        .ok_or(AbiErrorV1::InvalidBounds("ZDEX decimal scale factor"))?;
    if state.live_supply_atoms.checked_mul(scale_factor).is_none()
        || state
            .remaining_epoch_burn_cap_atoms
            .checked_mul(scale_factor)
            .is_none()
        || state
            .buckets
            .iter()
            .any(|bucket| bucket.amount_atoms.checked_mul(scale_factor).is_none())
    {
        return precision_reject_v1(ZDEXPrecisionRejectCodeV1::ATOM_OVERFLOW, state);
    }
    apply_precision_rescale_v1(policy, state, next_decimals, scale_factor)
}

fn apply_precision_rescale_v1(
    policy: &ZDEXHyperdeflationPolicyV1,
    state: &ZDEXSupplyStateV1,
    next_decimals: u64,
    scale_factor: u128,
) -> AbiResultV1<ZDEXPrecisionRescaleResultV1> {
    let bucket_scales = state
        .buckets
        .iter()
        .map(|bucket| {
            Ok(ZDEXBucketScaleV1 {
                bucket_id: bucket.bucket_id.clone(),
                before_atoms: bucket.amount_atoms,
                after_atoms: bucket
                    .amount_atoms
                    .checked_mul(scale_factor)
                    .ok_or(AbiErrorV1::InvalidBounds("ZDEX precision bucket"))?,
            })
        })
        .collect::<AbiResultV1<Vec<_>>>()?;
    let supply_after_atoms = state
        .live_supply_atoms
        .checked_mul(scale_factor)
        .ok_or(AbiErrorV1::InvalidBounds("ZDEX precision supply"))?;
    let post_state = ZDEXSupplyStateV1 {
        asset_id: state.asset_id.clone(),
        policy_root: state.policy_root.clone(),
        decimals: next_decimals,
        precision_epoch: state
            .precision_epoch
            .checked_add(1)
            .ok_or(AbiErrorV1::InvalidBounds("ZDEX precision epoch"))?,
        live_supply_atoms: supply_after_atoms,
        buckets: bucket_scales
            .iter()
            .map(|row| ZDEXAmountBucketV1 {
                bucket_id: row.bucket_id.clone(),
                amount_atoms: row.after_atoms,
            })
            .collect(),
        burn_budget_epoch: state.burn_budget_epoch,
        remaining_epoch_burn_cap_atoms: state
            .remaining_epoch_burn_cap_atoms
            .checked_mul(scale_factor)
            .ok_or(AbiErrorV1::InvalidBounds("ZDEX precision burn budget"))?,
    };
    let burn_budget_remaining_after_atoms = post_state.remaining_epoch_burn_cap_atoms;
    let accepted = ZDEXPrecisionRescaleAcceptedV1 {
        policy: policy.clone(),
        pre_state: state.clone(),
        post_state,
        effect: ZDEXPrecisionEffectV1 {
            scale_factor,
            supply_before_atoms: state.live_supply_atoms,
            supply_after_atoms,
            bucket_scales,
            authorized_issue_atoms: 0,
            authorized_burn_atoms: 0,
            burn_budget_remaining_before_atoms: state.remaining_epoch_burn_cap_atoms,
            burn_budget_remaining_after_atoms,
        },
    };
    accepted.validate()?;
    Ok(ZDEXPrecisionRescaleResultV1::Accepted(Box::new(accepted)))
}

fn precision_reject_v1(
    code: ZDEXPrecisionRejectCodeV1,
    state: &ZDEXSupplyStateV1,
) -> AbiResultV1<ZDEXPrecisionRescaleResultV1> {
    let rejected = ZDEXPrecisionRescaleRejectedV1 {
        code,
        pre_state: state.clone(),
        post_state: state.clone(),
        effects: vec![],
    };
    rejected.validate()?;
    Ok(ZDEXPrecisionRescaleResultV1::Rejected(Box::new(rejected)))
}
