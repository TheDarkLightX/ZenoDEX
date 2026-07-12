use alloc::vec::Vec;

use super::{SettlementEffectErrorV2, SettlementEffectPlanV2, MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2};

pub fn encode_settlement_effect_plan_v2(
    plan: &SettlementEffectPlanV2,
) -> Result<Vec<u8>, SettlementEffectErrorV2> {
    plan.validate_self_consistency()?;
    let bytes = postcard::to_allocvec(plan).map_err(|_| SettlementEffectErrorV2::PostcardDecode)?;
    require_size(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_settlement_effect_plan_v2(
    bytes: &[u8],
) -> Result<SettlementEffectPlanV2, SettlementEffectErrorV2> {
    require_size(bytes.len())?;
    let (plan, remainder) = postcard::take_from_bytes::<SettlementEffectPlanV2>(bytes)
        .map_err(|_| SettlementEffectErrorV2::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(SettlementEffectErrorV2::TrailingBytes);
    }
    if encode_settlement_effect_plan_v2(&plan)?.as_slice() != bytes {
        return Err(SettlementEffectErrorV2::NonCanonicalEncoding);
    }
    Ok(plan)
}

fn require_size(size: usize) -> Result<(), SettlementEffectErrorV2> {
    if size == 0 {
        return Err(SettlementEffectErrorV2::EmptyInput);
    }
    if size > MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2 {
        return Err(SettlementEffectErrorV2::InputTooLarge {
            actual: size,
            maximum: MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2,
        });
    }
    Ok(())
}
