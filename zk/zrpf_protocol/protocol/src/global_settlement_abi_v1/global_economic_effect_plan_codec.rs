use alloc::vec::Vec;

use super::{
    GlobalEconomicEffectPlanErrorV1, GlobalEconomicEffectPlanV1,
    MAX_GLOBAL_ECONOMIC_EFFECT_PLAN_BYTES_V1,
};

pub fn encode_global_economic_effect_plan_v1(
    plan: &GlobalEconomicEffectPlanV1,
) -> Result<Vec<u8>, GlobalEconomicEffectPlanErrorV1> {
    plan.validate_self_consistency()?;
    let bytes =
        postcard::to_allocvec(plan).map_err(|_| GlobalEconomicEffectPlanErrorV1::PostcardDecode)?;
    require_bounded(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_global_economic_effect_plan_v1(
    bytes: &[u8],
) -> Result<GlobalEconomicEffectPlanV1, GlobalEconomicEffectPlanErrorV1> {
    require_bounded(bytes.len())?;
    let (plan, remainder) = postcard::take_from_bytes::<GlobalEconomicEffectPlanV1>(bytes)
        .map_err(|_| GlobalEconomicEffectPlanErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(GlobalEconomicEffectPlanErrorV1::TrailingBytes);
    }
    if encode_global_economic_effect_plan_v1(&plan)?.as_slice() != bytes {
        return Err(GlobalEconomicEffectPlanErrorV1::NonCanonicalEncoding);
    }
    Ok(plan)
}

fn require_bounded(size: usize) -> Result<(), GlobalEconomicEffectPlanErrorV1> {
    if size == 0 {
        return Err(GlobalEconomicEffectPlanErrorV1::EmptyInput);
    }
    if size > MAX_GLOBAL_ECONOMIC_EFFECT_PLAN_BYTES_V1 {
        return Err(GlobalEconomicEffectPlanErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_GLOBAL_ECONOMIC_EFFECT_PLAN_BYTES_V1,
        });
    }
    Ok(())
}
