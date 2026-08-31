use std::collections::BTreeMap;

use crate::canonical::{AbiErrorV2, AbiResultV2};
use crate::effects::{
    EconomicEffectKindV2, GlobalEconomicEffectPlanV2, FEE_RESIDUE_CONTROL_DOMAIN_V2,
    FEE_RESIDUE_PRINCIPAL_V2,
};

type AmountKeyV2 = (String, String, String);

fn state_bearing_effect_totals_v2(
    effect_plan: &GlobalEconomicEffectPlanV2,
) -> AbiResultV2<BTreeMap<AmountKeyV2, i128>> {
    let mut state_rows = BTreeMap::<AmountKeyV2, i128>::new();
    for row in &effect_plan.rows {
        if !matches!(
            row.kind,
            EconomicEffectKindV2::ACCOUNT_MOVEMENT
                | EconomicEffectKindV2::CUSTODY
                | EconomicEffectKindV2::RESERVE
        ) {
            continue;
        }
        let key = (
            row.asset.clone(),
            row.principal.clone(),
            row.custody_domain.clone(),
        );
        let total = state_rows
            .get(&key)
            .copied()
            .unwrap_or(0)
            .checked_add(row.delta_atoms)
            .ok_or(AbiErrorV2::InvalidBounds(
                "global refinement annotation mirror overflow",
            ))?;
        state_rows.insert(key, total);
    }
    Ok(state_rows)
}

fn require_effect_annotation_mirrors_v2(
    effect_plan: &GlobalEconomicEffectPlanV2,
    state_rows: &BTreeMap<AmountKeyV2, i128>,
) -> AbiResultV2<()> {
    for row in &effect_plan.rows {
        let key = (
            row.asset.clone(),
            row.principal.clone(),
            row.custody_domain.clone(),
        );
        if row.kind == EconomicEffectKindV2::FEE_ALLOCATION
            && (row.delta_atoms < 0 || state_rows.get(&key).copied().unwrap_or(0) < row.delta_atoms)
        {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement fee allocation is not mirrored",
            ));
        }
        if matches!(
            row.kind,
            EconomicEffectKindV2::REWARD | EconomicEffectKindV2::SLASH
        ) && state_rows.get(&key).copied() != Some(row.delta_atoms)
        {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement reward or slash lacks exact state-bearing mirror",
            ));
        }
    }
    Ok(())
}

fn require_fee_residue_v2(effect_plan: &GlobalEconomicEffectPlanV2) -> AbiResultV2<()> {
    if effect_plan
        .fee_conservation
        .iter()
        .any(|row| row.fee_charged_atoms == 0)
    {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement zero fee conservation row is noncanonical",
        ));
    }
    let residue_effects = effect_plan
        .rows
        .iter()
        .filter(|row| {
            row.kind == EconomicEffectKindV2::RESERVE
                && row.principal == FEE_RESIDUE_PRINCIPAL_V2
                && row.custody_domain == FEE_RESIDUE_CONTROL_DOMAIN_V2
                && row.delta_atoms > 0
        })
        .map(|row| {
            u128::try_from(row.delta_atoms)
                .map(|amount| (row.asset.as_str(), amount))
                .map_err(|_| AbiErrorV2::InvalidBounds("global refinement fee residue"))
        })
        .collect::<AbiResultV2<BTreeMap<_, _>>>()?;
    let expected_residue = effect_plan
        .fee_conservation
        .iter()
        .filter(|row| row.carried_residue_atoms > 0)
        .map(|row| (row.asset.as_str(), row.carried_residue_atoms))
        .collect::<BTreeMap<_, _>>();
    if residue_effects != expected_residue {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement fee residue state mapping mismatch",
        ));
    }
    Ok(())
}

pub(crate) fn require_global_annotation_mirrors_v2(
    effect_plan: &GlobalEconomicEffectPlanV2,
) -> AbiResultV2<()> {
    let state_rows = state_bearing_effect_totals_v2(effect_plan)?;
    require_effect_annotation_mirrors_v2(effect_plan, &state_rows)?;
    require_fee_residue_v2(effect_plan)
}
