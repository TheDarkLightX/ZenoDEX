use std::collections::{BTreeMap, BTreeSet};

use crate::canonical::{AbiErrorV2, AbiResultV2};
use crate::effects::{EconomicEffectKindV2, GlobalEconomicEffectPlanV2, LaneIdV2};
use crate::global_refinement_checks::{effect_deltas_v2, AmountKeyV2};
use crate::global_state::GlobalEconomicStateV2;
use crate::lifecycle::{
    GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2, TerminalObligationStatusV2,
};
use crate::signed_atoms::checked_add_atoms_difference_v2;

fn terminal_liability_deltas_v2(
    plan: &GlobalTerminalObligationPlanV2,
) -> AbiResultV2<BTreeMap<AmountKeyV2, i128>> {
    let mut values = BTreeMap::<AmountKeyV2, i128>::new();
    for delta in &plan.deltas {
        let post = &delta.post_obligation;
        let key = (
            post.asset.clone(),
            post.claimant.clone(),
            post.liability_domain.clone(),
        );
        let pre_atoms = delta
            .pre_obligation
            .as_ref()
            .filter(|pre| pre.status == TerminalObligationStatusV2::OPEN)
            .map(|pre| pre.amount_atoms)
            .unwrap_or(0);
        let post_atoms = if post.status == TerminalObligationStatusV2::OPEN {
            post.amount_atoms
        } else {
            0
        };
        let value = checked_add_atoms_difference_v2(
            values.get(&key).copied().unwrap_or(0),
            post_atoms,
            pre_atoms,
            "global refinement terminal liability delta overflow",
        )?;
        values.insert(key, value);
    }
    values.retain(|_, value| *value != 0);
    Ok(values)
}

pub(crate) fn require_global_terminal_refinement_v2(
    pre_state: &GlobalEconomicStateV2,
    post_state: &GlobalEconomicStateV2,
    effect_plan: &GlobalEconomicEffectPlanV2,
    terminal_plan: &GlobalTerminalObligationPlanV2,
) -> AbiResultV2<()> {
    let mut expected = pre_state
        .terminal_obligations
        .iter()
        .map(|row| (row.obligation_id.clone(), row.clone()))
        .collect::<BTreeMap<_, _>>();
    let written_lanes = effect_plan
        .lane_writes
        .iter()
        .map(|row| row.lane_id)
        .collect::<BTreeSet<_>>();
    for delta in &terminal_plan.deltas {
        if expected.get(&delta.obligation_id) != delta.pre_obligation.as_ref() {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement terminal obligation pre-state mismatch",
            ));
        }
        if !written_lanes.contains(&delta.post_obligation.lane_id) {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement terminal obligation lacks its owning lane write",
            ));
        }
        expected.insert(delta.obligation_id.clone(), delta.post_obligation.clone());
    }
    if post_state.terminal_obligations != expected.into_values().collect::<Vec<_>>() {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement terminal obligation plan mismatch",
        ));
    }
    if terminal_liability_deltas_v2(terminal_plan)?
        != effect_deltas_v2(effect_plan, EconomicEffectKindV2::LIABILITY)
    {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement terminal obligation liability mismatch",
        ));
    }
    Ok(())
}

pub(crate) fn require_global_oracle_refinement_v2(
    pre_state: &GlobalEconomicStateV2,
    post_state: &GlobalEconomicStateV2,
    effect_plan: &GlobalEconomicEffectPlanV2,
    oracle_plan: &GlobalOracleOccurrencePlanV2,
) -> AbiResultV2<()> {
    if !oracle_plan.deltas.is_empty()
        && !effect_plan
            .lane_writes
            .iter()
            .any(|row| row.lane_id == LaneIdV2::ORACLE_MARKET)
    {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement Oracle lane write is missing",
        ));
    }
    let mut expected = pre_state
        .oracle_occurrences
        .iter()
        .map(|row| (row.oracle_id.clone(), row.clone()))
        .collect::<BTreeMap<_, _>>();
    for delta in &oracle_plan.deltas {
        if expected.get(&delta.oracle_id) != delta.pre_occurrence.as_ref() {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement Oracle occurrence pre-state mismatch",
            ));
        }
        expected.insert(delta.oracle_id.clone(), delta.post_occurrence.clone());
    }
    if post_state.oracle_occurrences != expected.into_values().collect::<Vec<_>>() {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement Oracle occurrence plan mismatch",
        ));
    }
    Ok(())
}
