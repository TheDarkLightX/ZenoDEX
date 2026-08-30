//! Exact refinement between full global states and canonical economic effects.
//!
//! This deterministic checker covers sparse amount tables, supply, lane roots,
//! replay insertion, one-step whole-epoch height progression, intra-epoch route
//! height preservation, and conservation rows. Unsupported state and effect
//! categories fail closed. The result verifies no receipt and grants no
//! publication authority.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::effects::{
    EconomicEffectKindV1, GlobalEconomicEffectPlanV1, FEE_RESIDUE_CONTROL_DOMAIN_V1,
    FEE_RESIDUE_PRINCIPAL_V1,
};
use crate::global_economic_replay_refinement::derive_replay_insertions_v1;
use crate::global_economic_state_delta::{
    derive_global_economic_state_delta_v1, supply_map_v1, DerivedGlobalEconomicStateDeltaV1,
};
use crate::proof::{EconomicCommandOccurrenceV1, RouteCompositionJournalV1};
use crate::state::GlobalEconomicStateV1;

pub const GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V1: &str =
    "zenodex/global-economic-state-effect-refinement/v1";

#[derive(Clone, Copy, Debug)]
pub struct GlobalEconomicStateEffectRefinementCandidateV1<'a> {
    pub pre_state: &'a GlobalEconomicStateV1,
    pub post_state: &'a GlobalEconomicStateV1,
    pub effect_plan: &'a GlobalEconomicEffectPlanV1,
    pub consumed_occurrences: &'a [EconomicCommandOccurrenceV1],
    pub route_journals: &'a [RouteCompositionJournalV1],
}

#[derive(Serialize)]
struct RefinementContentV1<'a> {
    schema: &'static str,
    pre_state_root: &'a RootV1,
    post_state_root: &'a RootV1,
    effect_plan_root: &'a RootV1,
    state_delta_root: &'a RootV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobalEconomicStateEffectRefinementV1 {
    pre_state_root: RootV1,
    post_state_root: RootV1,
    effect_plan_root: RootV1,
    state_delta_root: RootV1,
}

impl GlobalEconomicStateEffectRefinementV1 {
    pub fn pre_state_root(&self) -> &RootV1 {
        &self.pre_state_root
    }

    pub fn post_state_root(&self) -> &RootV1 {
        &self.post_state_root
    }

    pub fn effect_plan_root(&self) -> &RootV1 {
        &self.effect_plan_root
    }

    pub fn state_delta_root(&self) -> &RootV1 {
        &self.state_delta_root
    }

    pub fn refinement_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "global-economic-state-effect-refinement-v1",
            &RefinementContentV1 {
                schema: GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V1,
                pre_state_root: &self.pre_state_root,
                post_state_root: &self.post_state_root,
                effect_plan_root: &self.effect_plan_root,
                state_delta_root: &self.state_delta_root,
            },
        )
    }
}

fn require_fixed_context_v1(
    pre_state: &GlobalEconomicStateV1,
    post_state: &GlobalEconomicStateV1,
    expected_post_height: u64,
) -> AbiResultV1<()> {
    if pre_state.chain_id != post_state.chain_id
        || pre_state.deployment_root != post_state.deployment_root
        || pre_state.writer_epoch != post_state.writer_epoch
        || pre_state.profile_root != post_state.profile_root
        || pre_state.oracle_occurrences != post_state.oracle_occurrences
        || pre_state.terminal_obligations != post_state.terminal_obligations
        || pre_state.history_root != post_state.history_root
        || pre_state.outbox != post_state.outbox
    {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement unsupported global field changed",
        ));
    }
    if post_state.height != expected_post_height {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement state height progression",
        ));
    }
    Ok(())
}

fn require_nonzero_sparse_amounts_v1(state: &GlobalEconomicStateV1) -> AbiResultV1<()> {
    if state
        .balances
        .iter()
        .chain(&state.custody)
        .chain(&state.liabilities)
        .chain(&state.reserves)
        .any(|row| row.amount_atoms == 0)
    {
        return Err(AbiErrorV1::InvalidBounds(
            "economic refinement zero economic amount",
        ));
    }
    Ok(())
}

fn require_supported_effects_v1(effect_plan: &GlobalEconomicEffectPlanV1) -> AbiResultV1<()> {
    if !effect_plan.external_outbox_enqueue.is_empty() {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement external outbox unavailable",
        ));
    }
    if effect_plan.rows.iter().any(|row| {
        matches!(
            row.kind,
            EconomicEffectKindV1::REWARD | EconomicEffectKindV1::SLASH
        )
    }) {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement reward and slash unmapped",
        ));
    }
    Ok(())
}

fn require_fee_mirror_v1(effect_plan: &GlobalEconomicEffectPlanV1) -> AbiResultV1<()> {
    let mut state_rows = BTreeMap::<(&str, &str, &str), i128>::new();
    for row in &effect_plan.rows {
        if !matches!(
            row.kind,
            EconomicEffectKindV1::ACCOUNT_MOVEMENT
                | EconomicEffectKindV1::CUSTODY
                | EconomicEffectKindV1::RESERVE
        ) {
            continue;
        }
        let key = (
            row.principal.as_str(),
            row.asset.as_str(),
            row.custody_domain.as_str(),
        );
        let total = state_rows
            .get(&key)
            .copied()
            .unwrap_or(0)
            .checked_add(row.delta_atoms)
            .ok_or(AbiErrorV1::InvalidBounds(
                "economic refinement fee mirror aggregate",
            ))?;
        state_rows.insert(key, total);
    }
    for row in &effect_plan.rows {
        let key = (
            row.principal.as_str(),
            row.asset.as_str(),
            row.custody_domain.as_str(),
        );
        if row.kind == EconomicEffectKindV1::FEE_ALLOCATION
            && state_rows.get(&key).copied().unwrap_or(0) < row.delta_atoms
        {
            return Err(AbiErrorV1::InvalidBinding(
                "economic refinement fee allocation not mirrored",
            ));
        }
    }
    if effect_plan
        .fee_conservation
        .iter()
        .any(|row| row.fee_charged_atoms == 0)
    {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement zero fee conservation row",
        ));
    }
    let residue_effects = effect_plan
        .rows
        .iter()
        .filter(|row| {
            row.kind == EconomicEffectKindV1::RESERVE
                && row.principal == FEE_RESIDUE_PRINCIPAL_V1
                && row.custody_domain == FEE_RESIDUE_CONTROL_DOMAIN_V1
                && row.delta_atoms > 0
        })
        .map(|row| {
            u128::try_from(row.delta_atoms)
                .map(|atoms| (row.asset.as_str(), atoms))
                .map_err(|_| AbiErrorV1::InvalidBounds("economic refinement fee residue"))
        })
        .collect::<AbiResultV1<BTreeMap<_, _>>>()?;
    let expected_residue = effect_plan
        .fee_conservation
        .iter()
        .filter(|row| row.carried_residue_atoms > 0)
        .map(|row| (row.asset.as_str(), row.carried_residue_atoms))
        .collect::<BTreeMap<_, _>>();
    if residue_effects != expected_residue {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement fee residue state mapping",
        ));
    }
    Ok(())
}

fn owned_totals_v1(state: &GlobalEconomicStateV1) -> AbiResultV1<BTreeMap<String, u128>> {
    let mut totals = BTreeMap::<String, u128>::new();
    for row in state
        .balances
        .iter()
        .chain(&state.custody)
        .chain(&state.reserves)
    {
        let total = totals
            .get(&row.asset)
            .copied()
            .unwrap_or(0)
            .checked_add(row.amount_atoms)
            .ok_or(AbiErrorV1::Conservation(
                "economic refinement owned total overflow",
            ))?;
        totals.insert(row.asset.clone(), total);
    }
    Ok(totals)
}

fn require_owned_supply_equality_v1(
    pre_owned: &BTreeMap<String, u128>,
    post_owned: &BTreeMap<String, u128>,
    pre_supply: &BTreeMap<String, u128>,
    post_supply: &BTreeMap<String, u128>,
) -> AbiResultV1<()> {
    let assets = pre_owned
        .keys()
        .chain(post_owned.keys())
        .chain(pre_supply.keys())
        .chain(post_supply.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    if assets.iter().any(|asset| {
        pre_owned.get(asset).copied().unwrap_or(0) != pre_supply.get(asset).copied().unwrap_or(0)
            || post_owned.get(asset).copied().unwrap_or(0)
                != post_supply.get(asset).copied().unwrap_or(0)
    }) {
        return Err(AbiErrorV1::Conservation(
            "economic refinement owned total does not equal supply",
        ));
    }
    Ok(())
}

fn require_conservation_v1(
    pre_state: &GlobalEconomicStateV1,
    post_state: &GlobalEconomicStateV1,
    effect_plan: &GlobalEconomicEffectPlanV1,
    state_delta: &DerivedGlobalEconomicStateDeltaV1,
) -> AbiResultV1<()> {
    let pre_owned = owned_totals_v1(pre_state)?;
    let post_owned = owned_totals_v1(post_state)?;
    let pre_supply = supply_map_v1(pre_state);
    let post_supply = supply_map_v1(post_state);
    require_owned_supply_equality_v1(&pre_owned, &post_owned, &pre_supply, &post_supply)?;
    let mut touched_assets = state_delta.touched_assets.clone();
    touched_assets.extend(
        effect_plan
            .rows
            .iter()
            .filter(|row| {
                matches!(
                    row.kind,
                    EconomicEffectKindV1::ISSUE | EconomicEffectKindV1::BURN
                )
            })
            .map(|row| row.asset.clone()),
    );
    let conservation = effect_plan
        .asset_conservation
        .iter()
        .map(|row| (row.asset.clone(), row))
        .collect::<BTreeMap<_, _>>();
    if conservation.keys().ne(touched_assets.iter()) {
        return Err(AbiErrorV1::Conservation(
            "economic refinement conservation asset set",
        ));
    }
    for asset in touched_assets {
        let row = conservation[&asset];
        let owned_pre = pre_owned.get(&asset).copied().unwrap_or(0);
        let owned_post = post_owned.get(&asset).copied().unwrap_or(0);
        let supply_pre = pre_supply.get(&asset).copied().unwrap_or(0);
        let supply_post = post_supply.get(&asset).copied().unwrap_or(0);
        if row.owned_and_custodied_pre_atoms != owned_pre
            || row.owned_and_custodied_post_atoms != owned_post
            || row.supply_pre_atoms != supply_pre
            || row.supply_post_atoms != supply_post
        {
            return Err(AbiErrorV1::Conservation(
                "economic refinement conservation state mismatch",
            ));
        }
    }
    Ok(())
}

fn refine_with_expected_post_height_v1(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV1<'_>,
    expected_post_height: u64,
) -> AbiResultV1<GlobalEconomicStateEffectRefinementV1> {
    candidate.pre_state.validate()?;
    candidate.post_state.validate()?;
    candidate.effect_plan.validate()?;
    if candidate.effect_plan.occurrence_consumptions.is_empty()
        != candidate.consumed_occurrences.is_empty()
    {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement occurrence disclosure mismatch",
        ));
    }
    require_fixed_context_v1(
        candidate.pre_state,
        candidate.post_state,
        expected_post_height,
    )?;
    require_nonzero_sparse_amounts_v1(candidate.pre_state)?;
    require_nonzero_sparse_amounts_v1(candidate.post_state)?;
    require_supported_effects_v1(candidate.effect_plan)?;
    let replay_insertions = derive_replay_insertions_v1(
        candidate.pre_state,
        candidate.post_state,
        candidate.effect_plan,
        candidate.consumed_occurrences,
        candidate.route_journals,
    )?;
    require_fee_mirror_v1(candidate.effect_plan)?;
    let state_delta = derive_global_economic_state_delta_v1(
        candidate.pre_state,
        candidate.post_state,
        candidate.effect_plan,
        &replay_insertions,
    )?;
    require_conservation_v1(
        candidate.pre_state,
        candidate.post_state,
        candidate.effect_plan,
        &state_delta,
    )?;
    let pre_state_root = candidate.pre_state.state_root()?;
    let post_state_root = candidate.post_state.state_root()?;
    let effect_plan_root = candidate.effect_plan.effect_plan_root()?;
    Ok(GlobalEconomicStateEffectRefinementV1 {
        pre_state_root,
        post_state_root,
        effect_plan_root,
        state_delta_root: state_delta.state_delta_root,
    })
}

pub fn refine_global_economic_state_effects_v1(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV1<'_>,
) -> AbiResultV1<GlobalEconomicStateEffectRefinementV1> {
    let has_occurrences = !candidate.effect_plan.occurrence_consumptions.is_empty();
    let expected_post_height = candidate
        .pre_state
        .height
        .checked_add(u64::from(has_occurrences))
        .ok_or(AbiErrorV1::InvalidBounds(
            "economic refinement state height",
        ))?;
    refine_with_expected_post_height_v1(candidate, expected_post_height)
}

pub fn refine_route_global_economic_state_effects_v1(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV1<'_>,
) -> AbiResultV1<GlobalEconomicStateEffectRefinementV1> {
    if candidate.consumed_occurrences.len() != 1
        || candidate.route_journals.len() != 1
        || candidate.effect_plan.occurrence_consumptions.len() != 1
    {
        return Err(AbiErrorV1::InvalidBinding(
            "route economic refinement occurrence count",
        ));
    }
    let occurrence = &candidate.consumed_occurrences[0];
    let post_height = candidate.post_state.height;
    if occurrence.height != post_height
        || (candidate.pre_state.height != post_height
            && candidate.pre_state.height.checked_add(1) != Some(post_height))
    {
        return Err(AbiErrorV1::InvalidBinding(
            "route economic refinement epoch height context",
        ));
    }
    refine_with_expected_post_height_v1(candidate, post_height)
}
