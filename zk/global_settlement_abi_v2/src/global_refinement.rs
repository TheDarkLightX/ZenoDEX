use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::canonical::{hash_global_v2, AbiErrorV2, AbiResultV2, RootV2};
use crate::effects::{GlobalEconomicEffectPlanV2, LaneWriteV2};
use crate::global_refinement_checks::require_global_economic_tables_v2;
use crate::global_refinement_lifecycle::{
    require_global_oracle_refinement_v2, require_global_terminal_refinement_v2,
};
use crate::global_state::{GlobalEconomicStateV2, ReplayStateV2};
use crate::lifecycle::{GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2};
use crate::proof::EconomicCommandOccurrenceV2;

pub const GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V2: &str =
    "zenodex/global-economic-state-effect-refinement/v2";
pub const GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_AUTHORITY_V2: &str = "NONE";

#[derive(Clone, Copy, Debug)]
pub struct GlobalEconomicStateEffectRefinementCandidateV2<'a> {
    pub pre_state: &'a GlobalEconomicStateV2,
    pub post_state: &'a GlobalEconomicStateV2,
    pub effect_plan: &'a GlobalEconomicEffectPlanV2,
    pub consumed_occurrences: &'a [EconomicCommandOccurrenceV2],
    pub terminal_plan: &'a GlobalTerminalObligationPlanV2,
    pub oracle_plan: &'a GlobalOracleOccurrencePlanV2,
}

#[derive(Serialize)]
struct StateDeltaContentV2<'a> {
    pre_state_root: &'a RootV2,
    post_state_root: &'a RootV2,
    effect_plan_root: &'a RootV2,
    lane_writes: &'a [LaneWriteV2],
    replay_insertions: &'a [ReplayStateV2],
    terminal_plan_root: &'a RootV2,
    oracle_plan_root: &'a RootV2,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobalEconomicStateEffectRefinementV2 {
    pre_state_root: RootV2,
    post_state_root: RootV2,
    effect_plan_root: RootV2,
    terminal_plan_root: RootV2,
    oracle_plan_root: RootV2,
    state_delta_root: RootV2,
}

impl GlobalEconomicStateEffectRefinementV2 {
    pub fn pre_state_root(&self) -> &RootV2 {
        &self.pre_state_root
    }

    pub fn post_state_root(&self) -> &RootV2 {
        &self.post_state_root
    }

    pub fn effect_plan_root(&self) -> &RootV2 {
        &self.effect_plan_root
    }

    pub fn terminal_plan_root(&self) -> &RootV2 {
        &self.terminal_plan_root
    }

    pub fn oracle_plan_root(&self) -> &RootV2 {
        &self.oracle_plan_root
    }

    pub fn state_delta_root(&self) -> &RootV2 {
        &self.state_delta_root
    }

    pub fn production_authority(&self) -> &'static str {
        GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_AUTHORITY_V2
    }

    pub fn refinement_root(&self) -> AbiResultV2<RootV2> {
        #[derive(Serialize)]
        struct RefinementContentV2<'a> {
            schema: &'static str,
            pre_state_root: &'a RootV2,
            post_state_root: &'a RootV2,
            effect_plan_root: &'a RootV2,
            terminal_plan_root: &'a RootV2,
            oracle_plan_root: &'a RootV2,
            state_delta_root: &'a RootV2,
        }
        hash_global_v2(
            "global-economic-state-effect-refinement-v2",
            &RefinementContentV2 {
                schema: GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V2,
                pre_state_root: &self.pre_state_root,
                post_state_root: &self.post_state_root,
                effect_plan_root: &self.effect_plan_root,
                terminal_plan_root: &self.terminal_plan_root,
                oracle_plan_root: &self.oracle_plan_root,
                state_delta_root: &self.state_delta_root,
            },
        )
    }
}

fn require_fixed_context_v2(
    pre_state: &GlobalEconomicStateV2,
    post_state: &GlobalEconomicStateV2,
) -> AbiResultV2<()> {
    if pre_state.chain_id != post_state.chain_id
        || pre_state.deployment_root != post_state.deployment_root
        || pre_state.writer_epoch != post_state.writer_epoch
        || pre_state.profile_root != post_state.profile_root
        || pre_state.history_root != post_state.history_root
        || pre_state.outbox != post_state.outbox
    {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement fixed context changed",
        ));
    }
    Ok(())
}

fn require_lane_refinement_v2(
    pre_state: &GlobalEconomicStateV2,
    post_state: &GlobalEconomicStateV2,
    effect_plan: &GlobalEconomicEffectPlanV2,
) -> AbiResultV2<()> {
    let mut changed = BTreeSet::new();
    for (pre, post) in pre_state.lane_roots.iter().zip(&post_state.lane_roots) {
        if pre.lane_id != post.lane_id
            || pre.module_release_id != post.module_release_id
            || pre.enabled != post.enabled
        {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement lane ownership changed outside migration",
            ));
        }
        if pre.state_root != post.state_root {
            if !pre.enabled {
                return Err(AbiErrorV2::InvalidBinding(
                    "global refinement disabled lane write",
                ));
            }
            changed.insert(pre.lane_id);
        }
    }
    let writes = effect_plan
        .lane_writes
        .iter()
        .map(|row| (row.lane_id, row))
        .collect::<BTreeMap<_, _>>();
    if writes.keys().copied().collect::<BTreeSet<_>>() != changed {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement lane write coverage mismatch",
        ));
    }
    let pre_by_lane = pre_state
        .lane_roots
        .iter()
        .map(|row| (row.lane_id, row))
        .collect::<BTreeMap<_, _>>();
    let post_by_lane = post_state
        .lane_roots
        .iter()
        .map(|row| (row.lane_id, row))
        .collect::<BTreeMap<_, _>>();
    if writes.iter().any(|(lane, write)| {
        write.pre_root != pre_by_lane[lane].state_root
            || write.post_root != post_by_lane[lane].state_root
    }) {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement lane write root mismatch",
        ));
    }
    Ok(())
}

fn validated_occurrence_ids_v2(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV2<'_>,
) -> AbiResultV2<Vec<RootV2>> {
    let mut occurrence_ids = Vec::with_capacity(candidate.consumed_occurrences.len());
    for occurrence in candidate.consumed_occurrences {
        occurrence.validate()?;
        occurrence_ids.push(occurrence.occurrence_id()?);
    }
    let ordered_unique = occurrence_ids.iter().cloned().collect::<BTreeSet<_>>();
    if occurrence_ids != ordered_unique.into_iter().collect::<Vec<_>>() {
        return Err(AbiErrorV2::InvalidOrder(
            "global refinement occurrences must be ordered and unique",
        ));
    }
    if candidate.effect_plan.occurrence_consumptions != occurrence_ids {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement replay consumption mismatch",
        ));
    }
    Ok(occurrence_ids)
}

fn derive_replay_insertions_v2(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV2<'_>,
    occurrence_ids: &[RootV2],
) -> AbiResultV2<Vec<ReplayStateV2>> {
    let pre_state_root = candidate.pre_state.state_root()?;
    let mut expected = candidate
        .pre_state
        .replay_state
        .iter()
        .map(|row| (row.replay_id.clone(), row.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut existing_occurrences = expected
        .values()
        .map(|row| row.occurrence_id.clone())
        .collect::<BTreeSet<_>>();
    let mut insertions = Vec::with_capacity(candidate.consumed_occurrences.len());
    for (occurrence, occurrence_id) in candidate
        .consumed_occurrences
        .iter()
        .zip(occurrence_ids.iter())
    {
        if occurrence.chain_id != candidate.pre_state.chain_id
            || occurrence.deployment_root != candidate.pre_state.deployment_root
            || occurrence.profile_root != candidate.pre_state.profile_root
            || occurrence.pre_state_root != pre_state_root
        {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement occurrence context mismatch",
            ));
        }
        let replay_id = occurrence.replay_id()?.to_string();
        if expected.contains_key(&replay_id) || existing_occurrences.contains(occurrence_id) {
            return Err(AbiErrorV2::InvalidBinding(
                "global refinement replay already consumed",
            ));
        }
        let row = ReplayStateV2 {
            replay_id: replay_id.clone(),
            occurrence_id: occurrence_id.clone(),
        };
        row.validate()?;
        expected.insert(replay_id, row.clone());
        existing_occurrences.insert(occurrence_id.clone());
        insertions.push(row);
    }
    if candidate.post_state.replay_state != expected.into_values().collect::<Vec<_>>() {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement replay post-state mismatch",
        ));
    }
    Ok(insertions)
}

fn require_replay_height_v2(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV2<'_>,
) -> AbiResultV2<()> {
    let expected_height = candidate
        .pre_state
        .height
        .checked_add(u64::from(!candidate.consumed_occurrences.is_empty()))
        .ok_or(AbiErrorV2::InvalidBounds(
            "global refinement height progression mismatch",
        ))?;
    if candidate.post_state.height != expected_height {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement height progression mismatch",
        ));
    }
    if candidate
        .consumed_occurrences
        .iter()
        .any(|occurrence| occurrence.height != candidate.post_state.height)
    {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement occurrence height mismatch",
        ));
    }
    Ok(())
}

fn require_replay_refinement_v2(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV2<'_>,
) -> AbiResultV2<Vec<ReplayStateV2>> {
    let occurrence_ids = validated_occurrence_ids_v2(candidate)?;
    let insertions = derive_replay_insertions_v2(candidate, &occurrence_ids)?;
    require_replay_height_v2(candidate)?;
    Ok(insertions)
}

fn validate_refinement_candidate_v2(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV2<'_>,
) -> AbiResultV2<Vec<ReplayStateV2>> {
    candidate.pre_state.validate()?;
    candidate.post_state.validate()?;
    candidate.effect_plan.validate()?;
    candidate.terminal_plan.validate()?;
    candidate.oracle_plan.validate()?;
    if !candidate.effect_plan.external_outbox_enqueue.is_empty() {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement external outbox requires the O-009 publisher",
        ));
    }
    if candidate.consumed_occurrences.is_empty()
        && (!candidate.effect_plan.is_empty()
            || !candidate.terminal_plan.deltas.is_empty()
            || !candidate.oracle_plan.deltas.is_empty()
            || candidate.pre_state != candidate.post_state)
    {
        return Err(AbiErrorV2::InvalidBinding(
            "global refinement zero-occurrence relation must be static",
        ));
    }
    require_fixed_context_v2(candidate.pre_state, candidate.post_state)?;
    require_lane_refinement_v2(
        candidate.pre_state,
        candidate.post_state,
        candidate.effect_plan,
    )?;
    require_global_economic_tables_v2(
        candidate.pre_state,
        candidate.post_state,
        candidate.effect_plan,
    )?;
    require_global_terminal_refinement_v2(
        candidate.pre_state,
        candidate.post_state,
        candidate.effect_plan,
        candidate.terminal_plan,
    )?;
    require_global_oracle_refinement_v2(
        candidate.pre_state,
        candidate.post_state,
        candidate.effect_plan,
        candidate.oracle_plan,
    )?;
    require_replay_refinement_v2(candidate)
}

fn build_refinement_witness_v2(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV2<'_>,
    replay_insertions: &[ReplayStateV2],
) -> AbiResultV2<GlobalEconomicStateEffectRefinementV2> {
    let pre_state_root = candidate.pre_state.state_root()?;
    let post_state_root = candidate.post_state.state_root()?;
    let effect_plan_root = candidate.effect_plan.effect_plan_root()?;
    let terminal_plan_root = candidate.terminal_plan.plan_root()?;
    let oracle_plan_root = candidate.oracle_plan.plan_root()?;
    let state_delta_root = hash_global_v2(
        "global-economic-state-delta-v2",
        &StateDeltaContentV2 {
            pre_state_root: &pre_state_root,
            post_state_root: &post_state_root,
            effect_plan_root: &effect_plan_root,
            lane_writes: &candidate.effect_plan.lane_writes,
            replay_insertions,
            terminal_plan_root: &terminal_plan_root,
            oracle_plan_root: &oracle_plan_root,
        },
    )?;
    Ok(GlobalEconomicStateEffectRefinementV2 {
        pre_state_root,
        post_state_root,
        effect_plan_root,
        terminal_plan_root,
        oracle_plan_root,
        state_delta_root,
    })
}

pub fn refine_global_economic_state_effects_v2(
    candidate: &GlobalEconomicStateEffectRefinementCandidateV2<'_>,
) -> AbiResultV2<GlobalEconomicStateEffectRefinementV2> {
    let replay_insertions = validate_refinement_candidate_v2(candidate)?;
    build_refinement_witness_v2(candidate, &replay_insertions)
}
