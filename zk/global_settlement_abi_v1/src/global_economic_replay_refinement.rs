//! Replay-state refinement for disclosed economic command occurrences.

use std::collections::BTreeSet;

use crate::canonical::{AbiErrorV1, AbiResultV1, MAX_EPOCH_COMMANDS_V1};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::proof::{EconomicCommandOccurrenceV1, RouteCompositionJournalV1};
use crate::state::{GlobalEconomicStateV1, ReplayStateV1};

pub(crate) fn derive_replay_insertions_v1(
    pre_state: &GlobalEconomicStateV1,
    post_state: &GlobalEconomicStateV1,
    effect_plan: &GlobalEconomicEffectPlanV1,
    consumed_occurrences: &[EconomicCommandOccurrenceV1],
    route_journals: &[RouteCompositionJournalV1],
) -> AbiResultV1<Vec<ReplayStateV1>> {
    if consumed_occurrences.len() > MAX_EPOCH_COMMANDS_V1 {
        return Err(AbiErrorV1::InvalidBounds(
            "economic refinement occurrence count",
        ));
    }
    if route_journals.len() != consumed_occurrences.len() {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement route-state chain count",
        ));
    }
    let disclosed_roots = consumed_occurrences
        .iter()
        .map(EconomicCommandOccurrenceV1::occurrence_id)
        .collect::<AbiResultV1<BTreeSet<_>>>()?
        .into_iter()
        .collect::<Vec<_>>();
    if disclosed_roots != effect_plan.occurrence_consumptions {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement occurrence disclosure mismatch",
        ));
    }
    let mut previous_position = None;
    let mut current_root = pre_state.state_root()?;
    for (occurrence, journal) in consumed_occurrences.iter().zip(route_journals) {
        journal.validate()?;
        let position = (occurrence.height, occurrence.tx_index, occurrence.op_index);
        if previous_position.is_some_and(|previous| previous >= position) {
            return Err(AbiErrorV1::InvalidOrder(
                "economic refinement occurrence order",
            ));
        }
        previous_position = Some(position);
        if occurrence.chain_id != pre_state.chain_id
            || occurrence.deployment_root != pre_state.deployment_root
            || occurrence.profile_root != pre_state.profile_root
            || occurrence.height != pre_state.height
            || occurrence.pre_state_root != current_root
            || journal.chain_id != pre_state.chain_id
            || journal.deployment_root != pre_state.deployment_root
            || journal.profile_root != pre_state.profile_root
            || journal.writer_epoch != pre_state.writer_epoch
            || journal.route_release_id != occurrence.route_release_id
            || journal.command_occurrence_id != occurrence.occurrence_id()?
            || journal.pre_state_root != current_root
        {
            return Err(AbiErrorV1::InvalidBinding(
                "economic refinement occurrence state context mismatch",
            ));
        }
        current_root = journal.post_state_root.clone();
    }
    if !consumed_occurrences.is_empty() && current_root != post_state.state_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement route-state chain terminal",
        ));
    }

    let mut insertions = consumed_occurrences
        .iter()
        .map(|occurrence| {
            Ok(ReplayStateV1 {
                replay_id: occurrence.replay_id()?.to_string(),
                occurrence_id: occurrence.occurrence_id()?,
            })
        })
        .collect::<AbiResultV1<Vec<_>>>()?;
    insertions.sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
    if insertions
        .windows(2)
        .any(|pair| pair[0].replay_id == pair[1].replay_id)
    {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement duplicate replay identity",
        ));
    }
    let existing_occurrence_ids = pre_state
        .replay_state
        .iter()
        .map(|row| &row.occurrence_id)
        .collect::<BTreeSet<_>>();
    if insertions
        .iter()
        .any(|row| existing_occurrence_ids.contains(&row.occurrence_id))
    {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement occurrence already consumed",
        ));
    }
    let existing_ids = pre_state
        .replay_state
        .iter()
        .map(|row| row.replay_id.as_str())
        .collect::<BTreeSet<_>>();
    if insertions
        .iter()
        .any(|row| existing_ids.contains(row.replay_id.as_str()))
    {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement replay identity already consumed",
        ));
    }
    let mut expected_post = pre_state.replay_state.clone();
    expected_post.extend(insertions.iter().cloned());
    expected_post.sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
    if post_state.replay_state != expected_post {
        return Err(AbiErrorV1::InvalidBinding(
            "economic refinement replay state delta mismatch",
        ));
    }
    Ok(insertions)
}
