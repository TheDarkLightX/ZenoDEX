//! Restricted global consumer for the custody-aware ASSET_TRANSFER successor.
//!
//! This relation binds the complete lane frame to existing V2 global state and
//! delegates final state/effect/replay checking to the unchanged global
//! refinement core. It creates no proof, settlement, publication, or runtime
//! authority.

use crate::asset_lane_custody::AssetLaneCustodyAcceptedV2;
use crate::asset_lane_custody_state::AssetLaneCustodyStateV2;
use crate::canonical::{AbiErrorV2, AbiResultV2};
use crate::effects::LaneIdV2;
use crate::global_refinement::{
    refine_global_economic_state_effects_v2, GlobalEconomicStateEffectRefinementCandidateV2,
    GlobalEconomicStateEffectRefinementV2,
};
use crate::global_state::GlobalEconomicStateV2;
use crate::lifecycle::{GlobalOracleOccurrencePlanV2, GlobalTerminalObligationPlanV2};
use crate::proof::EconomicCommandOccurrenceV2;

fn require_complete_projection(
    lane: &AssetLaneCustodyStateV2,
    state: &GlobalEconomicStateV2,
) -> AbiResultV2<()> {
    let lane_root = state
        .lane_roots
        .iter()
        .find(|row| row.lane_id == LaneIdV2::ASSET_TRANSFER)
        .ok_or(AbiErrorV2::InvalidBinding(
            "custody lane/global complete projection mismatch",
        ))?;
    let positive_supplies = lane
        .supplies()
        .iter()
        .filter(|row| row.amount_atoms != 0)
        .cloned()
        .collect::<Vec<_>>();
    if state.balances != lane.balances()
        || state.custody != lane.custody
        || state.supplies != positive_supplies
        || !state.reserves.is_empty()
        || lane_root.state_root != lane.state_root()?
        || lane_root.module_release_id != *lane.module_release_id()
        || !lane_root.enabled
    {
        return Err(AbiErrorV2::InvalidBinding(
            "custody lane/global complete projection mismatch",
        ));
    }
    Ok(())
}

pub fn refine_asset_lane_custody_global_v2(
    lane_pre: &AssetLaneCustodyStateV2,
    accepted: &AssetLaneCustodyAcceptedV2,
    global_pre: &GlobalEconomicStateV2,
    global_post: &GlobalEconomicStateV2,
    occurrence: &EconomicCommandOccurrenceV2,
) -> AbiResultV2<GlobalEconomicStateEffectRefinementV2> {
    lane_pre.validate()?;
    accepted.validate()?;
    global_pre.validate()?;
    global_post.validate()?;
    occurrence.validate()?;

    let lane_post = accepted.post_state();
    require_complete_projection(lane_pre, global_pre)?;
    require_complete_projection(lane_post, global_post)?;

    let journal = accepted.module_journal();
    let occurrence_id = occurrence.occurrence_id()?;
    let lane_pre_root = lane_pre.state_root()?;
    let lane_post_root = lane_post.state_root()?;
    let effect_plan_root = accepted.effects().effect_plan_root()?;
    if journal.chain_id != global_pre.chain_id
        || journal.deployment_root != global_pre.deployment_root
        || journal.profile_root != global_pre.profile_root
        || journal.writer_epoch != global_pre.writer_epoch
        || journal.command_occurrence_id != occurrence_id
        || journal.pre_lane_root != lane_pre_root
        || journal.post_lane_root != lane_post_root
        || journal.effect_plan_root != effect_plan_root
    {
        return Err(AbiErrorV2::InvalidBinding(
            "custody global source journal binding mismatch",
        ));
    }
    if global_pre.liabilities != global_post.liabilities
        || global_pre.custody != global_post.custody
    {
        return Err(AbiErrorV2::InvalidBinding(
            "custody global claimant or custody frame changed",
        ));
    }

    let terminal_plan = GlobalTerminalObligationPlanV2::empty();
    let oracle_plan = GlobalOracleOccurrencePlanV2::empty();
    refine_global_economic_state_effects_v2(&GlobalEconomicStateEffectRefinementCandidateV2 {
        pre_state: global_pre,
        post_state: global_post,
        effect_plan: accepted.effects(),
        consumed_occurrences: std::slice::from_ref(occurrence),
        terminal_plan: &terminal_plan,
        oracle_plan: &oracle_plan,
    })
}
