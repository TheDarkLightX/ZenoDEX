//! Canonical economic statement producer for the custody-aware ASSET_TRANSFER lane.
//!
//! The returned bytes bind an already-accepted lane journal to the two endpoint
//! roots checked by the existing global refinement relation. They are an inner
//! economic payload and carry no proof, receipt, publication, or settlement
//! authority.

use serde::Serialize;

use crate::asset_lane_coordinator_types::{AssetLaneCommandV2, AssetLaneRejectedV2};
use crate::asset_lane_custody::{transition_asset_lane_custody_v2, AssetLaneCustodyResultV2};
use crate::asset_lane_custody_global::refine_asset_lane_custody_global_v2;
use crate::asset_lane_custody_state::AssetLaneCustodyStateV2;
use crate::asset_lane_state::AssetLaneContextV2;
use crate::canonical::{canonical_bytes_v2, AbiErrorV2, AbiResultV2, RootV2};
use crate::global_state::GlobalEconomicStateV2;
use crate::proof::LaneModuleTransitionJournalV2;

pub const ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_SCHEMA_V2: &str =
    "zenodex/asset-lane-custody-global-statement/v2";

#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub enum AssetLaneCustodyStatementResultV2 {
    Statement(Vec<u8>),
    Rejected(AssetLaneRejectedV2),
}

#[derive(Serialize)]
struct AssetLaneCustodyGlobalStatementV2<'a> {
    schema: &'static str,
    module_journal: &'a LaneModuleTransitionJournalV2,
    global_pre_state_root: &'a RootV2,
    global_post_state_root: &'a RootV2,
}

pub fn prepare_asset_lane_custody_global_statement_v2(
    context: &AssetLaneContextV2,
    pre_state: &AssetLaneCustodyStateV2,
    command: &AssetLaneCommandV2,
    global_pre: &GlobalEconomicStateV2,
    global_post: &GlobalEconomicStateV2,
) -> AbiResultV2<AssetLaneCustodyStatementResultV2> {
    let accepted = match transition_asset_lane_custody_v2(context, pre_state, command)? {
        AssetLaneCustodyResultV2::Accepted(accepted) => accepted,
        AssetLaneCustodyResultV2::Rejected(rejected) => {
            return Ok(AssetLaneCustodyStatementResultV2::Rejected(*rejected));
        }
    };
    let occurrence = context
        .occurrence
        .as_ref()
        .ok_or(AbiErrorV2::InvalidBinding(
            "asset lane custody statement occurrence",
        ))?;
    let refinement = refine_asset_lane_custody_global_v2(
        pre_state,
        &accepted,
        global_pre,
        global_post,
        occurrence,
    )?;
    let bytes = canonical_bytes_v2(&AssetLaneCustodyGlobalStatementV2 {
        schema: ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_SCHEMA_V2,
        module_journal: accepted.module_journal(),
        global_pre_state_root: refinement.pre_state_root(),
        global_post_state_root: refinement.post_state_root(),
    })?;
    Ok(AssetLaneCustodyStatementResultV2::Statement(bytes))
}
