//! Owned, data-only prospective state construction for one asset epoch position.
//!
//! The constructor derives a candidate post-state from an epoch position,
//! predecessor, occurrence, and accepted asset-transfer module output. It
//! performs no receipt verification and grants no admission, store, publication,
//! or settlement authority. The existing epoch allocation relation remains the
//! checker for allocation content; receipt, store, publication, and settlement
//! authorities remain separate.

use crate::asset_transfer_global_allocation::AssetTransferEpochPositionV1;
use crate::asset_transfer_lane_module::AssetTransferLaneModuleAcceptedV1;
use crate::canonical::{AbiErrorV1, AbiResultV1, MAX_EPOCH_COMMANDS_V1};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::LaneIdV1;
use crate::state::{GlobalEconomicStateV1, ReplayStateV1};

/// Owned data-only copy of an epoch source and position index.
///
/// The public fields of `AssetTransferEpochPositionV1` borrow their source.
/// This owned mirror keeps a returned proposal detached from all caller-owned
/// state. Its fields remain private so callers cannot construct a position
/// through a second unchecked API.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssetTransferEpochPositionOwnedV1 {
    epoch_source: GlobalEconomicStateV1,
    occurrence_index: usize,
}

impl AssetTransferEpochPositionOwnedV1 {
    /// Return the owned epoch source snapshot.
    pub fn epoch_source(&self) -> &GlobalEconomicStateV1 {
        &self.epoch_source
    }

    /// Return the position index.
    pub fn occurrence_index(&self) -> usize {
        self.occurrence_index
    }
}

/// Fully owned, input-derived prospective state for one asset epoch position.
///
/// `post_state` is ordinary proposal data. The constructor intentionally does
/// not authenticate the source, establish predecessor adjacency, verify a
/// receipt, or decide whether a later consumer may admit the proposal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssetTransferEpochProspectiveProjectionV1 {
    position: AssetTransferEpochPositionOwnedV1,
    predecessor: GlobalEconomicStateV1,
    occurrence: EconomicCommandOccurrenceV1,
    accepted: AssetTransferLaneModuleAcceptedV1,
    post_state: GlobalEconomicStateV1,
}

impl AssetTransferEpochProspectiveProjectionV1 {
    /// Return the owned position snapshot.
    pub fn position(&self) -> &AssetTransferEpochPositionOwnedV1 {
        &self.position
    }

    /// Return the owned predecessor snapshot.
    pub fn predecessor(&self) -> &GlobalEconomicStateV1 {
        &self.predecessor
    }

    /// Return the owned occurrence snapshot.
    pub fn occurrence(&self) -> &EconomicCommandOccurrenceV1 {
        &self.occurrence
    }

    /// Return the owned accepted module-output snapshot.
    pub fn accepted(&self) -> &AssetTransferLaneModuleAcceptedV1 {
        &self.accepted
    }

    /// Return the derived owned prospective post-state.
    pub fn post_state(&self) -> &GlobalEconomicStateV1 {
        &self.post_state
    }
}

fn derive_post_state_v1(
    predecessor: &GlobalEconomicStateV1,
    occurrence: &EconomicCommandOccurrenceV1,
    accepted: &AssetTransferLaneModuleAcceptedV1,
) -> AbiResultV1<GlobalEconomicStateV1> {
    let private_post = &accepted.private_port.post_state;
    let asset_lane_root = private_post.state_root()?;

    let mut lane_roots = predecessor.lane_roots.clone();
    let Some(asset_lane) = lane_roots
        .iter_mut()
        .find(|lane| lane.lane_id == LaneIdV1::ASSET_TRANSFER)
    else {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer epoch projection asset lane",
        ));
    };
    asset_lane.state_root = asset_lane_root;

    let replay = ReplayStateV1 {
        replay_id: occurrence.replay_id()?.as_str().to_owned(),
        occurrence_id: occurrence.occurrence_id()?,
    };
    let mut replay_state = predecessor.replay_state.clone();
    replay_state.push(replay);
    replay_state.sort_by(|left, right| left.replay_id.cmp(&right.replay_id));

    let mut post_state = predecessor.clone();
    post_state.height = occurrence.height;
    post_state.lane_roots = lane_roots;
    post_state.balances = private_post.balances.clone();
    post_state.supplies = private_post.supplies.clone();
    post_state.replay_state = replay_state;
    post_state.validate()?;
    Ok(post_state)
}

/// Construct one owned, data-only prospective asset-transfer epoch state.
///
/// The returned state changes only occurrence height, the selected asset-lane
/// root, balances, supplies, and one canonical replay insertion. All other
/// predecessor frame fields are retained. This function is an internal data
/// constructor; malformed values may return `AbiErrorV1` and no protocol reject
/// result is claimed here.
#[must_use = "the owned projection carries the detached proposal inputs and post-state"]
pub fn project_asset_transfer_epoch_position_v1(
    position: AssetTransferEpochPositionV1<'_>,
    predecessor: &GlobalEconomicStateV1,
    occurrence: &EconomicCommandOccurrenceV1,
    accepted: &AssetTransferLaneModuleAcceptedV1,
) -> AbiResultV1<AssetTransferEpochProspectiveProjectionV1> {
    position.epoch_source.validate()?;
    if position.occurrence_index >= MAX_EPOCH_COMMANDS_V1 {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer epoch projection position index",
        ));
    }
    predecessor.validate()?;
    occurrence.validate()?;
    accepted.validate()?;

    let owned_position = AssetTransferEpochPositionOwnedV1 {
        epoch_source: position.epoch_source.clone(),
        occurrence_index: position.occurrence_index,
    };
    let owned_predecessor = predecessor.clone();
    let owned_occurrence = occurrence.clone();
    let owned_accepted = accepted.clone();
    let post_state = derive_post_state_v1(&owned_predecessor, &owned_occurrence, &owned_accepted)?;

    Ok(AssetTransferEpochProspectiveProjectionV1 {
        position: owned_position,
        predecessor: owned_predecessor,
        occurrence: owned_occurrence,
        accepted: owned_accepted,
        post_state,
    })
}
