use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};

use super::{
    EconomicLaneIdV1, LaneStateTransitionErrorV1, LANE_STATE_OPENING_BATCH_VERSION_V1,
    MAX_LANE_STATE_OPENING_WITNESSES_V1,
};
use crate::{CommitmentV3, EconomicActionIdV1, SparseMerkleCellTransitionWitnessV1};

use super::lane_state_transition_bounded::deserialize_lane_opening_witnesses;
use super::lane_state_transition_hash::{opening_batch_root_v1, transition_witness_root_v1};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaneStateOpeningBatchInputV1 {
    pub lane_id: EconomicLaneIdV1,
    pub economic_action_id: EconomicActionIdV1,
    pub witnesses: Vec<SparseMerkleCellTransitionWitnessV1>,
    pub lane_pre_state_root: CommitmentV3,
    pub lane_post_state_root: CommitmentV3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LaneStateOpeningBatchV1 {
    batch_version: u16,
    lane_id: EconomicLaneIdV1,
    economic_action_id: EconomicActionIdV1,
    witnesses: Vec<SparseMerkleCellTransitionWitnessV1>,
    lane_pre_state_root: CommitmentV3,
    lane_post_state_root: CommitmentV3,
    openings_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LaneStateOpeningBatchWireV1 {
    batch_version: u16,
    lane_id: EconomicLaneIdV1,
    economic_action_id: EconomicActionIdV1,
    #[serde(deserialize_with = "deserialize_lane_opening_witnesses")]
    witnesses: Vec<SparseMerkleCellTransitionWitnessV1>,
    lane_pre_state_root: CommitmentV3,
    lane_post_state_root: CommitmentV3,
    openings_root: CommitmentV3,
}

impl LaneStateOpeningBatchV1 {
    pub fn new(input: LaneStateOpeningBatchInputV1) -> Result<Self, LaneStateTransitionErrorV1> {
        let mut batch = Self {
            batch_version: LANE_STATE_OPENING_BATCH_VERSION_V1,
            lane_id: input.lane_id,
            economic_action_id: input.economic_action_id,
            witnesses: input.witnesses,
            lane_pre_state_root: input.lane_pre_state_root,
            lane_post_state_root: input.lane_post_state_root,
            openings_root: input.lane_pre_state_root,
        };
        validate_opening_batch(&batch)?;
        batch.openings_root = opening_batch_root_v1(&batch)?;
        Ok(batch)
    }

    fn from_wire(wire: LaneStateOpeningBatchWireV1) -> Result<Self, LaneStateTransitionErrorV1> {
        let batch = Self {
            batch_version: wire.batch_version,
            lane_id: wire.lane_id,
            economic_action_id: wire.economic_action_id,
            witnesses: wire.witnesses,
            lane_pre_state_root: wire.lane_pre_state_root,
            lane_post_state_root: wire.lane_post_state_root,
            openings_root: wire.openings_root,
        };
        batch.validate_self_consistency()?;
        Ok(batch)
    }

    pub fn validate_self_consistency(&self) -> Result<(), LaneStateTransitionErrorV1> {
        validate_opening_batch(self)?;
        if opening_batch_root_v1(self)? != self.openings_root {
            return Err(LaneStateTransitionErrorV1::OpeningRootMismatch);
        }
        Ok(())
    }

    pub const fn batch_version(&self) -> u16 {
        self.batch_version
    }

    pub const fn lane_id(&self) -> EconomicLaneIdV1 {
        self.lane_id
    }

    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.economic_action_id
    }

    pub fn witnesses(&self) -> &[SparseMerkleCellTransitionWitnessV1] {
        &self.witnesses
    }

    pub const fn lane_pre_state_root(&self) -> CommitmentV3 {
        self.lane_pre_state_root
    }

    pub const fn lane_post_state_root(&self) -> CommitmentV3 {
        self.lane_post_state_root
    }

    pub const fn openings_root(&self) -> CommitmentV3 {
        self.openings_root
    }
}

impl<'de> Deserialize<'de> for LaneStateOpeningBatchV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_wire(LaneStateOpeningBatchWireV1::deserialize(deserializer)?)
            .map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum LaneStateTransitionContentV1 {
    Unchanged {
        lane_id: EconomicLaneIdV1,
        economic_action_id: EconomicActionIdV1,
        lane_state_root: CommitmentV3,
    },
    Changed(LaneStateOpeningBatchV1),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(transparent)]
pub struct LaneStateTransitionWitnessV1(LaneStateTransitionContentV1);

impl LaneStateTransitionWitnessV1 {
    pub const fn unchanged(
        lane_id: EconomicLaneIdV1,
        economic_action_id: EconomicActionIdV1,
        lane_state_root: CommitmentV3,
    ) -> Self {
        Self(LaneStateTransitionContentV1::Unchanged {
            lane_id,
            economic_action_id,
            lane_state_root,
        })
    }

    pub fn changed(batch: LaneStateOpeningBatchV1) -> Result<Self, LaneStateTransitionErrorV1> {
        batch.validate_self_consistency()?;
        Ok(Self(LaneStateTransitionContentV1::Changed(batch)))
    }

    pub fn validate_self_consistency(&self) -> Result<(), LaneStateTransitionErrorV1> {
        match &self.0 {
            LaneStateTransitionContentV1::Unchanged { .. } => Ok(()),
            LaneStateTransitionContentV1::Changed(batch) => batch.validate_self_consistency(),
        }
    }

    pub const fn lane_id(&self) -> EconomicLaneIdV1 {
        match &self.0 {
            LaneStateTransitionContentV1::Unchanged { lane_id, .. } => *lane_id,
            LaneStateTransitionContentV1::Changed(batch) => batch.lane_id(),
        }
    }

    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        match &self.0 {
            LaneStateTransitionContentV1::Unchanged {
                economic_action_id, ..
            } => *economic_action_id,
            LaneStateTransitionContentV1::Changed(batch) => batch.economic_action_id(),
        }
    }

    pub const fn lane_pre_state_root(&self) -> CommitmentV3 {
        match &self.0 {
            LaneStateTransitionContentV1::Unchanged {
                lane_state_root, ..
            } => *lane_state_root,
            LaneStateTransitionContentV1::Changed(batch) => batch.lane_pre_state_root(),
        }
    }

    pub const fn lane_post_state_root(&self) -> CommitmentV3 {
        match &self.0 {
            LaneStateTransitionContentV1::Unchanged {
                lane_state_root, ..
            } => *lane_state_root,
            LaneStateTransitionContentV1::Changed(batch) => batch.lane_post_state_root(),
        }
    }

    pub const fn changed_batch(&self) -> Option<&LaneStateOpeningBatchV1> {
        match &self.0 {
            LaneStateTransitionContentV1::Unchanged { .. } => None,
            LaneStateTransitionContentV1::Changed(batch) => Some(batch),
        }
    }

    pub fn canonical_commitment(&self) -> Result<CommitmentV3, LaneStateTransitionErrorV1> {
        transition_witness_root_v1(self)
    }

    pub(super) const fn kind_code(&self) -> u8 {
        match &self.0 {
            LaneStateTransitionContentV1::Unchanged { .. } => 0,
            LaneStateTransitionContentV1::Changed(_) => 1,
        }
    }
}

impl<'de> Deserialize<'de> for LaneStateTransitionWitnessV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let witness = Self(LaneStateTransitionContentV1::deserialize(deserializer)?);
        witness
            .validate_self_consistency()
            .map_err(de::Error::custom)?;
        Ok(witness)
    }
}

fn validate_opening_batch(
    batch: &LaneStateOpeningBatchV1,
) -> Result<(), LaneStateTransitionErrorV1> {
    if batch.batch_version != LANE_STATE_OPENING_BATCH_VERSION_V1 {
        return Err(LaneStateTransitionErrorV1::InvalidBatchVersion(
            batch.batch_version,
        ));
    }
    if batch.witnesses.is_empty() {
        return Err(LaneStateTransitionErrorV1::EmptyWitnesses);
    }
    if batch.witnesses.len() > MAX_LANE_STATE_OPENING_WITNESSES_V1 {
        return Err(LaneStateTransitionErrorV1::TooManyWitnesses {
            actual: batch.witnesses.len(),
            maximum: MAX_LANE_STATE_OPENING_WITNESSES_V1,
        });
    }
    if batch.lane_pre_state_root == batch.lane_post_state_root {
        return Err(LaneStateTransitionErrorV1::UnchangedBatchRoot);
    }
    validate_opening_witnesses(batch)
}

fn validate_opening_witnesses(
    batch: &LaneStateOpeningBatchV1,
) -> Result<(), LaneStateTransitionErrorV1> {
    for (index, witness) in batch.witnesses.iter().enumerate() {
        witness.validate_self_consistency()?;
        if witness.economic_action_id() != batch.economic_action_id {
            return Err(LaneStateTransitionErrorV1::EconomicActionMismatch { index });
        }
    }
    for pair in batch.witnesses.windows(2) {
        if pair[0].cell_key() == pair[1].cell_key() {
            return Err(LaneStateTransitionErrorV1::DuplicateCellKey);
        }
        if pair[0].cell_key() > pair[1].cell_key() {
            return Err(LaneStateTransitionErrorV1::NonCanonicalCellKeyOrder);
        }
    }
    let first = batch
        .witnesses
        .first()
        .ok_or(LaneStateTransitionErrorV1::EmptyWitnesses)?;
    if first.claimed_pre_root() != batch.lane_pre_state_root {
        return Err(LaneStateTransitionErrorV1::BatchPreRootMismatch);
    }
    for (offset, pair) in batch.witnesses.windows(2).enumerate() {
        if pair[0].claimed_post_root() != pair[1].claimed_pre_root() {
            let index =
                offset
                    .checked_add(1)
                    .ok_or(LaneStateTransitionErrorV1::ArithmeticOverflow(
                        "root_chain_index",
                    ))?;
            return Err(LaneStateTransitionErrorV1::RootChainDiscontinuity { index });
        }
    }
    let last = batch
        .witnesses
        .last()
        .ok_or(LaneStateTransitionErrorV1::EmptyWitnesses)?;
    if last.claimed_post_root() != batch.lane_post_state_root {
        return Err(LaneStateTransitionErrorV1::BatchPostRootMismatch);
    }
    Ok(())
}
