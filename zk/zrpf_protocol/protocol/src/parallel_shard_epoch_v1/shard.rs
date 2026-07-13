use serde::{de, Deserialize, Deserializer, Serialize};

use super::hash::{
    canonical_empty_carry_queue_root_v1, canonical_empty_cross_shard_inbox_root_v1,
    canonical_empty_cross_shard_outbox_root_v1, derive_global_carry_post_root_v1,
    derive_global_carry_pre_root_v1, derive_global_inbox_root_v1, derive_global_outbox_root_v1,
    derive_global_post_state_root_v1, derive_global_pre_state_root_v1,
    derive_governed_shard_set_root_v1, derive_shard_action_nullifiers_root_v1,
    derive_shard_semantic_values_root_v1,
};
use super::{ParallelShardEpochErrorV1, PARALLEL_SHARD_COUNT_V1};
use crate::{CommitmentV3, ProfileIdV3};

/// Nonzero key for one governed shard.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct ShardIdV1(CommitmentV3);

impl ShardIdV1 {
    pub fn new(bytes: [u8; 32]) -> Result<Self, ParallelShardEpochErrorV1> {
        Ok(Self(CommitmentV3::new(bytes)?))
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        self.0.as_bytes()
    }

    pub const fn as_commitment(self) -> CommitmentV3 {
        self.0
    }
}

/// Exact sorted set admitted by governance for the bounded V1 profile.
///
/// The array width makes missing and extra shards unrepresentable. Construction
/// rejects duplicates and noncanonical ordering rather than sorting host input.
/// Governance or release authority must supply and bind this set externally.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(transparent)]
pub struct GovernedShardSetV1([ShardIdV1; PARALLEL_SHARD_COUNT_V1]);

impl GovernedShardSetV1 {
    pub fn new(
        shard_ids: [ShardIdV1; PARALLEL_SHARD_COUNT_V1],
    ) -> Result<Self, ParallelShardEpochErrorV1> {
        require_strictly_sorted(&shard_ids)?;
        Ok(Self(shard_ids))
    }

    pub fn validate(&self) -> Result<(), ParallelShardEpochErrorV1> {
        require_strictly_sorted(&self.0)
    }

    pub fn canonical_root(&self) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
        self.validate()?;
        derive_governed_shard_set_root_v1(&self.0)
    }

    pub const fn shard_ids(&self) -> &[ShardIdV1; PARALLEL_SHARD_COUNT_V1] {
        &self.0
    }
}

impl<'de> Deserialize<'de> for GovernedShardSetV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(<[ShardIdV1; PARALLEL_SHARD_COUNT_V1]>::deserialize(
            deserializer,
        )?)
        .map_err(de::Error::custom)
    }
}

/// Untrusted per-shard semantic summary proposed to the two-shard composer.
///
/// The message and carry fields are present so a nonempty value reaches a
/// typed reject. V1 accepts only the channel-specific canonical empty roots.
/// An authenticated application adapter must establish the meaning of the
/// proposed local state, semantic-value, and nullifier roots.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ShardTransitionInputV1 {
    pub shard_id: ShardIdV1,
    pub scope_hash: CommitmentV3,
    pub semantic_profile_id: ProfileIdV3,
    pub state_root_scheme_id: CommitmentV3,
    pub local_pre_state_root: CommitmentV3,
    pub local_post_state_root: CommitmentV3,
    pub semantic_value_root: CommitmentV3,
    pub shard_action_nullifiers_root: CommitmentV3,
    pub cross_shard_outbox_root: CommitmentV3,
    pub cross_shard_inbox_root: CommitmentV3,
    pub carry_queue_pre_root: CommitmentV3,
    pub carry_queue_post_root: CommitmentV3,
}

/// Epoch-owned bindings that every shard transition must match exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShardCompositionContextV1 {
    scope_hash: CommitmentV3,
    semantic_profile_id: ProfileIdV3,
    state_root_scheme_id: CommitmentV3,
}

impl ShardCompositionContextV1 {
    pub const fn new(
        scope_hash: CommitmentV3,
        semantic_profile_id: ProfileIdV3,
        state_root_scheme_id: CommitmentV3,
    ) -> Self {
        Self {
            scope_hash,
            semantic_profile_id,
            state_root_scheme_id,
        }
    }
}

/// Validated local transition summary. It carries no proof or settlement authority.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(transparent)]
pub struct ShardTransitionV1(ShardTransitionInputV1);

impl ShardTransitionV1 {
    fn from_input(
        input: ShardTransitionInputV1,
        shard_index: usize,
    ) -> Result<Self, ParallelShardEpochErrorV1> {
        validate_empty_roots(&input, shard_index)?;
        Ok(Self(input))
    }

    fn validate(&self, shard_index: usize) -> Result<(), ParallelShardEpochErrorV1> {
        validate_empty_roots(&self.0, shard_index)
    }

    pub const fn shard_id(&self) -> ShardIdV1 {
        self.0.shard_id
    }

    pub const fn scope_hash(&self) -> CommitmentV3 {
        self.0.scope_hash
    }

    pub const fn semantic_profile_id(&self) -> ProfileIdV3 {
        self.0.semantic_profile_id
    }

    pub const fn state_root_scheme_id(&self) -> CommitmentV3 {
        self.0.state_root_scheme_id
    }

    pub const fn local_pre_state_root(&self) -> CommitmentV3 {
        self.0.local_pre_state_root
    }

    pub const fn local_post_state_root(&self) -> CommitmentV3 {
        self.0.local_post_state_root
    }

    pub const fn semantic_value_root(&self) -> CommitmentV3 {
        self.0.semantic_value_root
    }

    pub const fn shard_action_nullifiers_root(&self) -> CommitmentV3 {
        self.0.shard_action_nullifiers_root
    }

    pub const fn cross_shard_outbox_root(&self) -> CommitmentV3 {
        self.0.cross_shard_outbox_root
    }

    pub const fn cross_shard_inbox_root(&self) -> CommitmentV3 {
        self.0.cross_shard_inbox_root
    }

    pub const fn carry_queue_pre_root(&self) -> CommitmentV3 {
        self.0.carry_queue_pre_root
    }

    pub const fn carry_queue_post_root(&self) -> CommitmentV3 {
        self.0.carry_queue_post_root
    }

    pub fn to_input(&self) -> ShardTransitionInputV1 {
        self.0.clone()
    }
}

/// Canonical complete map from two governed shard IDs to local transitions.
///
/// Global roots hash each value together with its shard key. This prevents a
/// bare list of state roots from changing meaning when assignments change.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(transparent)]
pub struct CanonicalShardStateMapV1([ShardTransitionV1; PARALLEL_SHARD_COUNT_V1]);

impl CanonicalShardStateMapV1 {
    pub fn new(
        governed_shards: &GovernedShardSetV1,
        context: ShardCompositionContextV1,
        transitions: [ShardTransitionInputV1; PARALLEL_SHARD_COUNT_V1],
    ) -> Result<Self, ParallelShardEpochErrorV1> {
        let state_map = Self::from_inputs(transitions)?;
        state_map.validate_against(governed_shards, context)?;
        Ok(state_map)
    }

    fn from_inputs(
        inputs: [ShardTransitionInputV1; PARALLEL_SHARD_COUNT_V1],
    ) -> Result<Self, ParallelShardEpochErrorV1> {
        let [first, second] = inputs;
        let entries = [
            ShardTransitionV1::from_input(first, 0)?,
            ShardTransitionV1::from_input(second, 1)?,
        ];
        let state_map = Self(entries);
        state_map.validate()?;
        Ok(state_map)
    }

    pub fn validate(&self) -> Result<(), ParallelShardEpochErrorV1> {
        require_strictly_sorted(&[self.0[0].shard_id(), self.0[1].shard_id()])?;
        for (index, entry) in self.0.iter().enumerate() {
            entry.validate(index)?;
        }
        require_common_context(&self.0)?;
        Ok(())
    }

    pub fn validate_against(
        &self,
        governed_shards: &GovernedShardSetV1,
        context: ShardCompositionContextV1,
    ) -> Result<(), ParallelShardEpochErrorV1> {
        self.validate()?;
        if self.shard_ids() != *governed_shards.shard_ids() {
            return Err(ParallelShardEpochErrorV1::GovernedShardMismatch);
        }
        for (index, entry) in self.0.iter().enumerate() {
            if entry.scope_hash() != context.scope_hash {
                return Err(ParallelShardEpochErrorV1::ScopeMismatch { shard_index: index });
            }
            if entry.semantic_profile_id() != context.semantic_profile_id {
                return Err(ParallelShardEpochErrorV1::SemanticProfileMismatch {
                    shard_index: index,
                });
            }
            if entry.state_root_scheme_id() != context.state_root_scheme_id {
                return Err(ParallelShardEpochErrorV1::StateRootSchemeMismatch {
                    shard_index: index,
                });
            }
        }
        Ok(())
    }

    pub const fn entries(&self) -> &[ShardTransitionV1; PARALLEL_SHARD_COUNT_V1] {
        &self.0
    }

    pub fn shard_ids(&self) -> [ShardIdV1; PARALLEL_SHARD_COUNT_V1] {
        [self.0[0].shard_id(), self.0[1].shard_id()]
    }

    pub fn global_pre_state_root(&self) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
        self.validate()?;
        derive_global_pre_state_root_v1(self)
    }

    pub fn global_post_state_root(&self) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
        self.validate()?;
        derive_global_post_state_root_v1(self)
    }

    pub fn shard_semantic_values_root(&self) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
        self.validate()?;
        derive_shard_semantic_values_root_v1(self)
    }

    pub fn shard_action_nullifiers_root(&self) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
        self.validate()?;
        derive_shard_action_nullifiers_root_v1(self)
    }

    pub fn global_outbox_root(&self) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
        self.validate()?;
        derive_global_outbox_root_v1(self)
    }

    pub fn global_inbox_root(&self) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
        self.validate()?;
        derive_global_inbox_root_v1(self)
    }

    pub fn global_carry_pre_root(&self) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
        self.validate()?;
        derive_global_carry_pre_root_v1(self)
    }

    pub fn global_carry_post_root(&self) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
        self.validate()?;
        derive_global_carry_post_root_v1(self)
    }

    pub(super) fn semantic_roots(&self) -> Result<[CommitmentV3; 8], ParallelShardEpochErrorV1> {
        self.validate()?;
        Ok([
            derive_global_pre_state_root_v1(self)?,
            derive_global_post_state_root_v1(self)?,
            derive_shard_semantic_values_root_v1(self)?,
            derive_shard_action_nullifiers_root_v1(self)?,
            derive_global_outbox_root_v1(self)?,
            derive_global_inbox_root_v1(self)?,
            derive_global_carry_pre_root_v1(self)?,
            derive_global_carry_post_root_v1(self)?,
        ])
    }
}

impl<'de> Deserialize<'de> for CanonicalShardStateMapV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_inputs(
            <[ShardTransitionInputV1; PARALLEL_SHARD_COUNT_V1]>::deserialize(deserializer)?,
        )
        .map_err(de::Error::custom)
    }
}

fn validate_empty_roots(
    input: &ShardTransitionInputV1,
    shard_index: usize,
) -> Result<(), ParallelShardEpochErrorV1> {
    if input.cross_shard_outbox_root != canonical_empty_cross_shard_outbox_root_v1()? {
        return Err(ParallelShardEpochErrorV1::NonEmptyCrossShardOutbox { shard_index });
    }
    if input.cross_shard_inbox_root != canonical_empty_cross_shard_inbox_root_v1()? {
        return Err(ParallelShardEpochErrorV1::NonEmptyCrossShardInbox { shard_index });
    }
    if input.carry_queue_pre_root != canonical_empty_carry_queue_root_v1()? {
        return Err(ParallelShardEpochErrorV1::NonEmptyCarryQueuePre { shard_index });
    }
    if input.carry_queue_post_root != canonical_empty_carry_queue_root_v1()? {
        return Err(ParallelShardEpochErrorV1::NonEmptyCarryQueuePost { shard_index });
    }
    Ok(())
}

fn require_strictly_sorted(
    shard_ids: &[ShardIdV1; PARALLEL_SHARD_COUNT_V1],
) -> Result<(), ParallelShardEpochErrorV1> {
    if shard_ids[0] >= shard_ids[1] {
        return Err(ParallelShardEpochErrorV1::ShardIdsNotStrictlySorted);
    }
    Ok(())
}

fn require_common_context(
    entries: &[ShardTransitionV1; PARALLEL_SHARD_COUNT_V1],
) -> Result<(), ParallelShardEpochErrorV1> {
    let first = &entries[0];
    for (index, entry) in entries.iter().enumerate().skip(1) {
        if entry.scope_hash() != first.scope_hash() {
            return Err(ParallelShardEpochErrorV1::ScopeMismatch { shard_index: index });
        }
        if entry.semantic_profile_id() != first.semantic_profile_id() {
            return Err(ParallelShardEpochErrorV1::SemanticProfileMismatch { shard_index: index });
        }
        if entry.state_root_scheme_id() != first.state_root_scheme_id() {
            return Err(ParallelShardEpochErrorV1::StateRootSchemeMismatch { shard_index: index });
        }
    }
    Ok(())
}
