use serde::{de, Deserialize, Deserializer, Serialize};

use super::hash::{
    derive_proposal_hash_v1, derive_semantic_epoch_root_v1, SemanticEpochRootInputV1,
};
use super::{
    CanonicalShardStateMapV1, DeclaredShardSetV1, ParallelShardEpochErrorV1,
    ShardCompositionContextV1, ShardIdV1, ShardTransitionInputV1, PARALLEL_SHARD_COUNT_V1,
    PARALLEL_SHARD_EPOCH_VERSION_V1,
};
use crate::{CommitmentV3, NodeScopeV3, ProfileIdV3};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParallelShardEpochInputV1 {
    pub scope: NodeScopeV3,
    pub semantic_profile_id: ProfileIdV3,
    pub state_root_scheme_id: CommitmentV3,
    pub declared_shard_ids: [ShardIdV1; PARALLEL_SHARD_COUNT_V1],
    pub shard_transitions: [ShardTransitionInputV1; PARALLEL_SHARD_COUNT_V1],
    pub proof_tree_root: CommitmentV3,
}

/// Proof-neutral two-shard semantic proposal.
///
/// `semantic_epoch_root` excludes `proof_tree_root`, so valid proof grouping
/// changes cannot alter semantic identity. `proposal_hash` binds both roots.
/// This type verifies no receipt, message cancellation, nullifier disjointness,
/// data availability, finality, governance or release authority, ledger commit,
/// settlement, or privacy claim.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ParallelShardEpochV1;
/// let epoch: ParallelShardEpochV1 = unimplemented!();
/// let _ = epoch.verified_program_id();
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ParallelShardEpochV1 {
    epoch_version: u16,
    scope: NodeScopeV3,
    semantic_profile_id: ProfileIdV3,
    state_root_scheme_id: CommitmentV3,
    declared_shard_set: DeclaredShardSetV1,
    shard_state_map: CanonicalShardStateMapV1,
    proof_tree_root: CommitmentV3,
    semantic_epoch_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ParallelShardEpochWireV1 {
    epoch_version: u16,
    scope: NodeScopeV3,
    semantic_profile_id: ProfileIdV3,
    state_root_scheme_id: CommitmentV3,
    declared_shard_set: DeclaredShardSetV1,
    shard_state_map: CanonicalShardStateMapV1,
    proof_tree_root: CommitmentV3,
    semantic_epoch_root: CommitmentV3,
}

impl ParallelShardEpochV1 {
    pub fn derive(input: ParallelShardEpochInputV1) -> Result<Self, ParallelShardEpochErrorV1> {
        let scope_hash = input.scope.canonical_hash()?;
        let declared_shard_set = DeclaredShardSetV1::new(input.declared_shard_ids)?;
        let shard_state_map = CanonicalShardStateMapV1::new(
            &declared_shard_set,
            ShardCompositionContextV1::new(
                scope_hash,
                input.semantic_profile_id,
                input.state_root_scheme_id,
            ),
            input.shard_transitions,
        )?;
        let semantic_epoch_root = derive_semantic_epoch_root_v1(SemanticEpochRootInputV1 {
            scope: &input.scope,
            semantic_profile_id: input.semantic_profile_id,
            state_root_scheme_id: input.state_root_scheme_id,
            declared_shard_set: &declared_shard_set,
            state_map: &shard_state_map,
        })?;
        let epoch = Self {
            epoch_version: PARALLEL_SHARD_EPOCH_VERSION_V1,
            scope: input.scope,
            semantic_profile_id: input.semantic_profile_id,
            state_root_scheme_id: input.state_root_scheme_id,
            declared_shard_set,
            shard_state_map,
            proof_tree_root: input.proof_tree_root,
            semantic_epoch_root,
        };
        epoch.validate()?;
        Ok(epoch)
    }

    pub fn validate(&self) -> Result<(), ParallelShardEpochErrorV1> {
        if self.epoch_version != PARALLEL_SHARD_EPOCH_VERSION_V1 {
            return Err(ParallelShardEpochErrorV1::InvalidVersion(
                self.epoch_version,
            ));
        }
        self.scope.validate()?;
        self.declared_shard_set.validate()?;
        self.shard_state_map.validate_against(
            &self.declared_shard_set,
            ShardCompositionContextV1::new(
                self.scope.canonical_hash()?,
                self.semantic_profile_id,
                self.state_root_scheme_id,
            ),
        )?;
        let expected = derive_semantic_epoch_root_v1(SemanticEpochRootInputV1 {
            scope: &self.scope,
            semantic_profile_id: self.semantic_profile_id,
            state_root_scheme_id: self.state_root_scheme_id,
            declared_shard_set: &self.declared_shard_set,
            state_map: &self.shard_state_map,
        })?;
        if self.semantic_epoch_root != expected {
            return Err(ParallelShardEpochErrorV1::SemanticEpochRootMismatch);
        }
        Ok(())
    }

    pub fn proposal_hash(&self) -> Result<CommitmentV3, ParallelShardEpochErrorV1> {
        self.validate()?;
        derive_proposal_hash_v1(self.semantic_epoch_root, self.proof_tree_root)
    }

    pub const fn epoch_version(&self) -> u16 {
        self.epoch_version
    }

    pub const fn scope(&self) -> &NodeScopeV3 {
        &self.scope
    }

    pub const fn semantic_profile_id(&self) -> ProfileIdV3 {
        self.semantic_profile_id
    }

    pub const fn state_root_scheme_id(&self) -> CommitmentV3 {
        self.state_root_scheme_id
    }

    /// Returns the proposal-declared set. External policy must authenticate it.
    pub const fn declared_shard_set(&self) -> &DeclaredShardSetV1 {
        &self.declared_shard_set
    }

    pub const fn shard_state_map(&self) -> &CanonicalShardStateMapV1 {
        &self.shard_state_map
    }

    pub const fn proof_tree_root(&self) -> CommitmentV3 {
        self.proof_tree_root
    }

    pub const fn semantic_epoch_root(&self) -> CommitmentV3 {
        self.semantic_epoch_root
    }

    fn from_wire(wire: ParallelShardEpochWireV1) -> Result<Self, ParallelShardEpochErrorV1> {
        let epoch = Self {
            epoch_version: wire.epoch_version,
            scope: wire.scope,
            semantic_profile_id: wire.semantic_profile_id,
            state_root_scheme_id: wire.state_root_scheme_id,
            declared_shard_set: wire.declared_shard_set,
            shard_state_map: wire.shard_state_map,
            proof_tree_root: wire.proof_tree_root,
            semantic_epoch_root: wire.semantic_epoch_root,
        };
        epoch.validate()?;
        Ok(epoch)
    }
}

impl<'de> Deserialize<'de> for ParallelShardEpochV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_wire(ParallelShardEpochWireV1::deserialize(deserializer)?)
            .map_err(de::Error::custom)
    }
}
