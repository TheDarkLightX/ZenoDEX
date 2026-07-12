use serde::{de, Deserialize, Deserializer, Serialize};

use super::hash::child_descriptor_hash_v5;
use super::ValueAggregateErrorV5;
use crate::{CommitmentV3, PartitionV3, ProfileIdV3, ProgramIdV3, MAX_NODE_LEVEL_V3};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueAggregateChildDescriptorInputV5 {
    pub child_level: u8,
    pub partition: PartitionV3,
    pub verified_program_id: ProgramIdV3,
    pub proof_profile_id: ProfileIdV3,
    pub program_manifest_root: CommitmentV3,
    pub journal_hash: CommitmentV3,
    pub claim_binding: CommitmentV3,
    pub semantic_subtree_root: CommitmentV3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
/// Proof-neutral projection of one child authenticated by a future guest.
///
/// Construction validates shape only. A caller cannot convert this value into
/// a verified receipt or a ledger capability.
pub struct ValueAggregateChildDescriptorV5 {
    child_level: u8,
    partition: PartitionV3,
    verified_program_id: ProgramIdV3,
    proof_profile_id: ProfileIdV3,
    program_manifest_root: CommitmentV3,
    journal_hash: CommitmentV3,
    claim_binding: CommitmentV3,
    semantic_subtree_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ValueAggregateChildDescriptorWireV5 {
    child_level: u8,
    partition: PartitionV3,
    verified_program_id: ProgramIdV3,
    proof_profile_id: ProfileIdV3,
    program_manifest_root: CommitmentV3,
    journal_hash: CommitmentV3,
    claim_binding: CommitmentV3,
    semantic_subtree_root: CommitmentV3,
}

impl ValueAggregateChildDescriptorV5 {
    pub fn new(input: ValueAggregateChildDescriptorInputV5) -> Result<Self, ValueAggregateErrorV5> {
        if input.child_level >= MAX_NODE_LEVEL_V3 {
            return Err(ValueAggregateErrorV5::InvalidAggregateLevel(
                input.child_level,
            ));
        }
        let descriptor = Self {
            child_level: input.child_level,
            partition: input.partition,
            verified_program_id: input.verified_program_id,
            proof_profile_id: input.proof_profile_id,
            program_manifest_root: input.program_manifest_root,
            journal_hash: input.journal_hash,
            claim_binding: input.claim_binding,
            semantic_subtree_root: input.semantic_subtree_root,
        };
        descriptor.validate()?;
        Ok(descriptor)
    }

    pub fn validate(&self) -> Result<(), ValueAggregateErrorV5> {
        if self.child_level >= MAX_NODE_LEVEL_V3 {
            return Err(ValueAggregateErrorV5::InvalidAggregateLevel(
                self.child_level,
            ));
        }
        Ok(())
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, ValueAggregateErrorV5> {
        self.validate()?;
        child_descriptor_hash_v5(self)
    }

    pub const fn child_level(&self) -> u8 {
        self.child_level
    }

    pub const fn partition(&self) -> PartitionV3 {
        self.partition
    }

    pub const fn verified_program_id(&self) -> ProgramIdV3 {
        self.verified_program_id
    }

    pub const fn proof_profile_id(&self) -> ProfileIdV3 {
        self.proof_profile_id
    }

    pub const fn program_manifest_root(&self) -> CommitmentV3 {
        self.program_manifest_root
    }

    pub const fn journal_hash(&self) -> CommitmentV3 {
        self.journal_hash
    }

    pub const fn claim_binding(&self) -> CommitmentV3 {
        self.claim_binding
    }

    pub const fn semantic_subtree_root(&self) -> CommitmentV3 {
        self.semantic_subtree_root
    }
}

impl<'de> Deserialize<'de> for ValueAggregateChildDescriptorV5 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ValueAggregateChildDescriptorWireV5::deserialize(deserializer)?;
        Self::new(ValueAggregateChildDescriptorInputV5 {
            child_level: wire.child_level,
            partition: wire.partition,
            verified_program_id: wire.verified_program_id,
            proof_profile_id: wire.proof_profile_id,
            program_manifest_root: wire.program_manifest_root,
            journal_hash: wire.journal_hash,
            claim_binding: wire.claim_binding,
            semantic_subtree_root: wire.semantic_subtree_root,
        })
        .map_err(de::Error::custom)
    }
}
