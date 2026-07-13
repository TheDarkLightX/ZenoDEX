use serde::{de, Deserialize, Deserializer, Serialize};

use super::{
    derive_sparse_merkle_root_v1, SparseMerkleCellTransitionErrorV1, SparseMerkleSiblingPathV1,
    SPARSE_MERKLE_WITNESS_VERSION_V1,
};
use crate::{CommitmentV3, EconomicActionIdV1, ValueHashV2};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseMerkleCellTransitionWitnessInputV1 {
    pub witness_version: u16,
    pub economic_action_id: EconomicActionIdV1,
    pub cell_key: CommitmentV3,
    pub pre_value_hash: ValueHashV2,
    pub post_value_hash: ValueHashV2,
    pub sibling_commitments: SparseMerkleSiblingPathV1,
    pub claimed_pre_root: CommitmentV3,
    pub claimed_post_root: CommitmentV3,
}

/// Validated one-cell sparse-Merkle transition witness.
///
/// The private fields can only be populated after both supplied roots are
/// derived from the same fixed path. This is a proof-neutral witness object. It
/// supplies no receipt, multi-write, settlement, or ledger authority.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::SparseMerkleCellTransitionWitnessV1;
/// let witness: SparseMerkleCellTransitionWitnessV1 = unimplemented!();
/// let _ = witness.receipt_authority();
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SparseMerkleCellTransitionWitnessV1 {
    witness_version: u16,
    economic_action_id: EconomicActionIdV1,
    cell_key: CommitmentV3,
    pre_value_hash: ValueHashV2,
    post_value_hash: ValueHashV2,
    sibling_commitments: SparseMerkleSiblingPathV1,
    claimed_pre_root: CommitmentV3,
    claimed_post_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SparseMerkleCellTransitionWitnessWireV1 {
    witness_version: u16,
    economic_action_id: EconomicActionIdV1,
    cell_key: CommitmentV3,
    pre_value_hash: ValueHashV2,
    post_value_hash: ValueHashV2,
    sibling_commitments: SparseMerkleSiblingPathV1,
    claimed_pre_root: CommitmentV3,
    claimed_post_root: CommitmentV3,
}

impl SparseMerkleCellTransitionWitnessV1 {
    pub fn new(
        input: SparseMerkleCellTransitionWitnessInputV1,
    ) -> Result<Self, SparseMerkleCellTransitionErrorV1> {
        let witness = Self {
            witness_version: input.witness_version,
            economic_action_id: input.economic_action_id,
            cell_key: input.cell_key,
            pre_value_hash: input.pre_value_hash,
            post_value_hash: input.post_value_hash,
            sibling_commitments: input.sibling_commitments,
            claimed_pre_root: input.claimed_pre_root,
            claimed_post_root: input.claimed_post_root,
        };
        witness.validate_self_consistency()?;
        Ok(witness)
    }

    pub fn validate_self_consistency(&self) -> Result<(), SparseMerkleCellTransitionErrorV1> {
        if self.witness_version != SPARSE_MERKLE_WITNESS_VERSION_V1 {
            return Err(SparseMerkleCellTransitionErrorV1::InvalidWitnessVersion(
                self.witness_version,
            ));
        }
        if self.pre_value_hash == self.post_value_hash {
            return Err(SparseMerkleCellTransitionErrorV1::UnchangedValue);
        }
        let derived_pre = derive_sparse_merkle_root_v1(
            self.cell_key,
            self.pre_value_hash,
            &self.sibling_commitments,
        )?;
        if derived_pre != self.claimed_pre_root {
            return Err(SparseMerkleCellTransitionErrorV1::ClaimedPreRootMismatch);
        }
        let derived_post = derive_sparse_merkle_root_v1(
            self.cell_key,
            self.post_value_hash,
            &self.sibling_commitments,
        )?;
        if derived_post != self.claimed_post_root {
            return Err(SparseMerkleCellTransitionErrorV1::ClaimedPostRootMismatch);
        }
        Ok(())
    }

    pub const fn witness_version(&self) -> u16 {
        self.witness_version
    }

    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.economic_action_id
    }

    pub const fn cell_key(&self) -> CommitmentV3 {
        self.cell_key
    }

    pub const fn pre_value_hash(&self) -> ValueHashV2 {
        self.pre_value_hash
    }

    pub const fn post_value_hash(&self) -> ValueHashV2 {
        self.post_value_hash
    }

    pub const fn sibling_commitments(&self) -> &SparseMerkleSiblingPathV1 {
        &self.sibling_commitments
    }

    pub const fn claimed_pre_root(&self) -> CommitmentV3 {
        self.claimed_pre_root
    }

    pub const fn claimed_post_root(&self) -> CommitmentV3 {
        self.claimed_post_root
    }
}

impl<'de> Deserialize<'de> for SparseMerkleCellTransitionWitnessV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = SparseMerkleCellTransitionWitnessWireV1::deserialize(deserializer)?;
        Self::new(SparseMerkleCellTransitionWitnessInputV1 {
            witness_version: wire.witness_version,
            economic_action_id: wire.economic_action_id,
            cell_key: wire.cell_key,
            pre_value_hash: wire.pre_value_hash,
            post_value_hash: wire.post_value_hash,
            sibling_commitments: wire.sibling_commitments,
            claimed_pre_root: wire.claimed_pre_root,
            claimed_post_root: wire.claimed_post_root,
        })
        .map_err(de::Error::custom)
    }
}
