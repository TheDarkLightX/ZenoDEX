use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};

use super::bounded::{deserialize_batch_entries, require_entry_count};
use super::{
    SparseMerkleBatchEntryV1, SparseMerkleBatchTransitionErrorV1, SPARSE_MERKLE_BATCH_VERSION_V1,
};
use crate::CommitmentV3;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseMerkleBatchTransitionInputV1 {
    pub batch_version: u16,
    pub entries: Vec<SparseMerkleBatchEntryV1>,
    pub batch_pre_root: CommitmentV3,
    pub batch_post_root: CommitmentV3,
}

/// Closed proof-neutral typestate for one canonical chain of cell witnesses.
///
/// Every entry binds one exact `LedgerCellWriteV2`, keys are strictly
/// increasing, write IDs are unique, and adjacent roots are continuous. This
/// type carries no receipt, settlement, persistence, or ledger authority.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ValidatedSparseMerkleBatchTransitionV1;
/// let batch: ValidatedSparseMerkleBatchTransitionV1 = unimplemented!();
/// let _ = batch.ledger_authority();
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ValidatedSparseMerkleBatchTransitionV1;
/// let _ = ValidatedSparseMerkleBatchTransitionV1 {};
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ValidatedSparseMerkleBatchTransitionV1 {
    batch_version: u16,
    entries: Vec<SparseMerkleBatchEntryV1>,
    batch_pre_root: CommitmentV3,
    batch_post_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SparseMerkleBatchTransitionWireV1 {
    batch_version: u16,
    #[serde(deserialize_with = "deserialize_batch_entries")]
    entries: Vec<SparseMerkleBatchEntryV1>,
    batch_pre_root: CommitmentV3,
    batch_post_root: CommitmentV3,
}

impl ValidatedSparseMerkleBatchTransitionV1 {
    pub fn new(
        input: SparseMerkleBatchTransitionInputV1,
    ) -> Result<Self, SparseMerkleBatchTransitionErrorV1> {
        let batch = Self {
            batch_version: input.batch_version,
            entries: input.entries,
            batch_pre_root: input.batch_pre_root,
            batch_post_root: input.batch_post_root,
        };
        batch.validate_self_consistency()?;
        Ok(batch)
    }

    pub fn validate_self_consistency(&self) -> Result<(), SparseMerkleBatchTransitionErrorV1> {
        if self.batch_version != SPARSE_MERKLE_BATCH_VERSION_V1 {
            return Err(SparseMerkleBatchTransitionErrorV1::InvalidBatchVersion(
                self.batch_version,
            ));
        }
        require_entry_count(self.entries.len())?;
        // Entry fields are private and both public construction and decoding
        // produce an exact write/witness binding before this typestate exists.
        validate_key_order(&self.entries)?;
        validate_unique_write_ids(&self.entries)?;
        let first = self
            .entries
            .first()
            .ok_or(SparseMerkleBatchTransitionErrorV1::EmptyBatch)?;
        if first.witness().claimed_pre_root() != self.batch_pre_root {
            return Err(SparseMerkleBatchTransitionErrorV1::BatchPreRootMismatch);
        }
        for (offset, pair) in self.entries.windows(2).enumerate() {
            if pair[1].witness().claimed_pre_root() != pair[0].witness().claimed_post_root() {
                let index = offset.checked_add(1).ok_or(
                    SparseMerkleBatchTransitionErrorV1::ArithmeticOverflow("root_chain_index"),
                )?;
                return Err(SparseMerkleBatchTransitionErrorV1::RootChainDiscontinuity { index });
            }
        }
        let last = self
            .entries
            .last()
            .ok_or(SparseMerkleBatchTransitionErrorV1::EmptyBatch)?;
        if last.witness().claimed_post_root() != self.batch_post_root {
            return Err(SparseMerkleBatchTransitionErrorV1::BatchPostRootMismatch);
        }
        Ok(())
    }

    pub const fn batch_version(&self) -> u16 {
        self.batch_version
    }

    pub fn entries(&self) -> &[SparseMerkleBatchEntryV1] {
        &self.entries
    }

    pub const fn batch_pre_root(&self) -> CommitmentV3 {
        self.batch_pre_root
    }

    pub const fn batch_post_root(&self) -> CommitmentV3 {
        self.batch_post_root
    }
}

fn validate_key_order(
    entries: &[SparseMerkleBatchEntryV1],
) -> Result<(), SparseMerkleBatchTransitionErrorV1> {
    for pair in entries.windows(2) {
        if pair[0].cell_key() == pair[1].cell_key() {
            return Err(SparseMerkleBatchTransitionErrorV1::DuplicateCellKey);
        }
        if pair[0].cell_key() > pair[1].cell_key() {
            return Err(SparseMerkleBatchTransitionErrorV1::NonCanonicalCellKeyOrder);
        }
    }
    Ok(())
}

fn validate_unique_write_ids(
    entries: &[SparseMerkleBatchEntryV1],
) -> Result<(), SparseMerkleBatchTransitionErrorV1> {
    for (index, entry) in entries.iter().enumerate() {
        if entries[..index]
            .iter()
            .any(|prior| prior.write_id() == entry.write_id())
        {
            return Err(SparseMerkleBatchTransitionErrorV1::DuplicateWriteId);
        }
    }
    Ok(())
}

impl<'de> Deserialize<'de> for ValidatedSparseMerkleBatchTransitionV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = SparseMerkleBatchTransitionWireV1::deserialize(deserializer)?;
        Self::new(SparseMerkleBatchTransitionInputV1 {
            batch_version: wire.batch_version,
            entries: wire.entries,
            batch_pre_root: wire.batch_pre_root,
            batch_post_root: wire.batch_post_root,
        })
        .map_err(de::Error::custom)
    }
}
