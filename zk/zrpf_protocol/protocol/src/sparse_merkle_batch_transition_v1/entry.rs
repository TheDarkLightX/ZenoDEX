use serde::{de, Deserialize, Deserializer, Serialize};

use super::SparseMerkleBatchTransitionErrorV1;
use crate::{
    bind_sparse_merkle_cell_transition_v1, CommitmentV3, EconomicActionIdV1, LedgerCellWriteV2,
    SparseMerkleCellTransitionWitnessV1,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseMerkleBatchEntryInputV1 {
    pub cell_write: LedgerCellWriteV2,
    pub witness: SparseMerkleCellTransitionWitnessV1,
}

/// One exact write/witness pair in the chained V1 profile.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SparseMerkleBatchEntryV1 {
    cell_write: LedgerCellWriteV2,
    witness: SparseMerkleCellTransitionWitnessV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SparseMerkleBatchEntryWireV1 {
    cell_write: LedgerCellWriteV2,
    witness: SparseMerkleCellTransitionWitnessV1,
}

impl SparseMerkleBatchEntryV1 {
    pub fn new(
        input: SparseMerkleBatchEntryInputV1,
    ) -> Result<Self, SparseMerkleBatchTransitionErrorV1> {
        bind_sparse_merkle_cell_transition_v1(&input.witness, &input.cell_write)?;
        Ok(Self {
            cell_write: input.cell_write,
            witness: input.witness,
        })
    }

    pub fn validate_self_consistency(&self) -> Result<(), SparseMerkleBatchTransitionErrorV1> {
        bind_sparse_merkle_cell_transition_v1(&self.witness, &self.cell_write)?;
        Ok(())
    }

    /// V1 permits one cell write per economic action, so the action ID is the
    /// batch write identity.
    pub const fn write_id(&self) -> EconomicActionIdV1 {
        self.cell_write.economic_action_id()
    }

    pub const fn cell_key(&self) -> CommitmentV3 {
        self.cell_write.cell_key()
    }

    pub const fn cell_write(&self) -> &LedgerCellWriteV2 {
        &self.cell_write
    }

    pub const fn witness(&self) -> &SparseMerkleCellTransitionWitnessV1 {
        &self.witness
    }
}

impl<'de> Deserialize<'de> for SparseMerkleBatchEntryV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = SparseMerkleBatchEntryWireV1::deserialize(deserializer)?;
        Self::new(SparseMerkleBatchEntryInputV1 {
            cell_write: wire.cell_write,
            witness: wire.witness,
        })
        .map_err(de::Error::custom)
    }
}
