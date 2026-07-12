use core::fmt;

use crate::SparseMerkleCellTransitionErrorV1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SparseMerkleBatchTransitionErrorV1 {
    CellTransition(SparseMerkleCellTransitionErrorV1),
    InvalidBatchVersion(u16),
    EmptyBatch,
    TooManyEntries { actual: usize, maximum: usize },
    DuplicateCellKey,
    NonCanonicalCellKeyOrder,
    DuplicateWriteId,
    BatchPreRootMismatch,
    RootChainDiscontinuity { index: usize },
    BatchPostRootMismatch,
    ArithmeticOverflow(&'static str),
    AllocationFailed(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl From<SparseMerkleCellTransitionErrorV1> for SparseMerkleBatchTransitionErrorV1 {
    fn from(error: SparseMerkleCellTransitionErrorV1) -> Self {
        Self::CellTransition(error)
    }
}

impl fmt::Display for SparseMerkleBatchTransitionErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CellTransition(error) => {
                write!(formatter, "single-cell witness rejected: {error}")
            }
            Self::InvalidBatchVersion(version) => {
                write!(formatter, "invalid sparse-Merkle batch version: {version}")
            }
            Self::EmptyBatch => formatter.write_str("sparse-Merkle batch is empty"),
            Self::TooManyEntries { actual, maximum } => write!(
                formatter,
                "sparse-Merkle batch entry count {actual} exceeds {maximum}"
            ),
            Self::DuplicateCellKey => {
                formatter.write_str("sparse-Merkle batch contains a duplicate cell key")
            }
            Self::NonCanonicalCellKeyOrder => {
                formatter.write_str("sparse-Merkle batch cell keys are not strictly increasing")
            }
            Self::DuplicateWriteId => {
                formatter.write_str("sparse-Merkle batch reuses one economic action as a write ID")
            }
            Self::BatchPreRootMismatch => {
                formatter.write_str("batch pre-root differs from the first witness pre-root")
            }
            Self::RootChainDiscontinuity { index } => write!(
                formatter,
                "witness pre-root at batch index {index} differs from the prior post-root"
            ),
            Self::BatchPostRootMismatch => {
                formatter.write_str("batch post-root differs from the final witness post-root")
            }
            Self::ArithmeticOverflow(field) => {
                write!(
                    formatter,
                    "sparse-Merkle batch arithmetic overflow: {field}"
                )
            }
            Self::AllocationFailed(field) => {
                write!(
                    formatter,
                    "bounded sparse-Merkle allocation failed: {field}"
                )
            }
            Self::EmptyInput => formatter.write_str("sparse-Merkle batch input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "sparse-Merkle batch input length {actual} exceeds {maximum}"
            ),
            Self::PostcardDecode => {
                formatter.write_str("sparse-Merkle batch Postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("sparse-Merkle batch contains trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("sparse-Merkle batch encoding is not canonical")
            }
        }
    }
}
