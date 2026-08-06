use core::fmt;

use crate::SparseMerkleCellTransitionErrorV1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LaneStateTransitionErrorV1 {
    SparseMerkleCell(SparseMerkleCellTransitionErrorV1),
    InvalidBatchVersion(u16),
    EmptyWitnesses,
    TooManyWitnesses { actual: usize, maximum: usize },
    EconomicActionMismatch { index: usize },
    DuplicateCellKey,
    NonCanonicalCellKeyOrder,
    BatchPreRootMismatch,
    RootChainDiscontinuity { index: usize },
    BatchPostRootMismatch,
    UnchangedBatchRoot,
    OpeningRootMismatch,
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl From<SparseMerkleCellTransitionErrorV1> for LaneStateTransitionErrorV1 {
    fn from(error: SparseMerkleCellTransitionErrorV1) -> Self {
        Self::SparseMerkleCell(error)
    }
}

impl fmt::Display for LaneStateTransitionErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SparseMerkleCell(error) => write!(formatter, "sparse Merkle cell: {error}"),
            Self::InvalidBatchVersion(version) => {
                write!(formatter, "invalid lane opening batch version: {version}")
            }
            Self::EmptyWitnesses => formatter.write_str("lane opening batch is empty"),
            Self::TooManyWitnesses { actual, maximum } => {
                write!(
                    formatter,
                    "lane opening witness count {actual} exceeds {maximum}"
                )
            }
            Self::EconomicActionMismatch { index } => {
                write!(formatter, "lane opening action mismatch at index {index}")
            }
            Self::DuplicateCellKey => formatter.write_str("duplicate lane opening cell key"),
            Self::NonCanonicalCellKeyOrder => {
                formatter.write_str("non-canonical lane opening cell-key order")
            }
            Self::BatchPreRootMismatch => formatter.write_str("lane opening pre-root mismatch"),
            Self::RootChainDiscontinuity { index } => {
                write!(formatter, "lane opening root chain breaks at index {index}")
            }
            Self::BatchPostRootMismatch => formatter.write_str("lane opening post-root mismatch"),
            Self::UnchangedBatchRoot => {
                formatter.write_str("changed lane opening has equal pre/post roots")
            }
            Self::OpeningRootMismatch => {
                formatter.write_str("lane opening root commitment mismatch")
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived commitment: {field}")
            }
            Self::EmptyInput => formatter.write_str("lane state transition input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "lane state transition input {actual} exceeds {maximum}"
                )
            }
            Self::PostcardDecode => formatter.write_str("lane state transition decode failed"),
            Self::TrailingBytes => formatter.write_str("lane state transition has trailing bytes"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("lane state transition encoding is not canonical")
            }
        }
    }
}
