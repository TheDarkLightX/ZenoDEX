use core::fmt;

use crate::{ValueNodeErrorV4, ZrpfErrorV3};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueAggregateErrorV5 {
    Structural(ZrpfErrorV3),
    Value(ValueNodeErrorV4),
    InvalidProposalVersion(u16),
    InvalidAggregateLevel(u8),
    EmptyChildren,
    TooManyChildren { actual: usize, maximum: usize },
    InvalidChildLevel { child: usize, actual: u8 },
    ChildPartitionGap { child: usize },
    ChildPartitionCoverageMismatch,
    DuplicateChildClaim,
    DuplicateChildJournal,
    ScopeHashMismatch,
    MultiEpochScope,
    CommitmentMismatch(&'static str),
    ArithmeticOverflow(&'static str),
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for ValueAggregateErrorV5 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Structural(error) => write!(formatter, "V5 structural value rejected: {error}"),
            Self::Value(error) => write!(formatter, "V5 semantic value rejected: {error}"),
            Self::InvalidProposalVersion(version) => {
                write!(formatter, "invalid V5 proposal version: {version}")
            }
            Self::InvalidAggregateLevel(level) => {
                write!(formatter, "invalid V5 aggregate level: {level}")
            }
            Self::EmptyChildren => formatter.write_str("V5 aggregate children are empty"),
            Self::TooManyChildren { actual, maximum } => {
                write!(formatter, "V5 child count {actual} exceeds {maximum}")
            }
            Self::InvalidChildLevel { child, actual } => {
                write!(formatter, "V5 child {child} has invalid level {actual}")
            }
            Self::ChildPartitionGap { child } => {
                write!(formatter, "V5 child {child} is not partition-contiguous")
            }
            Self::ChildPartitionCoverageMismatch => {
                formatter.write_str("V5 children do not cover the merged partition")
            }
            Self::DuplicateChildClaim => formatter.write_str("duplicate V5 child claim"),
            Self::DuplicateChildJournal => formatter.write_str("duplicate V5 child journal"),
            Self::ScopeHashMismatch => {
                formatter.write_str("V5 scope does not match semantic subtree scope")
            }
            Self::MultiEpochScope => {
                formatter.write_str("V5 value aggregate must represent exactly one epoch")
            }
            Self::CommitmentMismatch(field) => {
                write!(formatter, "V5 commitment mismatch: {field}")
            }
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "V5 arithmetic overflow: {field}")
            }
            Self::InputTooLarge { actual, maximum } => {
                write!(formatter, "V5 input length {actual} exceeds {maximum}")
            }
            Self::PostcardDecode => formatter.write_str("V5 postcard decode failed"),
            Self::TrailingBytes => formatter.write_str("V5 postcard input has trailing bytes"),
            Self::NonCanonicalEncoding => formatter.write_str("V5 postcard input is not canonical"),
        }
    }
}

impl From<ZrpfErrorV3> for ValueAggregateErrorV5 {
    fn from(error: ZrpfErrorV3) -> Self {
        Self::Structural(error)
    }
}

impl From<ValueNodeErrorV4> for ValueAggregateErrorV5 {
    fn from(error: ValueNodeErrorV4) -> Self {
        Self::Value(error)
    }
}
