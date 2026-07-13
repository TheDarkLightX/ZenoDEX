mod hash;
mod proposal;

use core::fmt;

pub use hash::semantic_epoch_dependency_manifest_root_v2;
pub use proposal::{
    decode_exact_semantic_epoch_proposal_v2, encode_semantic_epoch_proposal_v2,
    ProposedSemanticEpochV2, SemanticEpochProposalInputV2,
};

use super::{SemanticEpochErrorV1, ZrpfErrorV3};

pub const SEMANTIC_EPOCH_PROPOSAL_SCHEMA_VERSION_V2: u16 = 2;
pub const MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V2: usize = 4_096;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticEpochErrorV2 {
    Core(SemanticEpochErrorV1),
    Structural(ZrpfErrorV3),
    InvalidProposalSchema(u16),
    InvalidSemanticStatementVersion(u16),
    InvalidSemanticProfile,
    InvalidProposalShape,
    SemanticRootMismatch,
    ArithmeticOverflow(&'static str),
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl From<SemanticEpochErrorV1> for SemanticEpochErrorV2 {
    fn from(error: SemanticEpochErrorV1) -> Self {
        Self::Core(error)
    }
}

impl From<ZrpfErrorV3> for SemanticEpochErrorV2 {
    fn from(error: ZrpfErrorV3) -> Self {
        Self::Structural(error)
    }
}

impl fmt::Display for SemanticEpochErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Core(error) => write!(formatter, "semantic statement rejected: {error}"),
            Self::Structural(error) => write!(formatter, "structural value rejected: {error}"),
            Self::InvalidProposalSchema(version) => {
                write!(formatter, "invalid semantic proposal schema: {version}")
            }
            Self::InvalidSemanticStatementVersion(version) => {
                write!(formatter, "invalid semantic statement version: {version}")
            }
            Self::InvalidSemanticProfile => {
                formatter.write_str("semantic profile is not the V1 adapter compatibility profile")
            }
            Self::InvalidProposalShape => {
                formatter.write_str("invalid semantic epoch V2 proposal shape")
            }
            Self::SemanticRootMismatch => formatter.write_str("semantic epoch V2 root mismatch"),
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "semantic V2 input length {actual} exceeds {maximum}"
                )
            }
            Self::PostcardDecode => formatter.write_str("semantic V2 postcard decode failed"),
            Self::TrailingBytes => {
                formatter.write_str("semantic V2 postcard input has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("semantic V2 postcard input is not canonical")
            }
        }
    }
}
