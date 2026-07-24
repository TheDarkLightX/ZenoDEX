mod hash;
mod ids;
mod leaf;
mod proposal;
mod sets;

pub(crate) use proposal::{derive_semantic_epoch_root, SemanticRootInputV1};
pub(crate) use sets::{derive_epoch_commitments, validate_leaf_set};

use core::fmt;

pub use hash::{
    semantic_epoch_manifest_root_v1, semantic_epoch_profile_id_v1, v1_adapter_count_unit_id_v1,
    v1_adapter_manifest_root_v1, v1_adapter_profile_id_v1, v1_adapter_semantic_source_root_v1,
    v1_adapter_task_set_root_v1, v2_adapter_manifest_root_v2, v2_adapter_profile_id_v2,
    SemanticEpochDependencyProgramsInputV1, SemanticEpochDependencyProgramsV1,
};
pub use ids::{SemanticSourceIdV1, SourceClaimIdV1};
pub use leaf::{
    ExpectedV1AdapterLeafIdentityV1, ExpectedV2AdapterLeafIdentityV2, ProposedSemanticLeafV1,
    V1AdapterSemanticLeafOpeningV1, V2AdapterSemanticLeafOpeningV2,
};
pub use proposal::{
    decode_exact_semantic_epoch_proposal_v1, encode_semantic_epoch_proposal_v1,
    ProposedSemanticEpochV1, SemanticEpochCommitmentsV1, SemanticEpochProposalInputV1,
};

use super::ZrpfErrorV3;

pub const SEMANTIC_EPOCH_VERSION_V1: u16 = 1;
pub const MAX_SEMANTIC_EPOCH_PROPOSAL_BYTES_V1: usize = 4_096;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticEpochErrorV1 {
    Structural(ZrpfErrorV3),
    InvalidVersion(u16),
    InvalidSemanticProfile,
    LeafJournalRequired,
    EmptyLeaves,
    TooManyLeaves { actual: usize, maximum: usize },
    NonSingletonLeafPartition,
    InvalidLeafOperationCount,
    NonCanonicalLeafOrder,
    NonContiguousLeafPartitions,
    PartitionMustStartAtZero,
    ScopeMismatch,
    CountUnitMismatch,
    LeafProgramMismatch,
    LeafProfileMismatch,
    V1AdapterProfileMismatch,
    V1AdapterManifestMismatch,
    V1AdapterCountUnitMismatch,
    V1AdapterProvenanceMismatch,
    V1AdapterTaskSetMismatch,
    V1AdapterSemanticSourceMismatch,
    V1AdapterPartitionPlanMismatch,
    V1AdapterAuxiliarySetMustBeEmpty(&'static str),
    V1AdapterStatementMismatch,
    V2AdapterProfileMismatch,
    V2AdapterManifestMismatch,
    V2AdapterCountUnitMismatch,
    V2AdapterProvenanceMismatch,
    V2AdapterTaskSetMismatch,
    V2AdapterSemanticSourceMismatch,
    V2AdapterPartitionPlanMismatch,
    V2AdapterAuxiliarySetMustBeEmpty(&'static str),
    V2AdapterStatementMismatch,
    DuplicateSourceClaim,
    DuplicateSemanticSource,
    DuplicateTask,
    ArithmeticOverflow(&'static str),
    InvalidProposalShape,
    SemanticRootMismatch,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl From<ZrpfErrorV3> for SemanticEpochErrorV1 {
    fn from(error: ZrpfErrorV3) -> Self {
        Self::Structural(error)
    }
}

impl fmt::Display for SemanticEpochErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Structural(error) => write!(formatter, "structural journal rejected: {error}"),
            Self::InvalidVersion(version) => {
                write!(formatter, "invalid semantic version: {version}")
            }
            Self::InvalidSemanticProfile => {
                formatter.write_str("semantic profile is not the V1 adapter compatibility profile")
            }
            Self::LeafJournalRequired => {
                formatter.write_str("semantic record requires a leaf journal")
            }
            Self::EmptyLeaves => formatter.write_str("semantic epoch has no leaves"),
            Self::TooManyLeaves { actual, maximum } => {
                write!(formatter, "semantic leaf count {actual} exceeds {maximum}")
            }
            Self::NonSingletonLeafPartition => {
                formatter.write_str("semantic leaves require singleton partitions")
            }
            Self::InvalidLeafOperationCount => {
                formatter.write_str("V1 adapter semantic leaves require one operation")
            }
            Self::NonCanonicalLeafOrder => {
                formatter.write_str("semantic leaves are not canonically ordered")
            }
            Self::NonContiguousLeafPartitions => {
                formatter.write_str("semantic leaf partitions are not contiguous")
            }
            Self::PartitionMustStartAtZero => {
                formatter.write_str("semantic epoch partition must start at zero")
            }
            Self::ScopeMismatch => {
                formatter.write_str("semantic leaf scope differs from epoch scope")
            }
            Self::CountUnitMismatch => formatter.write_str("semantic leaf count unit differs"),
            Self::LeafProgramMismatch => {
                formatter.write_str("semantic leaves use different adapter programs")
            }
            Self::LeafProfileMismatch => {
                formatter.write_str("semantic leaves use different adapter profiles")
            }
            Self::V1AdapterProfileMismatch => {
                formatter.write_str("leaf does not use the exact V1 adapter profile")
            }
            Self::V1AdapterManifestMismatch => {
                formatter.write_str("leaf V1 adapter manifest root is invalid")
            }
            Self::V1AdapterCountUnitMismatch => {
                formatter.write_str("leaf V1 adapter count unit is invalid")
            }
            Self::V1AdapterProvenanceMismatch => {
                formatter.write_str("leaf V1 adapter provenance opening is invalid")
            }
            Self::V1AdapterTaskSetMismatch => {
                formatter.write_str("leaf V1 adapter task-set opening is invalid")
            }
            Self::V1AdapterSemanticSourceMismatch => {
                formatter.write_str("leaf V1 adapter semantic-source opening is invalid")
            }
            Self::V1AdapterPartitionPlanMismatch => {
                formatter.write_str("leaf V1 adapter partition-plan opening is invalid")
            }
            Self::V1AdapterAuxiliarySetMustBeEmpty(field) => {
                write!(
                    formatter,
                    "leaf V1 adapter {field} must be the canonical empty root"
                )
            }
            Self::V1AdapterStatementMismatch => {
                formatter.write_str("leaf V1 adapter statement is invalid")
            }
            Self::V2AdapterProfileMismatch => {
                formatter.write_str("leaf does not use the exact V2 adapter profile")
            }
            Self::V2AdapterManifestMismatch => {
                formatter.write_str("leaf V2 adapter manifest root is invalid")
            }
            Self::V2AdapterCountUnitMismatch => {
                formatter.write_str("leaf V2 adapter count unit is invalid")
            }
            Self::V2AdapterProvenanceMismatch => {
                formatter.write_str("leaf V2 adapter provenance opening is invalid")
            }
            Self::V2AdapterTaskSetMismatch => {
                formatter.write_str("leaf V2 adapter task-set opening is invalid")
            }
            Self::V2AdapterSemanticSourceMismatch => {
                formatter.write_str("leaf V2 adapter semantic-source opening is invalid")
            }
            Self::V2AdapterPartitionPlanMismatch => {
                formatter.write_str("leaf V2 adapter partition-plan opening is invalid")
            }
            Self::V2AdapterAuxiliarySetMustBeEmpty(field) => {
                write!(
                    formatter,
                    "leaf V2 adapter {field} must be the canonical empty root"
                )
            }
            Self::V2AdapterStatementMismatch => {
                formatter.write_str("leaf V2 adapter statement is invalid")
            }
            Self::DuplicateSourceClaim => formatter.write_str("duplicate semantic source claim"),
            Self::DuplicateSemanticSource => {
                formatter.write_str("duplicate semantic source identity")
            }
            Self::DuplicateTask => formatter.write_str("duplicate semantic task"),
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidProposalShape => {
                formatter.write_str("invalid semantic epoch proposal shape")
            }
            Self::SemanticRootMismatch => formatter.write_str("semantic epoch root mismatch"),
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "semantic input length {actual} exceeds {maximum}"
                )
            }
            Self::PostcardDecode => formatter.write_str("semantic postcard decode failed"),
            Self::TrailingBytes => {
                formatter.write_str("semantic postcard input has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("semantic postcard input is not canonical")
            }
        }
    }
}
