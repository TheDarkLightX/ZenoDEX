use core::fmt;

use super::super::ZrpfErrorV3;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueNodeErrorV4 {
    InvalidSemanticSubtreeVersion(u16),
    InvalidNodeJournalVersion(u16),
    EmptyLeafRecords,
    TooManyLeafRecords {
        actual: usize,
        maximum: usize,
    },
    LeafCountMismatch,
    SubtreePartitionMismatch,
    NonSingletonLeafRecord {
        ordinal: usize,
    },
    NonCanonicalLeafOrder {
        ordinal: usize,
    },
    DuplicateSourceClaim,
    DuplicateSemanticSource,
    DuplicateTask,
    DuplicateTransactionRoot,
    StateDiscontinuity {
        ordinal: usize,
    },
    SubtreeEndpointMismatch,
    RepresentedRowLimitExceeded {
        actual: u64,
        maximum: u64,
    },
    InvalidRepresentedRowShape,
    TooManyAssetFlows {
        actual: usize,
        maximum: usize,
    },
    InvalidAssetFlow,
    NonCanonicalAssetFlowOrder,
    TooManyAuthorityUses {
        actual: usize,
        maximum: usize,
    },
    InvalidAuthorityUse,
    NonCanonicalAuthorityUseOrder,
    AuthorityUseOutsidePartition,
    AuthorityUseSourceMismatch,
    IssuanceUseMismatch,
    EmptySemanticChildren,
    TooManySemanticChildren {
        actual: usize,
        maximum: usize,
    },
    SemanticChildMetadataMismatch {
        child: usize,
        field: &'static str,
    },
    NonCanonicalSemanticChildOrder {
        child: usize,
    },
    SemanticChildStateDiscontinuity {
        child: usize,
    },
    SemanticMergeLimitExceeded {
        field: &'static str,
        actual: usize,
        maximum: usize,
    },
    CommitmentMismatch(&'static str),
    StructuralPartitionMismatch,
    StructuralLeafCountMismatch,
    StructuralScopeMismatch,
    InvalidChildSemanticJournalCount {
        actual: usize,
        expected: usize,
    },
    DuplicateChildSemanticJournal,
    VerifierIdMismatch,
    StatementHashMismatch,
    ArithmeticOverflow(&'static str),
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
    Structural(ZrpfErrorV3),
}

impl fmt::Display for ValueNodeErrorV4 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidSemanticSubtreeVersion(version) => {
                write!(formatter, "invalid semantic subtree version: {version}")
            }
            Self::InvalidNodeJournalVersion(version) => {
                write!(formatter, "invalid node journal version: {version}")
            }
            Self::EmptyLeafRecords => formatter.write_str("semantic subtree has no leaf records"),
            Self::TooManyLeafRecords { actual, maximum } => {
                write!(formatter, "semantic leaf count {actual} exceeds {maximum}")
            }
            Self::LeafCountMismatch => {
                formatter.write_str("semantic subtree leaf count mismatches its records")
            }
            Self::SubtreePartitionMismatch => {
                formatter.write_str("semantic subtree partition mismatches its records")
            }
            Self::NonSingletonLeafRecord { ordinal } => {
                write!(formatter, "semantic leaf record {ordinal} is not singleton")
            }
            Self::NonCanonicalLeafOrder { ordinal } => {
                write!(
                    formatter,
                    "semantic leaf record {ordinal} is not dense and ordered"
                )
            }
            Self::DuplicateSourceClaim => formatter.write_str("duplicate semantic source claim"),
            Self::DuplicateSemanticSource => {
                formatter.write_str("duplicate semantic source identity")
            }
            Self::DuplicateTask => formatter.write_str("duplicate semantic task identity"),
            Self::DuplicateTransactionRoot => {
                formatter.write_str("duplicate semantic transaction root")
            }
            Self::StateDiscontinuity { ordinal } => {
                write!(
                    formatter,
                    "semantic state is discontinuous at record {ordinal}"
                )
            }
            Self::SubtreeEndpointMismatch => {
                formatter.write_str("semantic subtree endpoints mismatch its records")
            }
            Self::RepresentedRowLimitExceeded { actual, maximum } => {
                write!(
                    formatter,
                    "represented row count {actual} exceeds {maximum}"
                )
            }
            Self::InvalidRepresentedRowShape => {
                formatter.write_str("represented row count is inconsistent with summaries")
            }
            Self::TooManyAssetFlows { actual, maximum } => {
                write!(
                    formatter,
                    "semantic asset flow count {actual} exceeds {maximum}"
                )
            }
            Self::InvalidAssetFlow => formatter.write_str("semantic asset flow is invalid"),
            Self::NonCanonicalAssetFlowOrder => {
                formatter.write_str("semantic asset flows are not sorted unique")
            }
            Self::TooManyAuthorityUses { actual, maximum } => {
                write!(
                    formatter,
                    "semantic authority use count {actual} exceeds {maximum}"
                )
            }
            Self::InvalidAuthorityUse => formatter.write_str("semantic authority use is invalid"),
            Self::NonCanonicalAuthorityUseOrder => {
                formatter.write_str("semantic authority uses are not sorted unique")
            }
            Self::AuthorityUseOutsidePartition => {
                formatter.write_str("semantic authority use lies outside the subtree")
            }
            Self::AuthorityUseSourceMismatch => {
                formatter.write_str("semantic authority use source mismatches its leaf")
            }
            Self::IssuanceUseMismatch => {
                formatter.write_str("semantic issuance differs from authority use totals")
            }
            Self::EmptySemanticChildren => {
                formatter.write_str("semantic merge has no child subtrees")
            }
            Self::TooManySemanticChildren { actual, maximum } => {
                write!(formatter, "semantic child count {actual} exceeds {maximum}")
            }
            Self::SemanticChildMetadataMismatch { child, field } => {
                write!(formatter, "semantic child {child} mismatches {field}")
            }
            Self::NonCanonicalSemanticChildOrder { child } => {
                write!(formatter, "semantic child {child} is not dense and ordered")
            }
            Self::SemanticChildStateDiscontinuity { child } => {
                write!(
                    formatter,
                    "semantic child {child} has a discontinuous state"
                )
            }
            Self::SemanticMergeLimitExceeded {
                field,
                actual,
                maximum,
            } => write!(
                formatter,
                "semantic merge {field} count {actual} exceeds {maximum}"
            ),
            Self::CommitmentMismatch(field) => {
                write!(formatter, "semantic commitment mismatches: {field}")
            }
            Self::StructuralPartitionMismatch => {
                formatter.write_str("V4 semantic and structural partitions differ")
            }
            Self::StructuralLeafCountMismatch => {
                formatter.write_str("V4 semantic and structural leaf counts differ")
            }
            Self::StructuralScopeMismatch => {
                formatter.write_str("V4 semantic and structural scopes differ")
            }
            Self::InvalidChildSemanticJournalCount { actual, expected } => write!(
                formatter,
                "V4 child semantic journal count {actual} differs from {expected}"
            ),
            Self::DuplicateChildSemanticJournal => {
                formatter.write_str("V4 child semantic journal hash repeats")
            }
            Self::VerifierIdMismatch => formatter.write_str("V4 verifier ID mismatches"),
            Self::StatementHashMismatch => formatter.write_str("V4 statement hash mismatches"),
            Self::ArithmeticOverflow(field) => write!(formatter, "V4 overflow: {field}"),
            Self::EmptyInput => formatter.write_str("V4 input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(formatter, "V4 input length {actual} exceeds {maximum}")
            }
            Self::PostcardDecode => formatter.write_str("V4 postcard decode failed"),
            Self::TrailingBytes => formatter.write_str("V4 input has trailing bytes"),
            Self::NonCanonicalEncoding => formatter.write_str("V4 input is not canonical"),
            Self::Structural(error) => write!(formatter, "V3 structural journal rejected: {error}"),
        }
    }
}

impl From<ZrpfErrorV3> for ValueNodeErrorV4 {
    fn from(error: ZrpfErrorV3) -> Self {
        Self::Structural(error)
    }
}
