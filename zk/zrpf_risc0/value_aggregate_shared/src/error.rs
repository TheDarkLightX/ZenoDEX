use core::fmt;

use zenodex_zrpf_protocol_v3::{ValueAggregateErrorV5, ValueNodeErrorV4};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueAggregateRecompositionErrorV5 {
    InvalidPolicy(&'static str),
    InvalidChildCount {
        actual: usize,
        maximum: usize,
    },
    PolicyChildCountMismatch {
        policy: usize,
        input: usize,
    },
    EmptyChildBytes(usize),
    ChildBytesTooLarge {
        child: usize,
        actual: usize,
        maximum: usize,
    },
    ChildV4JournalDecode(usize),
    ChildV6StatementDecode(usize),
    ChildV5ProposalDecode(usize),
    ChildProgramMismatch(usize),
    ChildProfileMismatch(usize),
    ChildManifestMismatch(usize),
    ChildScopeMismatch(usize),
    ChildLevelMismatch {
        child: usize,
        actual: u8,
    },
    ChildNotSingletonLeaf(usize),
    DuplicateChildClaim,
    DuplicateChildJournal,
    ClaimBindingDerivation(usize),
    ChildCommitmentDerivation(usize),
    SemanticMerge(ValueNodeErrorV4),
    Proposal(ValueAggregateErrorV5),
}

impl fmt::Display for ValueAggregateRecompositionErrorV5 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPolicy(field) => write!(formatter, "invalid V5 policy: {field}"),
            Self::InvalidChildCount { actual, maximum } => {
                write!(
                    formatter,
                    "V5 child count {actual} is outside 1..={maximum}"
                )
            }
            Self::PolicyChildCountMismatch { policy, input } => write!(
                formatter,
                "V5 policy child count {policy} differs from input child count {input}"
            ),
            Self::EmptyChildBytes(child) => write!(formatter, "V5 child {child} bytes are empty"),
            Self::ChildBytesTooLarge {
                child,
                actual,
                maximum,
            } => write!(
                formatter,
                "V5 child {child} byte length {actual} exceeds {maximum}"
            ),
            Self::ChildV4JournalDecode(child) => {
                write!(formatter, "V4 child {child} exact journal decoding failed")
            }
            Self::ChildV6StatementDecode(child) => {
                write!(
                    formatter,
                    "V6 child {child} exact statement decoding failed"
                )
            }
            Self::ChildV5ProposalDecode(child) => {
                write!(formatter, "V5 child {child} exact proposal decoding failed")
            }
            Self::ChildProgramMismatch(child) => {
                write!(formatter, "V5 child {child} program differs from policy")
            }
            Self::ChildProfileMismatch(child) => {
                write!(formatter, "V5 child {child} profile differs from policy")
            }
            Self::ChildManifestMismatch(child) => {
                write!(formatter, "V5 child {child} manifest differs from policy")
            }
            Self::ChildScopeMismatch(child) => {
                write!(formatter, "V5 child {child} scope differs from policy")
            }
            Self::ChildLevelMismatch { child, actual } => {
                write!(formatter, "V5 child {child} has unexpected level {actual}")
            }
            Self::ChildNotSingletonLeaf(child) => {
                write!(formatter, "V5 child {child} is not a singleton value leaf")
            }
            Self::DuplicateChildClaim => formatter.write_str("duplicate derived V5 child claim"),
            Self::DuplicateChildJournal => {
                formatter.write_str("duplicate derived V5 child journal")
            }
            Self::ClaimBindingDerivation(child) => {
                write!(
                    formatter,
                    "V5 child {child} claim binding derivation failed"
                )
            }
            Self::ChildCommitmentDerivation(child) => {
                write!(formatter, "V5 child {child} commitment derivation failed")
            }
            Self::SemanticMerge(error) => write!(formatter, "V5 semantic merge rejected: {error}"),
            Self::Proposal(error) => write!(formatter, "V5 proposal rejected: {error}"),
        }
    }
}

impl From<ValueAggregateErrorV5> for ValueAggregateRecompositionErrorV5 {
    fn from(error: ValueAggregateErrorV5) -> Self {
        Self::Proposal(error)
    }
}
