use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceOpenedSpotValueLeafErrorV6 {
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    InvalidInputSchema(u16),
    TruncatedInput(&'static str),
    TrailingInputBytes,
    NonCanonicalInput,
    EmptyComponent(&'static str),
    ComponentTooLarge {
        component: &'static str,
        actual: usize,
        maximum: usize,
    },
    LengthOverflow(&'static str),
    SourceInputDecode,
    NonCanonicalSourceInput,
    SourceJournalDecode,
    NonCanonicalSourceJournal,
    SourceTransitionRejected,
    SourceJournalMismatch,
    SourceProfileRejected(&'static str),
    AdapterProjectionRejected,
    AdapterJournalDecode,
    AdapterJournalMismatch,
    SwapReexecutionRejected,
    SwapFlowRejected(&'static str),
    NullifierDerivation,
    StatementDerivation(&'static str),
    StatementDecode,
    StatementEncode,
    StatementTooLarge {
        actual: usize,
        maximum: usize,
    },
    NonCanonicalStatement,
    StatementShape(&'static str),
}

impl fmt::Display for SourceOpenedSpotValueLeafErrorV6 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("V6 source-opened input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(formatter, "V6 input length {actual} exceeds {maximum}")
            }
            Self::InvalidInputSchema(version) => {
                write!(formatter, "V6 input schema {version} is invalid")
            }
            Self::TruncatedInput(field) => write!(formatter, "V6 input truncated at {field}"),
            Self::TrailingInputBytes => formatter.write_str("V6 input has trailing bytes"),
            Self::NonCanonicalInput => formatter.write_str("V6 input encoding is noncanonical"),
            Self::EmptyComponent(component) => write!(formatter, "V6 {component} is empty"),
            Self::ComponentTooLarge {
                component,
                actual,
                maximum,
            } => write!(
                formatter,
                "V6 {component} length {actual} exceeds {maximum}"
            ),
            Self::LengthOverflow(field) => write!(formatter, "V6 {field} length overflows"),
            Self::SourceInputDecode => formatter.write_str("V6 source input decode failed"),
            Self::NonCanonicalSourceInput => {
                formatter.write_str("V6 source input is not canonical Postcard")
            }
            Self::SourceJournalDecode => formatter.write_str("V6 source journal decode failed"),
            Self::NonCanonicalSourceJournal => {
                formatter.write_str("V6 source journal is not canonical Postcard")
            }
            Self::SourceTransitionRejected => {
                formatter.write_str("V6 source transition recomposition rejected")
            }
            Self::SourceJournalMismatch => {
                formatter.write_str("V6 recomposed source journal differs from the opening")
            }
            Self::SourceProfileRejected(field) => {
                write!(
                    formatter,
                    "V6 ordinary Spot source profile rejected {field}"
                )
            }
            Self::AdapterProjectionRejected => {
                formatter.write_str("V6 adapter reprojection rejected")
            }
            Self::AdapterJournalDecode => {
                formatter.write_str("V6 authenticated adapter journal decode failed")
            }
            Self::AdapterJournalMismatch => formatter
                .write_str("V6 reprojected adapter journal differs from authenticated bytes"),
            Self::SwapReexecutionRejected => {
                formatter.write_str("V6 deterministic swap re-execution rejected")
            }
            Self::SwapFlowRejected(field) => {
                write!(formatter, "V6 swap flow rejected {field}")
            }
            Self::NullifierDerivation => {
                formatter.write_str("V6 action nullifier derivation failed")
            }
            Self::StatementDerivation(field) => {
                write!(formatter, "V6 statement derivation failed at {field}")
            }
            Self::StatementDecode => formatter.write_str("V6 statement decode failed"),
            Self::StatementEncode => formatter.write_str("V6 statement encode failed"),
            Self::StatementTooLarge { actual, maximum } => {
                write!(formatter, "V6 statement length {actual} exceeds {maximum}")
            }
            Self::NonCanonicalStatement => {
                formatter.write_str("V6 statement encoding is noncanonical")
            }
            Self::StatementShape(field) => {
                write!(formatter, "V6 statement shape mismatch: {field}")
            }
        }
    }
}
