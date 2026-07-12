use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SettlementEpochCertificateErrorV1 {
    InvalidVersion(u16),
    UnchangedStateRoot,
    InvalidDerivedCommitment(&'static str),
    ArithmeticOverflow(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for SettlementEpochCertificateErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidVersion(version) => {
                write!(
                    formatter,
                    "invalid settlement certificate version: {version}"
                )
            }
            Self::UnchangedStateRoot => {
                formatter.write_str("settlement pre-state and post-state roots are equal")
            }
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived settlement commitment: {field}")
            }
            Self::ArithmeticOverflow(field) => {
                write!(
                    formatter,
                    "settlement certificate arithmetic overflow: {field}"
                )
            }
            Self::EmptyInput => formatter.write_str("settlement certificate input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "settlement certificate input length {actual} exceeds {maximum}"
            ),
            Self::PostcardDecode => {
                formatter.write_str("settlement certificate postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("settlement certificate postcard input has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("settlement certificate postcard input is noncanonical")
            }
        }
    }
}
