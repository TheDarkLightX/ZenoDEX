use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckpointFinalityCertificateErrorV1 {
    InvalidVersion(u16),
    CertificateRootMismatch,
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for CheckpointFinalityCertificateErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidVersion(version) => {
                write!(
                    formatter,
                    "invalid checkpoint finality certificate version: {version}"
                )
            }
            Self::CertificateRootMismatch => {
                formatter.write_str("checkpoint finality certificate root mismatch")
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment(field) => write!(
                formatter,
                "invalid derived checkpoint finality commitment: {field}"
            ),
            Self::EmptyInput => {
                formatter.write_str("checkpoint finality certificate input is empty")
            }
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "checkpoint finality certificate length {actual} exceeds {maximum}"
            ),
            Self::PostcardDecode => {
                formatter.write_str("checkpoint finality certificate postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("checkpoint finality certificate has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("checkpoint finality certificate encoding is noncanonical")
            }
        }
    }
}
