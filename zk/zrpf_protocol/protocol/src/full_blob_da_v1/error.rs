use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FullBlobDataAvailabilityErrorV1 {
    InvalidVersion(u16),
    EmptyBlob,
    BlobTooLarge { actual: usize, maximum: usize },
    InvalidChunkSize(u32),
    InvalidChunkCount { actual: u32, expected: u32 },
    TooManyChunks { actual: u32, maximum: u32 },
    RetentionBeforeEpoch,
    DataRootMismatch,
    ChunkRootMismatch,
    CertificateRootMismatch,
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for FullBlobDataAvailabilityErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidVersion(version) => {
                write!(
                    formatter,
                    "invalid full-blob DA certificate version: {version}"
                )
            }
            Self::EmptyBlob => formatter.write_str("full-blob DA payload is empty"),
            Self::BlobTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "full-blob DA payload length {actual} exceeds {maximum}"
                )
            }
            Self::InvalidChunkSize(size) => {
                write!(formatter, "invalid full-blob DA chunk size: {size}")
            }
            Self::InvalidChunkCount { actual, expected } => write!(
                formatter,
                "full-blob DA chunk count {actual} differs from expected {expected}"
            ),
            Self::TooManyChunks { actual, maximum } => {
                write!(
                    formatter,
                    "full-blob DA chunk count {actual} exceeds {maximum}"
                )
            }
            Self::RetentionBeforeEpoch => {
                formatter.write_str("full-blob DA retention ends before its epoch")
            }
            Self::DataRootMismatch => formatter.write_str("full-blob DA data root mismatch"),
            Self::ChunkRootMismatch => formatter.write_str("full-blob DA chunk root mismatch"),
            Self::CertificateRootMismatch => {
                formatter.write_str("full-blob DA certificate root mismatch")
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment(field) => {
                write!(
                    formatter,
                    "invalid derived full-blob DA commitment: {field}"
                )
            }
            Self::EmptyInput => formatter.write_str("full-blob DA certificate input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "full-blob DA certificate length {actual} exceeds {maximum}"
            ),
            Self::PostcardDecode => {
                formatter.write_str("full-blob DA certificate postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("full-blob DA certificate has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("full-blob DA certificate encoding is noncanonical")
            }
        }
    }
}
