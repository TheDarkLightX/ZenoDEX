use core::fmt;

use super::RouteReleaseRegistryErrorV1;
use crate::EconomicActionBatchErrorV1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EconomicCommandOccurrenceErrorV1 {
    EconomicAction(EconomicActionBatchErrorV1),
    RouteRegistry(RouteReleaseRegistryErrorV1),
    InvalidOccurrenceVersion(u16),
    ZeroOccurrenceId,
    CounterfeitOccurrenceId,
    ProfileIdMismatch,
    WriterEpochMismatch,
    RouteRegistryRootMismatch,
    UnknownRouteRelease,
    CommandVariantMismatch,
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment,
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl From<EconomicActionBatchErrorV1> for EconomicCommandOccurrenceErrorV1 {
    fn from(error: EconomicActionBatchErrorV1) -> Self {
        Self::EconomicAction(error)
    }
}

impl From<RouteReleaseRegistryErrorV1> for EconomicCommandOccurrenceErrorV1 {
    fn from(error: RouteReleaseRegistryErrorV1) -> Self {
        Self::RouteRegistry(error)
    }
}

impl fmt::Display for EconomicCommandOccurrenceErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EconomicAction(error) => write!(formatter, "economic action rejected: {error}"),
            Self::RouteRegistry(error) => write!(formatter, "route registry rejected: {error}"),
            Self::InvalidOccurrenceVersion(version) => write!(
                formatter,
                "invalid economic command occurrence version: {version}"
            ),
            Self::ZeroOccurrenceId => formatter.write_str("economic command occurrence ID is zero"),
            Self::CounterfeitOccurrenceId => {
                formatter.write_str("economic command occurrence ID is not content-derived")
            }
            Self::ProfileIdMismatch => {
                formatter.write_str("economic command occurrence uses an inactive profile")
            }
            Self::WriterEpochMismatch => {
                formatter.write_str("economic command occurrence uses a stale writer epoch")
            }
            Self::RouteRegistryRootMismatch => formatter
                .write_str("economic command occurrence route registry differs from the profile"),
            Self::UnknownRouteRelease => {
                formatter.write_str("economic command occurrence route is not governed")
            }
            Self::CommandVariantMismatch => {
                formatter.write_str("economic command occurrence action and route variants differ")
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment => {
                formatter.write_str("economic command occurrence derived an invalid commitment")
            }
            Self::EmptyInput => formatter.write_str("economic command occurrence input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "economic command occurrence input length {actual} exceeds {maximum}"
            ),
            Self::PostcardDecode => {
                formatter.write_str("economic command occurrence postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("economic command occurrence input has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("economic command occurrence input is not canonical")
            }
        }
    }
}
