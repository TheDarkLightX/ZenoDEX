use core::fmt;

use super::{EconomicLaneIdV1, LaneModuleReleaseErrorV1, LaneModuleReleaseIdV1};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LaneModuleReleaseRegistryErrorV1 {
    InvalidRegistryVersion(u16),
    EmptyRegistry,
    TooManyReleases {
        actual: usize,
        maximum: usize,
    },
    MixedLane {
        position: usize,
        expected: EconomicLaneIdV1,
        actual: EconomicLaneIdV1,
    },
    DuplicateReleaseId(LaneModuleReleaseIdV1),
    NonCanonicalReleaseOrder {
        position: usize,
    },
    MultipleActiveNewReleases,
    MissingPredecessor {
        release_id: LaneModuleReleaseIdV1,
        predecessor_release_id: LaneModuleReleaseIdV1,
    },
    PredecessorCycle(LaneModuleReleaseIdV1),
    NoActiveNewRelease,
    UnknownRelease(LaneModuleReleaseIdV1),
    ReleaseAdmission(LaneModuleReleaseErrorV1),
    LaneEntryMismatch {
        expected: EconomicLaneIdV1,
        actual: EconomicLaneIdV1,
    },
    RegistryRootMismatch,
    InvalidDerivedCommitment,
    ArithmeticOverflow(&'static str),
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    PostcardEncode,
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for LaneModuleReleaseRegistryErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRegistryVersion(_)
            | Self::EmptyRegistry
            | Self::TooManyReleases { .. }
            | Self::MixedLane { .. }
            | Self::DuplicateReleaseId(_)
            | Self::NonCanonicalReleaseOrder { .. }
            | Self::MultipleActiveNewReleases
            | Self::MissingPredecessor { .. }
            | Self::PredecessorCycle(_) => self.fmt_registry(formatter),
            Self::NoActiveNewRelease
            | Self::UnknownRelease(_)
            | Self::ReleaseAdmission(_)
            | Self::LaneEntryMismatch { .. }
            | Self::RegistryRootMismatch
            | Self::InvalidDerivedCommitment
            | Self::ArithmeticOverflow(_) => self.fmt_resolution(formatter),
            Self::EmptyInput
            | Self::InputTooLarge { .. }
            | Self::PostcardEncode
            | Self::PostcardDecode
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding => self.fmt_codec(formatter),
        }
    }
}

impl LaneModuleReleaseRegistryErrorV1 {
    fn fmt_registry(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRegistryVersion(version) => {
                write!(
                    formatter,
                    "invalid lane module release registry version: {version}"
                )
            }
            Self::EmptyRegistry => formatter.write_str("lane module release registry is empty"),
            Self::TooManyReleases { actual, maximum } => write!(
                formatter,
                "lane module release count {actual} exceeds {maximum}"
            ),
            Self::MixedLane {
                position,
                expected,
                actual,
            } => write!(
                formatter,
                "release {position} lane {actual:?} differs from registry lane {expected:?}"
            ),
            Self::DuplicateReleaseId(release_id) => write!(
                formatter,
                "duplicate lane module release ID: {:02x?}",
                release_id.as_bytes()
            ),
            Self::NonCanonicalReleaseOrder { position } => {
                write!(
                    formatter,
                    "noncanonical release order at position {position}"
                )
            }
            Self::MultipleActiveNewReleases => {
                formatter.write_str("lane module registry has multiple ActiveNew releases")
            }
            Self::MissingPredecessor {
                release_id,
                predecessor_release_id,
            } => write!(
                formatter,
                "release {:02x?} has missing predecessor {:02x?}",
                release_id.as_bytes(),
                predecessor_release_id.as_bytes()
            ),
            Self::PredecessorCycle(release_id) => write!(
                formatter,
                "release predecessor graph cycles from {:02x?}",
                release_id.as_bytes()
            ),
            _ => formatter.write_str("lane module release registry rejection"),
        }
    }

    fn fmt_resolution(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoActiveNewRelease => {
                formatter.write_str("lane module registry has no ActiveNew release")
            }
            Self::UnknownRelease(release_id) => write!(
                formatter,
                "unknown lane module release: {:02x?}",
                release_id.as_bytes()
            ),
            Self::ReleaseAdmission(error) => write!(formatter, "release admission failed: {error}"),
            Self::LaneEntryMismatch { expected, actual } => write!(
                formatter,
                "global lane entry {actual:?} differs from registry lane {expected:?}"
            ),
            Self::RegistryRootMismatch => {
                formatter.write_str("global lane entry release-registry root mismatch")
            }
            Self::InvalidDerivedCommitment => {
                formatter.write_str("invalid derived lane module registry commitment")
            }
            Self::ArithmeticOverflow(field) => {
                write!(
                    formatter,
                    "lane module registry arithmetic overflow: {field}"
                )
            }
            _ => formatter.write_str("lane module release resolution rejection"),
        }
    }

    fn fmt_codec(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("lane module registry input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "lane module registry input length {actual} exceeds {maximum}"
            ),
            Self::PostcardEncode => formatter.write_str("lane module registry encode failed"),
            Self::PostcardDecode => formatter.write_str("lane module registry decode failed"),
            Self::TrailingBytes => formatter.write_str("lane module registry has trailing bytes"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("lane module registry encoding is not canonical")
            }
            _ => formatter.write_str("lane module release registry codec rejection"),
        }
    }
}
