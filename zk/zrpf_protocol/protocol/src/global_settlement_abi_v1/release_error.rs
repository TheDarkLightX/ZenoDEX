use core::fmt;

use super::{LaneModuleMigrationModeV1, LaneModuleReleaseStatusV1};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LaneModuleReleaseErrorV1 {
    InvalidReleaseVersion(u16),
    ZeroReleaseId,
    CounterfeitReleaseId,
    InvalidDerivedCommitment(&'static str),
    ArithmeticOverflow(&'static str),
    ZeroResourceLimit(&'static str),
    UnexpectedMigrationPredecessor,
    MissingMigrationPredecessor(LaneModuleMigrationModeV1),
    SelfMigrationPredecessor,
    TerminalCoverageIncomplete(LaneModuleReleaseStatusV1),
    InvalidStatusTransition {
        from: LaneModuleReleaseStatusV1,
        to: LaneModuleReleaseStatusV1,
    },
    StatusDisallowsNewObject(LaneModuleReleaseStatusV1),
    StatusDisallowsExistingObject(LaneModuleReleaseStatusV1),
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

impl fmt::Display for LaneModuleReleaseErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidReleaseVersion(_)
            | Self::ZeroReleaseId
            | Self::CounterfeitReleaseId
            | Self::InvalidDerivedCommitment(_)
            | Self::ArithmeticOverflow(_)
            | Self::ZeroResourceLimit(_)
            | Self::UnexpectedMigrationPredecessor
            | Self::MissingMigrationPredecessor(_)
            | Self::SelfMigrationPredecessor => self.fmt_content(formatter),
            Self::TerminalCoverageIncomplete(_)
            | Self::InvalidStatusTransition { .. }
            | Self::StatusDisallowsNewObject(_)
            | Self::StatusDisallowsExistingObject(_) => self.fmt_lifecycle(formatter),
            Self::EmptyInput
            | Self::InputTooLarge { .. }
            | Self::PostcardEncode
            | Self::PostcardDecode
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding => self.fmt_codec(formatter),
        }
    }
}

impl LaneModuleReleaseErrorV1 {
    fn fmt_content(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidReleaseVersion(version) => {
                write!(formatter, "invalid lane module release version: {version}")
            }
            Self::ZeroReleaseId => formatter.write_str("lane module release ID must be nonzero"),
            Self::CounterfeitReleaseId => {
                formatter.write_str("lane module release ID does not match its content")
            }
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived lane module commitment: {field}")
            }
            Self::ArithmeticOverflow(field) => {
                write!(
                    formatter,
                    "lane module release arithmetic overflow: {field}"
                )
            }
            Self::ZeroResourceLimit(field) => {
                write!(
                    formatter,
                    "lane module resource limit must be nonzero: {field}"
                )
            }
            Self::UnexpectedMigrationPredecessor => {
                formatter.write_str("genesis lane module release has a migration predecessor")
            }
            Self::MissingMigrationPredecessor(mode) => {
                write!(
                    formatter,
                    "lane module migration predecessor missing for {mode:?}"
                )
            }
            Self::SelfMigrationPredecessor => {
                formatter.write_str("lane module release names itself as migration predecessor")
            }
            _ => formatter.write_str("lane module release content rejection"),
        }
    }

    fn fmt_lifecycle(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TerminalCoverageIncomplete(status) => {
                write!(
                    formatter,
                    "terminal coverage is incomplete for release status {status:?}"
                )
            }
            Self::InvalidStatusTransition { from, to } => {
                write!(
                    formatter,
                    "invalid lane module release transition: {from:?} -> {to:?}"
                )
            }
            Self::StatusDisallowsNewObject(status) => {
                write!(
                    formatter,
                    "release status disallows new objects: {status:?}"
                )
            }
            Self::StatusDisallowsExistingObject(status) => {
                write!(
                    formatter,
                    "release status disallows existing-object transition: {status:?}"
                )
            }
            _ => formatter.write_str("lane module release lifecycle rejection"),
        }
    }

    fn fmt_codec(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("lane module release input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "lane module release input length {actual} exceeds {maximum}"
            ),
            Self::PostcardEncode => formatter.write_str("lane module release encode failed"),
            Self::PostcardDecode => formatter.write_str("lane module release decode failed"),
            Self::TrailingBytes => formatter.write_str("lane module release has trailing bytes"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("lane module release encoding is not canonical")
            }
            _ => formatter.write_str("lane module release codec rejection"),
        }
    }
}
