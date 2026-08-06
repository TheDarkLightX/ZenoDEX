use core::fmt;

use super::{
    EconomicLaneIdV1, EconomicProfileSnapshotErrorV1, LaneModuleReleaseErrorV1,
    LaneModuleReleaseIdV1,
};
use crate::SparseMerkleCellTransitionErrorV1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GlobalEconomicStateErrorV1 {
    InvalidStateVersion(u16),
    ZeroStateRoot,
    CounterfeitStateRoot,
    WrongLaneStateRootCount {
        actual: usize,
        expected: usize,
    },
    DuplicateLaneStateRoot(EconomicLaneIdV1),
    NonCanonicalLaneStateRootOrder {
        position: usize,
        expected: EconomicLaneIdV1,
        actual: EconomicLaneIdV1,
    },
    InvalidObjectReleasePinVersion(u16),
    EconomicProfileBinding(EconomicProfileSnapshotErrorV1),
    ProfileMismatch,
    WriterEpochMismatch,
    OccurrenceProfileMismatch,
    OccurrenceWriterEpochMismatch,
    ApplicationMismatch,
    ChainOrDomainMismatch,
    PreStateRootMismatch,
    ObjectPinProofCountMismatch {
        actual: usize,
        expected: usize,
    },
    ObjectPinObjectMismatch {
        position: usize,
    },
    ObjectPinRegistryRootMismatch {
        position: usize,
    },
    UnknownCreatingRelease {
        lane_id: EconomicLaneIdV1,
        release_id: LaneModuleReleaseIdV1,
    },
    CreatingReleaseAdmission {
        lane_id: EconomicLaneIdV1,
        source: LaneModuleReleaseErrorV1,
    },
    ObjectPinMerkle(SparseMerkleCellTransitionErrorV1),
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
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

impl fmt::Display for GlobalEconomicStateErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidStateVersion(version) => {
                write!(formatter, "invalid global economic state version: {version}")
            }
            Self::ZeroStateRoot => formatter.write_str("global economic state root must be nonzero"),
            Self::CounterfeitStateRoot => {
                formatter.write_str("global economic state root does not match its content")
            }
            Self::WrongLaneStateRootCount { actual, expected } => write!(
                formatter,
                "global economic lane-state root count {actual} differs from required count {expected}"
            ),
            Self::DuplicateLaneStateRoot(lane_id) => {
                write!(formatter, "duplicate global economic lane-state root for {lane_id:?}")
            }
            Self::NonCanonicalLaneStateRootOrder {
                position,
                expected,
                actual,
            } => write!(
                formatter,
                "global economic lane-state root {position} is {actual:?}, expected {expected:?}"
            ),
            Self::InvalidObjectReleasePinVersion(version) => {
                write!(formatter, "invalid economic object release-pin version: {version}")
            }
            Self::EconomicProfileBinding(source) => {
                write!(formatter, "global economic state profile binding failed: {source}")
            }
            Self::ProfileMismatch => {
                formatter.write_str("global economic state profile differs from the supplied profile")
            }
            Self::WriterEpochMismatch => formatter
                .write_str("global economic state writer epoch differs from the supplied profile"),
            Self::OccurrenceProfileMismatch => formatter
                .write_str("economic occurrence profile differs from the bound global state"),
            Self::OccurrenceWriterEpochMismatch => formatter
                .write_str("economic occurrence writer epoch differs from the bound global state"),
            Self::ApplicationMismatch => formatter
                .write_str("economic occurrence application differs from the bound global state"),
            Self::ChainOrDomainMismatch => formatter
                .write_str("economic occurrence chain or domain differs from the bound global state"),
            Self::PreStateRootMismatch => formatter
                .write_str("economic occurrence pre-state root differs from the bound global state"),
            Self::ObjectPinProofCountMismatch { actual, expected } => write!(
                formatter,
                "object release-pin proof count {actual} differs from consumed-object count {expected}"
            ),
            Self::ObjectPinObjectMismatch { position } => write!(
                formatter,
                "object release-pin proof {position} does not match the consumed object"
            ),
            Self::ObjectPinRegistryRootMismatch { position } => write!(
                formatter,
                "object release-pin proof {position} does not open the state registry root"
            ),
            Self::UnknownCreatingRelease {
                lane_id,
                release_id,
            } => write!(
                formatter,
                "object pin references unknown {lane_id:?} creating release {:02x?}",
                release_id.as_bytes()
            ),
            Self::CreatingReleaseAdmission { lane_id, source } => write!(
                formatter,
                "object pin creating release for {lane_id:?} is inadmissible: {source}"
            ),
            Self::ObjectPinMerkle(source) => {
                write!(formatter, "object release-pin Merkle derivation failed: {source}")
            }
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "global economic state arithmetic overflow: {field}")
            }
            Self::InvalidDerivedCommitment(field) => write!(
                formatter,
                "global economic state produced an invalid commitment: {field}"
            ),
            Self::EmptyInput => formatter.write_str("global economic state input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "global economic state input length {actual} exceeds {maximum}"
            ),
            Self::PostcardEncode => formatter.write_str("global economic state encode failed"),
            Self::PostcardDecode => formatter.write_str("global economic state decode failed"),
            Self::TrailingBytes => formatter.write_str("global economic state input has trailing bytes"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("global economic state input is not canonical")
            }
        }
    }
}

impl From<SparseMerkleCellTransitionErrorV1> for GlobalEconomicStateErrorV1 {
    fn from(source: SparseMerkleCellTransitionErrorV1) -> Self {
        Self::ObjectPinMerkle(source)
    }
}
