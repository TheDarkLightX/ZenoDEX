use core::fmt;

use super::{
    EconomicLaneIdV1, EconomicProfileTransitionModeV1, GlobalSettlementAbiErrorV1,
    LaneModuleReleaseErrorV1, LaneModuleReleaseIdV1, LaneModuleReleaseRegistryErrorV1,
    RouteReleaseIdV1, RouteReleaseRegistryErrorV1,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EconomicProfileSnapshotErrorV1 {
    InvalidProfileVersion(u16),
    ZeroProfileId,
    CounterfeitProfileId,
    GenesisHasPredecessor,
    TransitionRequiresPredecessor(EconomicProfileTransitionModeV1),
    GenesisCannotBeSuccessor,
    PredecessorProfileMismatch,
    AuthorityEpochNotIncreasing,
    WriterEpochNotRotated,
    EconomicLaneRegistryInvalid(GlobalSettlementAbiErrorV1),
    EconomicLaneRegistryRootMismatch,
    RouteReleaseRegistryInvalid(RouteReleaseRegistryErrorV1),
    RouteReleaseRegistryRootMismatch,
    WrongModuleRegistryCount {
        actual: usize,
        expected: usize,
    },
    ModuleRegistryLaneMismatch {
        position: usize,
        expected: EconomicLaneIdV1,
        actual: EconomicLaneIdV1,
    },
    ModuleRegistryBinding {
        lane_id: EconomicLaneIdV1,
        source: LaneModuleReleaseRegistryErrorV1,
    },
    UnknownDependencyRelease {
        route_id: RouteReleaseIdV1,
        lane_id: EconomicLaneIdV1,
        release_id: LaneModuleReleaseIdV1,
    },
    DependencyReleaseAdmission {
        route_id: RouteReleaseIdV1,
        lane_id: EconomicLaneIdV1,
        source: LaneModuleReleaseErrorV1,
    },
    EnabledLaneHasNoPrimaryRoute(EconomicLaneIdV1),
    DisabledLaneHasPrimaryRoute(EconomicLaneIdV1),
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

impl fmt::Display for EconomicProfileSnapshotErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidProfileVersion(_)
            | Self::ZeroProfileId
            | Self::CounterfeitProfileId
            | Self::GenesisHasPredecessor
            | Self::TransitionRequiresPredecessor(_)
            | Self::GenesisCannotBeSuccessor
            | Self::PredecessorProfileMismatch
            | Self::AuthorityEpochNotIncreasing
            | Self::WriterEpochNotRotated => self.fmt_profile(formatter),
            Self::EconomicLaneRegistryInvalid(_)
            | Self::EconomicLaneRegistryRootMismatch
            | Self::RouteReleaseRegistryInvalid(_)
            | Self::RouteReleaseRegistryRootMismatch => self.fmt_registry_roots(formatter),
            Self::WrongModuleRegistryCount { .. }
            | Self::ModuleRegistryLaneMismatch { .. }
            | Self::ModuleRegistryBinding { .. }
            | Self::UnknownDependencyRelease { .. }
            | Self::DependencyReleaseAdmission { .. }
            | Self::EnabledLaneHasNoPrimaryRoute(_)
            | Self::DisabledLaneHasPrimaryRoute(_)
            | Self::InvalidDerivedCommitment
            | Self::ArithmeticOverflow(_) => self.fmt_module_binding(formatter),
            Self::EmptyInput
            | Self::InputTooLarge { .. }
            | Self::PostcardEncode
            | Self::PostcardDecode
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding => self.fmt_codec(formatter),
        }
    }
}

impl EconomicProfileSnapshotErrorV1 {
    fn fmt_profile(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidProfileVersion(version) => {
                write!(formatter, "invalid economic profile version: {version}")
            }
            Self::ZeroProfileId => formatter.write_str("economic profile ID must be nonzero"),
            Self::CounterfeitProfileId => {
                formatter.write_str("economic profile ID does not match its content")
            }
            Self::GenesisHasPredecessor => {
                formatter.write_str("genesis economic profile has a predecessor")
            }
            Self::TransitionRequiresPredecessor(mode) => write!(
                formatter,
                "economic profile transition {mode:?} requires a predecessor"
            ),
            Self::GenesisCannotBeSuccessor => {
                formatter.write_str("genesis economic profile cannot be a successor")
            }
            Self::PredecessorProfileMismatch => {
                formatter.write_str("economic profile predecessor does not match")
            }
            Self::AuthorityEpochNotIncreasing => {
                formatter.write_str("economic profile authority epoch must increase")
            }
            Self::WriterEpochNotRotated => {
                formatter.write_str("economic profile writer epoch must increase")
            }
            _ => formatter.write_str("economic profile content rejection"),
        }
    }

    fn fmt_registry_roots(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EconomicLaneRegistryInvalid(source) => {
                write!(formatter, "economic lane registry is invalid: {source}")
            }
            Self::EconomicLaneRegistryRootMismatch => {
                formatter.write_str("economic lane registry root does not match the profile")
            }
            Self::RouteReleaseRegistryInvalid(source) => {
                write!(formatter, "route release registry is invalid: {source}")
            }
            Self::RouteReleaseRegistryRootMismatch => {
                formatter.write_str("route release registry root does not match the profile")
            }
            _ => formatter.write_str("economic profile registry root rejection"),
        }
    }

    fn fmt_module_binding(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongModuleRegistryCount { actual, expected } => write!(
                formatter,
                "module registry count {actual} differs from required count {expected}"
            ),
            Self::ModuleRegistryLaneMismatch {
                position,
                expected,
                actual,
            } => write!(
                formatter,
                "module registry {position} lane {actual:?} differs from required lane {expected:?}"
            ),
            Self::ModuleRegistryBinding { lane_id, source } => write!(
                formatter,
                "module registry for {lane_id:?} is invalid: {source}"
            ),
            Self::UnknownDependencyRelease {
                route_id,
                lane_id,
                release_id,
            } => write!(
                formatter,
                "route {:02x?} references unknown {lane_id:?} release {:02x?}",
                route_id.as_bytes(),
                release_id.as_bytes()
            ),
            Self::DependencyReleaseAdmission {
                route_id,
                lane_id,
                source,
            } => write!(
                formatter,
                "route {:02x?} dependency for {lane_id:?} is inadmissible: {source}",
                route_id.as_bytes()
            ),
            Self::EnabledLaneHasNoPrimaryRoute(lane_id) => {
                write!(formatter, "enabled lane {lane_id:?} has no primary route")
            }
            Self::DisabledLaneHasPrimaryRoute(lane_id) => {
                write!(formatter, "disabled lane {lane_id:?} has a primary route")
            }
            Self::InvalidDerivedCommitment => {
                formatter.write_str("invalid derived economic profile commitment")
            }
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "economic profile arithmetic overflow: {field}")
            }
            _ => formatter.write_str("economic profile registry binding rejection"),
        }
    }

    fn fmt_codec(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("economic profile input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "economic profile input length {actual} exceeds {maximum}"
            ),
            Self::PostcardEncode => formatter.write_str("economic profile encode failed"),
            Self::PostcardDecode => formatter.write_str("economic profile decode failed"),
            Self::TrailingBytes => formatter.write_str("economic profile has trailing bytes"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("economic profile encoding is not canonical")
            }
            _ => formatter.write_str("economic profile codec rejection"),
        }
    }
}
