use core::fmt;

use super::{EconomicLaneIdV1, LaneModuleReleaseIdV1, RouteReleaseIdV1};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RouteReleaseRegistryErrorV1 {
    InvalidRegistryVersion(u16),
    EmptyRegistry,
    TooManyRoutes {
        actual: usize,
        maximum: usize,
    },
    DuplicateRouteReleaseId(RouteReleaseIdV1),
    AmbiguousRouteSelection,
    NonCanonicalRouteOrder {
        position: usize,
    },
    EmptySelectionDependencies,
    TooManySelectionDependencies {
        actual: usize,
        maximum: usize,
    },
    DuplicateSelectionLane(EconomicLaneIdV1),
    NonCanonicalSelectionLaneOrder {
        position: usize,
    },
    UnknownRouteSelection,
    ModuleRegistryCountMismatch {
        actual: usize,
        expected: usize,
    },
    ModuleRegistryLaneMismatch {
        position: usize,
        expected: EconomicLaneIdV1,
        actual: EconomicLaneIdV1,
    },
    MissingRequiredModuleRegistry(EconomicLaneIdV1),
    UnknownDependencyRelease {
        route_id: RouteReleaseIdV1,
        lane_id: EconomicLaneIdV1,
        release_id: LaneModuleReleaseIdV1,
    },
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

impl fmt::Display for RouteReleaseRegistryErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRegistryVersion(_)
            | Self::EmptyRegistry
            | Self::TooManyRoutes { .. }
            | Self::DuplicateRouteReleaseId(_)
            | Self::AmbiguousRouteSelection
            | Self::NonCanonicalRouteOrder { .. } => self.fmt_registry(formatter),
            Self::EmptySelectionDependencies
            | Self::TooManySelectionDependencies { .. }
            | Self::DuplicateSelectionLane(_)
            | Self::NonCanonicalSelectionLaneOrder { .. }
            | Self::UnknownRouteSelection
            | Self::ModuleRegistryCountMismatch { .. }
            | Self::ModuleRegistryLaneMismatch { .. }
            | Self::MissingRequiredModuleRegistry(_)
            | Self::UnknownDependencyRelease { .. }
            | Self::InvalidDerivedCommitment
            | Self::ArithmeticOverflow(_) => self.fmt_selection_and_binding(formatter),
            Self::EmptyInput
            | Self::InputTooLarge { .. }
            | Self::PostcardEncode
            | Self::PostcardDecode
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding => self.fmt_codec(formatter),
        }
    }
}

impl RouteReleaseRegistryErrorV1 {
    fn fmt_registry(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRegistryVersion(version) => {
                write!(
                    formatter,
                    "invalid route release registry version: {version}"
                )
            }
            Self::EmptyRegistry => formatter.write_str("route release registry is empty"),
            Self::TooManyRoutes { actual, maximum } => {
                write!(formatter, "route release count {actual} exceeds {maximum}")
            }
            Self::DuplicateRouteReleaseId(route_id) => write!(
                formatter,
                "duplicate route release ID: {:02x?}",
                route_id.as_bytes()
            ),
            Self::AmbiguousRouteSelection => {
                formatter.write_str("multiple routes share one route selection key")
            }
            Self::NonCanonicalRouteOrder { position } => {
                write!(formatter, "noncanonical route order at position {position}")
            }
            _ => formatter.write_str("route release registry rejection"),
        }
    }

    fn fmt_selection_and_binding(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptySelectionDependencies => {
                formatter.write_str("route selection has no module releases")
            }
            Self::TooManySelectionDependencies { actual, maximum } => write!(
                formatter,
                "route selection module release count {actual} exceeds {maximum}"
            ),
            Self::DuplicateSelectionLane(lane_id) => {
                write!(formatter, "route selection repeats lane {lane_id:?}")
            }
            Self::NonCanonicalSelectionLaneOrder { position } => write!(
                formatter,
                "noncanonical route selection lane order at position {position}"
            ),
            Self::UnknownRouteSelection => {
                formatter.write_str("route selection is absent from the registry")
            }
            Self::ModuleRegistryCountMismatch { actual, expected } => write!(
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
            Self::MissingRequiredModuleRegistry(lane_id) => {
                write!(
                    formatter,
                    "required module registry for {lane_id:?} is missing"
                )
            }
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
            Self::InvalidDerivedCommitment => {
                formatter.write_str("invalid derived route registry commitment")
            }
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "route registry arithmetic overflow: {field}")
            }
            _ => formatter.write_str("route selection or binding rejection"),
        }
    }

    fn fmt_codec(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("route registry input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "route registry input length {actual} exceeds {maximum}"
            ),
            Self::PostcardEncode => formatter.write_str("route registry encode failed"),
            Self::PostcardDecode => formatter.write_str("route registry decode failed"),
            Self::TrailingBytes => formatter.write_str("route registry has trailing bytes"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("route registry encoding is not canonical")
            }
            _ => formatter.write_str("route registry codec rejection"),
        }
    }
}
