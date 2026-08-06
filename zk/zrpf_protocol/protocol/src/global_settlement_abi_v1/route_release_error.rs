use core::fmt;

use super::{EconomicLaneIdV1, LaneModuleReleaseIdV1, RouteDependencyRoleV1};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RouteReleaseErrorV1 {
    InvalidRouteReleaseVersion(u16),
    ZeroRouteReleaseId,
    CounterfeitRouteReleaseId,
    InvalidDerivedCommitment,
    ArithmeticOverflow(&'static str),
    EmptyDependencies,
    TooManyDependencies {
        actual: usize,
        maximum: usize,
    },
    EmptyDependencyRoles,
    DuplicateDependencyRole(RouteDependencyRoleV1),
    UnknownDependencyRoleBits(u8),
    DuplicateDependencyLane(EconomicLaneIdV1),
    PrimaryDependencyCount(usize),
    OracleDependencyCount(usize),
    IssueBurnDependencyCount(usize),
    ZeroResourceLimit(&'static str),
    DependencyRegistryCountMismatch {
        actual: usize,
        expected: usize,
    },
    DependencyRegistryLaneMismatch {
        position: usize,
        expected: EconomicLaneIdV1,
        actual: EconomicLaneIdV1,
    },
    UnknownDependencyRelease {
        position: usize,
        lane_id: EconomicLaneIdV1,
        release_id: LaneModuleReleaseIdV1,
    },
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

impl RouteReleaseErrorV1 {
    fn static_message(&self) -> Option<&'static str> {
        match self {
            Self::ZeroRouteReleaseId => Some("route release ID must be nonzero"),
            Self::CounterfeitRouteReleaseId => Some("route release ID does not match its content"),
            Self::InvalidDerivedCommitment => Some("invalid derived route release commitment"),
            Self::EmptyDependencies => Some("route dependency set is empty"),
            Self::EmptyDependencyRoles => Some("route dependency roles are empty"),
            Self::EmptyInput => Some("route release input is empty"),
            Self::PostcardEncode => Some("route release encode failed"),
            Self::PostcardDecode => Some("route release decode failed"),
            Self::TrailingBytes => Some("route release has trailing bytes"),
            Self::NonCanonicalEncoding => Some("route release encoding is not canonical"),
            _ => None,
        }
    }
}

impl fmt::Display for RouteReleaseErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRouteReleaseVersion(version) => {
                write!(formatter, "invalid route release version: {version}")
            }
            Self::ZeroRouteReleaseId
            | Self::CounterfeitRouteReleaseId
            | Self::InvalidDerivedCommitment
            | Self::EmptyDependencies
            | Self::EmptyDependencyRoles
            | Self::EmptyInput
            | Self::PostcardEncode
            | Self::PostcardDecode
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding => formatter.write_str(
                self.static_message()
                    .unwrap_or("unclassified route release error"),
            ),
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "route release arithmetic overflow: {field}")
            }
            Self::TooManyDependencies { actual, maximum } => {
                write_count_exceeds(formatter, "route dependency", *actual, *maximum)
            }
            Self::DuplicateDependencyRole(role) => {
                write!(formatter, "duplicate route dependency role: {role:?}")
            }
            Self::UnknownDependencyRoleBits(bits) => {
                write!(formatter, "unknown route dependency role bits: {bits:#04x}")
            }
            Self::DuplicateDependencyLane(lane_id) => {
                write!(formatter, "duplicate route dependency lane: {lane_id:?}")
            }
            Self::PrimaryDependencyCount(count) => write_primary_count(formatter, *count),
            Self::OracleDependencyCount(count) => {
                write!(formatter, "route Oracle role count is incoherent: {count}")
            }
            Self::IssueBurnDependencyCount(count) => write_issue_burn_count(formatter, *count),
            Self::ZeroResourceLimit(field) => {
                write!(formatter, "route resource limit must be nonzero: {field}")
            }
            Self::DependencyRegistryCountMismatch { actual, expected } => {
                write_registry_count(formatter, *actual, *expected)
            }
            Self::DependencyRegistryLaneMismatch {
                position,
                expected,
                actual,
            } => write_registry_lane(formatter, *position, *expected, *actual),
            Self::UnknownDependencyRelease {
                position,
                lane_id,
                release_id,
            } => write_unknown_release(formatter, *position, *lane_id, release_id),
            Self::InputTooLarge { actual, maximum } => {
                write_count_exceeds(formatter, "route release input length", *actual, *maximum)
            }
        }
    }
}

fn write_count_exceeds(
    formatter: &mut fmt::Formatter<'_>,
    subject: &str,
    actual: usize,
    maximum: usize,
) -> fmt::Result {
    write!(formatter, "{subject} {actual} exceeds {maximum}")
}

fn write_primary_count(formatter: &mut fmt::Formatter<'_>, count: usize) -> fmt::Result {
    write!(
        formatter,
        "route must contain one Primary dependency, found {count}"
    )
}

fn write_issue_burn_count(formatter: &mut fmt::Formatter<'_>, count: usize) -> fmt::Result {
    write!(
        formatter,
        "route IssueBurn role count is incoherent: {count}"
    )
}

fn write_registry_count(
    formatter: &mut fmt::Formatter<'_>,
    actual: usize,
    expected: usize,
) -> fmt::Result {
    write!(
        formatter,
        "route registry count {actual} differs from dependency count {expected}"
    )
}

fn write_registry_lane(
    formatter: &mut fmt::Formatter<'_>,
    position: usize,
    expected: EconomicLaneIdV1,
    actual: EconomicLaneIdV1,
) -> fmt::Result {
    write!(
        formatter,
        "route registry lane at {position} is {actual:?}, expected {expected:?}"
    )
}

fn write_unknown_release(
    formatter: &mut fmt::Formatter<'_>,
    position: usize,
    lane_id: EconomicLaneIdV1,
    release_id: &LaneModuleReleaseIdV1,
) -> fmt::Result {
    write!(
        formatter,
        "route dependency {position} for {lane_id:?} references unknown release {:02x?}",
        release_id.as_bytes()
    )
}
