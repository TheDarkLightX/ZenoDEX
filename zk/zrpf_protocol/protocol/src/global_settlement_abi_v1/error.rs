use core::fmt;

use super::EconomicLaneIdV1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GlobalSettlementAbiErrorV1 {
    InvalidRegistryVersion(u16),
    UnknownLaneIdentifier,
    UnknownLaneCode(u8),
    LaneDisabled(EconomicLaneIdV1),
    WrongLaneCount {
        actual: usize,
        expected: usize,
    },
    DuplicateLane(EconomicLaneIdV1),
    NonCanonicalLaneOrder {
        position: usize,
        expected: EconomicLaneIdV1,
        actual: EconomicLaneIdV1,
    },
    RegistryInvariantViolation,
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for GlobalSettlementAbiErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_semantic(formatter)
    }
}

impl GlobalSettlementAbiErrorV1 {
    fn fmt_semantic(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRegistryVersion(version) => {
                write!(
                    formatter,
                    "invalid global economic lane registry version: {version}"
                )
            }
            Self::UnknownLaneIdentifier => {
                formatter.write_str("unknown global economic lane identifier")
            }
            Self::UnknownLaneCode(code) => {
                write!(formatter, "unknown global economic lane code: {code}")
            }
            Self::LaneDisabled(lane_id) => {
                write!(
                    formatter,
                    "global economic lane is disabled: {}",
                    lane_id.as_str()
                )
            }
            Self::WrongLaneCount { actual, expected } => write!(
                formatter,
                "global economic lane registry has {actual} entries; expected {expected}"
            ),
            Self::DuplicateLane(lane_id) => write!(
                formatter,
                "duplicate global economic lane: {}",
                lane_id.as_str()
            ),
            Self::NonCanonicalLaneOrder {
                position,
                expected,
                actual,
            } => write!(
                formatter,
                "non-canonical global economic lane at position {position}: expected {}, got {}",
                expected.as_str(),
                actual.as_str()
            ),
            Self::RegistryInvariantViolation => {
                formatter.write_str("global economic lane registry invariant violation")
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived commitment: {field}")
            }
            Self::EmptyInput
            | Self::InputTooLarge { .. }
            | Self::PostcardDecode
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding => self.fmt_codec(formatter),
        }
    }

    fn fmt_codec(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("global economic lane registry input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "global economic lane registry input length {actual} exceeds {maximum}"
            ),
            Self::PostcardDecode => {
                formatter.write_str("global economic lane registry postcard decode failed")
            }
            Self::TrailingBytes => formatter
                .write_str("global economic lane registry postcard input has trailing bytes"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("global economic lane registry postcard input is not canonical")
            }
            _ => formatter.write_str("global economic lane registry semantic rejection"),
        }
    }
}
