use core::fmt;

use zenodex_zrpf_protocol_v3::{SettlementEffectErrorV2, ValueAggregateErrorV5};

use crate::SpotSettlementProjectionErrorV1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrdinarySpotSettlementReplayDataErrorV1 {
    InvalidVersion(u16),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    TruncatedInput(&'static str),
    EmptyProposalBytes,
    ProposalBytesTooLarge { actual: usize, maximum: usize },
    EmptyPlanBytes,
    PlanBytesTooLarge { actual: usize, maximum: usize },
    TrailingBytes,
    NonCanonicalEncoding,
    PlanActionCount { actual: usize, expected: usize },
    RecomposedPlanMismatch,
    ValueAggregate(ValueAggregateErrorV5),
    SettlementPlan(SettlementEffectErrorV2),
    Projection(SpotSettlementProjectionErrorV1),
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
}

impl fmt::Display for OrdinarySpotSettlementReplayDataErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidVersion(version) => {
                write!(
                    formatter,
                    "ordinary Spot replay version {version} is invalid"
                )
            }
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "ordinary Spot replay-data length {actual} exceeds {maximum}"
            ),
            Self::TruncatedInput(field) => {
                write!(formatter, "ordinary Spot replay is truncated at {field}")
            }
            Self::ProposalBytesTooLarge { actual, maximum } => write!(
                formatter,
                "ordinary Spot replay V5 proposal length {actual} exceeds {maximum}"
            ),
            Self::PlanBytesTooLarge { actual, maximum } => write!(
                formatter,
                "ordinary Spot replay settlement plan length {actual} exceeds {maximum}"
            ),
            Self::PlanActionCount { actual, expected } => write!(
                formatter,
                "ordinary Spot replay plan action count {actual} differs from {expected}"
            ),
            Self::ValueAggregate(error) => {
                write!(formatter, "ordinary Spot replay proposal rejected: {error}")
            }
            Self::SettlementPlan(error) => write!(
                formatter,
                "ordinary Spot replay settlement plan rejected: {error}"
            ),
            Self::Projection(error) => {
                write!(
                    formatter,
                    "ordinary Spot replay projection rejected: {error}"
                )
            }
            Self::ArithmeticOverflow(field) => {
                write!(
                    formatter,
                    "ordinary Spot replay arithmetic overflow: {field}"
                )
            }
            Self::InvalidDerivedCommitment(field) => write!(
                formatter,
                "invalid derived ordinary Spot replay commitment: {field}"
            ),
            Self::EmptyInput
            | Self::EmptyProposalBytes
            | Self::EmptyPlanBytes
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding
            | Self::RecomposedPlanMismatch => formatter.write_str(self.static_message()),
        }
    }
}

impl OrdinarySpotSettlementReplayDataErrorV1 {
    fn static_message(&self) -> &'static str {
        match self {
            Self::EmptyInput => "ordinary Spot replay-data input is empty",
            Self::EmptyProposalBytes => "ordinary Spot replay data has empty V5 proposal bytes",
            Self::EmptyPlanBytes => "ordinary Spot replay data has empty settlement plan bytes",
            Self::TrailingBytes => "ordinary Spot replay data has trailing bytes",
            Self::NonCanonicalEncoding => "ordinary Spot replay-data encoding is noncanonical",
            Self::RecomposedPlanMismatch => {
                "ordinary Spot replay plan differs from deterministic V5 recomposition"
            }
            Self::InvalidVersion(_)
            | Self::InputTooLarge { .. }
            | Self::TruncatedInput(_)
            | Self::ProposalBytesTooLarge { .. }
            | Self::PlanBytesTooLarge { .. }
            | Self::PlanActionCount { .. }
            | Self::ValueAggregate(_)
            | Self::SettlementPlan(_)
            | Self::Projection(_)
            | Self::ArithmeticOverflow(_)
            | Self::InvalidDerivedCommitment(_) => "ordinary Spot settlement replay-data error",
        }
    }
}

impl From<ValueAggregateErrorV5> for OrdinarySpotSettlementReplayDataErrorV1 {
    fn from(error: ValueAggregateErrorV5) -> Self {
        Self::ValueAggregate(error)
    }
}

impl From<SettlementEffectErrorV2> for OrdinarySpotSettlementReplayDataErrorV1 {
    fn from(error: SettlementEffectErrorV2) -> Self {
        Self::SettlementPlan(error)
    }
}

impl From<SpotSettlementProjectionErrorV1> for OrdinarySpotSettlementReplayDataErrorV1 {
    fn from(error: SpotSettlementProjectionErrorV1) -> Self {
        Self::Projection(error)
    }
}
