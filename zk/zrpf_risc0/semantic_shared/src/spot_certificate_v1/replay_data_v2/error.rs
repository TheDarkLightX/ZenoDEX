use core::fmt;

use zenodex_zrpf_protocol_v3::{
    SettlementEffectErrorV2, SparseMerkleCellTransitionErrorV1, ValueAggregateErrorV5,
};

use crate::SpotSettlementProjectionErrorV1;

use super::super::wire_v2::{ExactWireErrorV2, ExactWireErrorV2::*};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrdinarySpotSettlementReplayDataErrorV2 {
    InvalidVersion(u16),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    TruncatedInput(&'static str),
    InvalidAuthorization(&'static str),
    EmptyProposalBytes,
    ProposalBytesTooLarge { actual: usize, maximum: usize },
    EmptyWitnessBytes,
    WitnessBytesTooLarge { actual: usize, maximum: usize },
    EmptyPlanBytes,
    PlanBytesTooLarge { actual: usize, maximum: usize },
    TrailingBytes,
    NonCanonicalEncoding,
    RecomposedPlanMismatch,
    ValueAggregate(ValueAggregateErrorV5),
    Witness(SparseMerkleCellTransitionErrorV1),
    SettlementPlan(SettlementEffectErrorV2),
    Projection(SpotSettlementProjectionErrorV1),
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
}

impl fmt::Display for OrdinarySpotSettlementReplayDataErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidVersion(version) => {
                write!(formatter, "Spot replay V2 version {version} is invalid")
            }
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "ordinary Spot replay V2 length {actual} exceeds {maximum}"
                )
            }
            Self::TruncatedInput(field) => {
                write!(formatter, "Spot replay V2 is truncated at {field}")
            }
            Self::InvalidAuthorization(field) => {
                write!(
                    formatter,
                    "Spot replay V2 authorization is invalid at {field}"
                )
            }
            Self::ProposalBytesTooLarge { actual, maximum } => write!(
                formatter,
                "ordinary Spot replay V2 proposal length {actual} exceeds {maximum}"
            ),
            Self::WitnessBytesTooLarge { actual, maximum } => write!(
                formatter,
                "ordinary Spot replay V2 witness length {actual} exceeds {maximum}"
            ),
            Self::PlanBytesTooLarge { actual, maximum } => write!(
                formatter,
                "ordinary Spot replay V2 plan length {actual} exceeds {maximum}"
            ),
            Self::ValueAggregate(error) => {
                write!(formatter, "replay V2 proposal rejected: {error}")
            }
            Self::Witness(error) => write!(formatter, "replay V2 witness rejected: {error}"),
            Self::SettlementPlan(error) => write!(formatter, "replay V2 plan rejected: {error}"),
            Self::Projection(error) => write!(formatter, "replay V2 projection rejected: {error}"),
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "Spot replay V2 arithmetic overflow: {field}")
            }
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "Spot replay V2 invalid commitment: {field}")
            }
            Self::EmptyInput
            | Self::EmptyProposalBytes
            | Self::EmptyWitnessBytes
            | Self::EmptyPlanBytes
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding
            | Self::RecomposedPlanMismatch => formatter.write_str(self.static_message()),
        }
    }
}

impl OrdinarySpotSettlementReplayDataErrorV2 {
    fn static_message(&self) -> &'static str {
        match self {
            Self::EmptyInput => "ordinary Spot replay V2 input is empty",
            Self::EmptyProposalBytes => "ordinary Spot replay V2 proposal bytes are empty",
            Self::EmptyWitnessBytes => "ordinary Spot replay V2 witness bytes are empty",
            Self::EmptyPlanBytes => "ordinary Spot replay V2 plan bytes are empty",
            Self::TrailingBytes => "ordinary Spot replay V2 has trailing bytes",
            Self::NonCanonicalEncoding => "ordinary Spot replay V2 encoding is noncanonical",
            Self::RecomposedPlanMismatch => {
                "ordinary Spot replay V2 plan differs from state-bound recomposition"
            }
            Self::InvalidVersion(_)
            | Self::InputTooLarge { .. }
            | Self::TruncatedInput(_)
            | Self::InvalidAuthorization(_)
            | Self::ProposalBytesTooLarge { .. }
            | Self::WitnessBytesTooLarge { .. }
            | Self::PlanBytesTooLarge { .. }
            | Self::ValueAggregate(_)
            | Self::Witness(_)
            | Self::SettlementPlan(_)
            | Self::Projection(_)
            | Self::ArithmeticOverflow(_)
            | Self::InvalidDerivedCommitment(_) => "ordinary Spot settlement replay V2 error",
        }
    }
}

impl From<ValueAggregateErrorV5> for OrdinarySpotSettlementReplayDataErrorV2 {
    fn from(error: ValueAggregateErrorV5) -> Self {
        Self::ValueAggregate(error)
    }
}

impl From<SparseMerkleCellTransitionErrorV1> for OrdinarySpotSettlementReplayDataErrorV2 {
    fn from(error: SparseMerkleCellTransitionErrorV1) -> Self {
        Self::Witness(error)
    }
}

impl From<SettlementEffectErrorV2> for OrdinarySpotSettlementReplayDataErrorV2 {
    fn from(error: SettlementEffectErrorV2) -> Self {
        Self::SettlementPlan(error)
    }
}

impl From<SpotSettlementProjectionErrorV1> for OrdinarySpotSettlementReplayDataErrorV2 {
    fn from(error: SpotSettlementProjectionErrorV1) -> Self {
        Self::Projection(error)
    }
}

impl From<ExactWireErrorV2> for OrdinarySpotSettlementReplayDataErrorV2 {
    fn from(error: ExactWireErrorV2) -> Self {
        match error {
            Truncated(field) => Self::TruncatedInput(field),
            InvalidAuthorization(field) => Self::InvalidAuthorization(field),
            ArithmeticOverflow(field) => Self::ArithmeticOverflow(field),
        }
    }
}
