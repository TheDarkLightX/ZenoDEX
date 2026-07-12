use core::fmt;

use zenodex_zrpf_protocol_v3::{
    FullBlobDataAvailabilityErrorV1, SparseMerkleCellTransitionErrorV1, ValueAggregateErrorV5,
};

use super::super::wire_v2::{ExactWireErrorV2, ExactWireErrorV2::*};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrdinarySpotSettlementGuestInputErrorV2 {
    InvalidVersion(u16),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    TruncatedInput(&'static str),
    InvalidAuthorization(&'static str),
    EmptyProposalBytes,
    ProposalBytesTooLarge { actual: usize, maximum: usize },
    EmptyWitnessBytes,
    WitnessBytesTooLarge { actual: usize, maximum: usize },
    EmptyCertificateBytes,
    CertificateBytesTooLarge { actual: usize, maximum: usize },
    TrailingBytes,
    NonCanonicalEncoding,
    ValueAggregate(ValueAggregateErrorV5),
    Witness(SparseMerkleCellTransitionErrorV1),
    DataAvailability(FullBlobDataAvailabilityErrorV1),
    ArithmeticOverflow(&'static str),
}

impl fmt::Display for OrdinarySpotSettlementGuestInputErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidVersion(version) => {
                write!(formatter, "Spot guest V2 version {version} is invalid")
            }
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "ordinary Spot guest V2 length {actual} exceeds {maximum}"
                )
            }
            Self::TruncatedInput(field) => {
                write!(formatter, "Spot guest V2 is truncated at {field}")
            }
            Self::InvalidAuthorization(field) => {
                write!(
                    formatter,
                    "Spot guest V2 authorization is invalid at {field}"
                )
            }
            Self::ProposalBytesTooLarge { actual, maximum } => write!(
                formatter,
                "ordinary Spot guest V2 proposal length {actual} exceeds {maximum}"
            ),
            Self::WitnessBytesTooLarge { actual, maximum } => write!(
                formatter,
                "ordinary Spot guest V2 witness length {actual} exceeds {maximum}"
            ),
            Self::CertificateBytesTooLarge { actual, maximum } => write!(
                formatter,
                "ordinary Spot guest V2 certificate length {actual} exceeds {maximum}"
            ),
            Self::ValueAggregate(error) => write!(formatter, "guest V2 proposal rejected: {error}"),
            Self::Witness(error) => write!(formatter, "guest V2 witness rejected: {error}"),
            Self::DataAvailability(error) => {
                write!(formatter, "guest V2 DA certificate rejected: {error}")
            }
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "Spot guest V2 arithmetic overflow: {field}")
            }
            Self::EmptyInput
            | Self::EmptyProposalBytes
            | Self::EmptyWitnessBytes
            | Self::EmptyCertificateBytes
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding => formatter.write_str(self.static_message()),
        }
    }
}

impl OrdinarySpotSettlementGuestInputErrorV2 {
    fn static_message(&self) -> &'static str {
        match self {
            Self::EmptyInput => "ordinary Spot guest V2 input is empty",
            Self::EmptyProposalBytes => "ordinary Spot guest V2 proposal bytes are empty",
            Self::EmptyWitnessBytes => "ordinary Spot guest V2 witness bytes are empty",
            Self::EmptyCertificateBytes => "ordinary Spot guest V2 certificate bytes are empty",
            Self::TrailingBytes => "ordinary Spot guest V2 has trailing bytes",
            Self::NonCanonicalEncoding => "ordinary Spot guest V2 encoding is noncanonical",
            Self::InvalidVersion(_)
            | Self::InputTooLarge { .. }
            | Self::TruncatedInput(_)
            | Self::InvalidAuthorization(_)
            | Self::ProposalBytesTooLarge { .. }
            | Self::WitnessBytesTooLarge { .. }
            | Self::CertificateBytesTooLarge { .. }
            | Self::ValueAggregate(_)
            | Self::Witness(_)
            | Self::DataAvailability(_)
            | Self::ArithmeticOverflow(_) => "ordinary Spot settlement guest V2 error",
        }
    }
}

impl From<ValueAggregateErrorV5> for OrdinarySpotSettlementGuestInputErrorV2 {
    fn from(error: ValueAggregateErrorV5) -> Self {
        Self::ValueAggregate(error)
    }
}

impl From<SparseMerkleCellTransitionErrorV1> for OrdinarySpotSettlementGuestInputErrorV2 {
    fn from(error: SparseMerkleCellTransitionErrorV1) -> Self {
        Self::Witness(error)
    }
}

impl From<FullBlobDataAvailabilityErrorV1> for OrdinarySpotSettlementGuestInputErrorV2 {
    fn from(error: FullBlobDataAvailabilityErrorV1) -> Self {
        Self::DataAvailability(error)
    }
}

impl From<ExactWireErrorV2> for OrdinarySpotSettlementGuestInputErrorV2 {
    fn from(error: ExactWireErrorV2) -> Self {
        match error {
            Truncated(field) => Self::TruncatedInput(field),
            InvalidAuthorization(field) => Self::InvalidAuthorization(field),
            ArithmeticOverflow(field) => Self::ArithmeticOverflow(field),
        }
    }
}
