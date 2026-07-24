use core::fmt;

use zenodex_zrpf_protocol_v3::{
    SettlementAdmissionJournalErrorV1, SettlementEffectErrorV2, SettlementEpochCertificateErrorV1,
    ValueAggregateErrorV5,
};
use zenodex_zrpf_risc0_semantic_shared::{
    OrdinarySpotSettlementCertificateErrorV1, OrdinarySpotSettlementGuestInputErrorV2,
    OrdinarySpotSettlementReplayDataErrorV2,
};
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::SourceOpenedSpotValueLeafErrorV6;
use zenodex_zrpf_risc0_value_aggregate_shared::ValueAggregateRecompositionErrorV5;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceOpenedSpotSettlementErrorV6 {
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    InvalidVersion(u16),
    EmptyComponent(&'static str),
    ComponentTooLarge {
        component: &'static str,
        actual: usize,
        maximum: usize,
    },
    Truncated(&'static str),
    TrailingBytes,
    NonCanonicalReplay,
    LengthOverflow(&'static str),
    BaseInput(OrdinarySpotSettlementGuestInputErrorV2),
    SourceLeaf(SourceOpenedSpotValueLeafErrorV6),
    Proposal(ValueAggregateErrorV5),
    Aggregate(ValueAggregateRecompositionErrorV5),
    InvalidSingletonRelation(&'static str),
    Replay(OrdinarySpotSettlementReplayDataErrorV2),
    Certificate(OrdinarySpotSettlementCertificateErrorV1),
    Output(SettlementEpochCertificateErrorV1),
    EffectPlan(SettlementEffectErrorV2),
    Admission(SettlementAdmissionJournalErrorV1),
    InvalidDerivedCommitment(&'static str),
}

impl fmt::Display for SourceOpenedSpotSettlementErrorV6 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "source-opened settlement input {actual} exceeds {maximum}"
                )
            }
            Self::InvalidVersion(version) => {
                write!(
                    formatter,
                    "source-opened settlement version {version} is invalid"
                )
            }
            Self::EmptyComponent(component) => write!(formatter, "{component} is empty"),
            Self::ComponentTooLarge {
                component,
                actual,
                maximum,
            } => write!(formatter, "{component} length {actual} exceeds {maximum}"),
            Self::Truncated(field) => {
                write!(formatter, "source-opened settlement truncated at {field}")
            }
            Self::LengthOverflow(field) => {
                write!(
                    formatter,
                    "source-opened settlement length overflow at {field}"
                )
            }
            Self::BaseInput(error) => write!(formatter, "base settlement input rejected: {error}"),
            Self::SourceLeaf(error) => write!(formatter, "source-opened V6 leaf rejected: {error}"),
            Self::Proposal(error) => write!(formatter, "L2 proposal rejected: {error}"),
            Self::Aggregate(error) => write!(formatter, "V6 aggregate relation rejected: {error}"),
            Self::InvalidSingletonRelation(field) => {
                write!(
                    formatter,
                    "source-opened singleton relation rejected: {field}"
                )
            }
            Self::Replay(error) => write!(formatter, "source-opened replay rejected: {error}"),
            Self::Certificate(error) => {
                write!(
                    formatter,
                    "source-opened settlement certificate rejected: {error}"
                )
            }
            Self::Output(error) => write!(formatter, "source-opened output rejected: {error}"),
            Self::EffectPlan(error) => {
                write!(formatter, "source-opened effect plan rejected: {error}")
            }
            Self::Admission(error) => write!(
                formatter,
                "source-opened admission journal rejected: {error}"
            ),
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid source-opened commitment: {field}")
            }
            Self::EmptyInput => formatter.write_str("source-opened settlement input is empty"),
            Self::TrailingBytes => {
                formatter.write_str("source-opened settlement input has trailing bytes")
            }
            Self::NonCanonicalReplay => {
                formatter.write_str("source-opened settlement replay is not canonical")
            }
        }
    }
}

impl From<OrdinarySpotSettlementGuestInputErrorV2> for SourceOpenedSpotSettlementErrorV6 {
    fn from(error: OrdinarySpotSettlementGuestInputErrorV2) -> Self {
        Self::BaseInput(error)
    }
}

impl From<SourceOpenedSpotValueLeafErrorV6> for SourceOpenedSpotSettlementErrorV6 {
    fn from(error: SourceOpenedSpotValueLeafErrorV6) -> Self {
        Self::SourceLeaf(error)
    }
}

impl From<ValueAggregateErrorV5> for SourceOpenedSpotSettlementErrorV6 {
    fn from(error: ValueAggregateErrorV5) -> Self {
        Self::Proposal(error)
    }
}

impl From<ValueAggregateRecompositionErrorV5> for SourceOpenedSpotSettlementErrorV6 {
    fn from(error: ValueAggregateRecompositionErrorV5) -> Self {
        Self::Aggregate(error)
    }
}

impl From<OrdinarySpotSettlementReplayDataErrorV2> for SourceOpenedSpotSettlementErrorV6 {
    fn from(error: OrdinarySpotSettlementReplayDataErrorV2) -> Self {
        Self::Replay(error)
    }
}

impl From<OrdinarySpotSettlementCertificateErrorV1> for SourceOpenedSpotSettlementErrorV6 {
    fn from(error: OrdinarySpotSettlementCertificateErrorV1) -> Self {
        Self::Certificate(error)
    }
}

impl From<SettlementEpochCertificateErrorV1> for SourceOpenedSpotSettlementErrorV6 {
    fn from(error: SettlementEpochCertificateErrorV1) -> Self {
        Self::Output(error)
    }
}

impl From<SettlementEffectErrorV2> for SourceOpenedSpotSettlementErrorV6 {
    fn from(error: SettlementEffectErrorV2) -> Self {
        Self::EffectPlan(error)
    }
}

impl From<SettlementAdmissionJournalErrorV1> for SourceOpenedSpotSettlementErrorV6 {
    fn from(error: SettlementAdmissionJournalErrorV1) -> Self {
        Self::Admission(error)
    }
}
