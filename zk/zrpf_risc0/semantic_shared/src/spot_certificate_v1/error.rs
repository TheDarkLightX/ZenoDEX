use core::fmt;

use zenodex_zrpf_protocol_v3::{
    EconomicActionBatchErrorV1, SettlementEffectErrorV2, SettlementEpochCertificateErrorV1,
    ZrpfErrorV3,
};

use crate::SpotSettlementProjectionErrorV1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrdinarySpotSettlementCertificateErrorV1 {
    Projection(SpotSettlementProjectionErrorV1),
    SettlementPlan(SettlementEffectErrorV2),
    ProjectionBatchMismatch,
    ProjectionSourceHashMismatch,
    NonEmptyMessageEffects { actual: usize },
    NonEmptyCarryEffects { actual: usize },
    NonEmptyRewardEffects { actual: usize },
    EconomicBatch(EconomicActionBatchErrorV1),
    Structural(ZrpfErrorV3),
    Certificate(SettlementEpochCertificateErrorV1),
    ArithmeticOverflow(&'static str),
}

impl fmt::Display for OrdinarySpotSettlementCertificateErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Projection(error) => {
                write!(formatter, "ordinary Spot projection rejected: {error}")
            }
            Self::SettlementPlan(error) => {
                write!(formatter, "ordinary Spot settlement plan rejected: {error}")
            }
            Self::ProjectionBatchMismatch => formatter
                .write_str("ordinary Spot projection batch differs from its settlement plan batch"),
            Self::ProjectionSourceHashMismatch => formatter.write_str(
                "ordinary Spot projection source hash differs from its settlement plan source hash",
            ),
            Self::NonEmptyMessageEffects { actual } => write!(
                formatter,
                "ordinary Spot settlement has {actual} message effects"
            ),
            Self::NonEmptyCarryEffects { actual } => write!(
                formatter,
                "ordinary Spot settlement has {actual} carry effects"
            ),
            Self::NonEmptyRewardEffects { actual } => write!(
                formatter,
                "ordinary Spot settlement has {actual} reward effects"
            ),
            Self::EconomicBatch(error) => {
                write!(formatter, "ordinary Spot action batch rejected: {error}")
            }
            Self::Structural(error) => {
                write!(
                    formatter,
                    "ordinary Spot certificate structure rejected: {error}"
                )
            }
            Self::Certificate(error) => {
                write!(formatter, "ordinary Spot certificate rejected: {error}")
            }
            Self::ArithmeticOverflow(field) => write!(
                formatter,
                "ordinary Spot certificate arithmetic overflow: {field}"
            ),
        }
    }
}

impl From<SpotSettlementProjectionErrorV1> for OrdinarySpotSettlementCertificateErrorV1 {
    fn from(error: SpotSettlementProjectionErrorV1) -> Self {
        Self::Projection(error)
    }
}

impl From<SettlementEffectErrorV2> for OrdinarySpotSettlementCertificateErrorV1 {
    fn from(error: SettlementEffectErrorV2) -> Self {
        Self::SettlementPlan(error)
    }
}

impl From<EconomicActionBatchErrorV1> for OrdinarySpotSettlementCertificateErrorV1 {
    fn from(error: EconomicActionBatchErrorV1) -> Self {
        Self::EconomicBatch(error)
    }
}

impl From<ZrpfErrorV3> for OrdinarySpotSettlementCertificateErrorV1 {
    fn from(error: ZrpfErrorV3) -> Self {
        Self::Structural(error)
    }
}

impl From<SettlementEpochCertificateErrorV1> for OrdinarySpotSettlementCertificateErrorV1 {
    fn from(error: SettlementEpochCertificateErrorV1) -> Self {
        Self::Certificate(error)
    }
}
