use core::fmt;

use zenodex_zrpf_protocol_v3::{
    EconomicActionBatchErrorV1, FullBlobDataAvailabilityErrorV1, SettlementEffectErrorV2,
    SettlementEpochCertificateErrorV1, ZrpfErrorV3,
};

use super::OrdinarySpotSettlementReplayDataErrorV1;
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
    ReplayData(OrdinarySpotSettlementReplayDataErrorV1),
    DataAvailability(FullBlobDataAvailabilityErrorV1),
    DataAvailabilityApplicationMismatch,
    DataAvailabilityDomainMismatch,
    DataAvailabilityEpochMismatch,
    DataAvailabilityStoragePolicyMismatch,
    DataAvailabilitySchemaMismatch,
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
            Self::ReplayData(error) => {
                write!(formatter, "ordinary Spot replay data rejected: {error}")
            }
            Self::DataAvailability(error) => {
                write!(formatter, "ordinary Spot full-blob data rejected: {error}")
            }
            Self::ArithmeticOverflow(field) => {
                write!(
                    formatter,
                    "ordinary Spot certificate arithmetic overflow: {field}"
                )
            }
            Self::ProjectionBatchMismatch
            | Self::ProjectionSourceHashMismatch
            | Self::DataAvailabilityApplicationMismatch
            | Self::DataAvailabilityDomainMismatch
            | Self::DataAvailabilityEpochMismatch
            | Self::DataAvailabilityStoragePolicyMismatch
            | Self::DataAvailabilitySchemaMismatch => formatter.write_str(self.static_message()),
        }
    }
}

impl OrdinarySpotSettlementCertificateErrorV1 {
    fn static_message(&self) -> &'static str {
        match self {
            Self::ProjectionBatchMismatch => {
                "ordinary Spot projection batch differs from its settlement plan batch"
            }
            Self::ProjectionSourceHashMismatch => {
                "ordinary Spot projection source hash differs from its settlement plan source hash"
            }
            Self::DataAvailabilityApplicationMismatch => {
                "ordinary Spot DA application differs from the V5 scope"
            }
            Self::DataAvailabilityDomainMismatch => {
                "ordinary Spot DA domain differs from the V5 scope"
            }
            Self::DataAvailabilityEpochMismatch => {
                "ordinary Spot DA epoch differs from the V5 scope"
            }
            Self::DataAvailabilityStoragePolicyMismatch => {
                "ordinary Spot DA storage policy differs from the V5 public policy"
            }
            Self::DataAvailabilitySchemaMismatch => {
                "ordinary Spot DA schema differs from the replay-data schema"
            }
            Self::Projection(_)
            | Self::SettlementPlan(_)
            | Self::NonEmptyMessageEffects { .. }
            | Self::NonEmptyCarryEffects { .. }
            | Self::NonEmptyRewardEffects { .. }
            | Self::EconomicBatch(_)
            | Self::Structural(_)
            | Self::Certificate(_)
            | Self::ReplayData(_)
            | Self::DataAvailability(_)
            | Self::ArithmeticOverflow(_) => "ordinary Spot settlement certificate error",
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

impl From<OrdinarySpotSettlementReplayDataErrorV1> for OrdinarySpotSettlementCertificateErrorV1 {
    fn from(error: OrdinarySpotSettlementReplayDataErrorV1) -> Self {
        Self::ReplayData(error)
    }
}

impl From<FullBlobDataAvailabilityErrorV1> for OrdinarySpotSettlementCertificateErrorV1 {
    fn from(error: FullBlobDataAvailabilityErrorV1) -> Self {
        Self::DataAvailability(error)
    }
}
