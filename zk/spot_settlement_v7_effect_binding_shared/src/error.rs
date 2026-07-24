use core::fmt;

use zenodex_zrpf_protocol_v3::{
    EconomicActionBatchErrorV1, EconomicActionErrorV1, SettlementEffectErrorV2, ZrpfErrorV3,
};
use zenodex_zrpf_risc0_spot_state_root_v5_bridge_shared::RestrictedSpotStateRootV5BridgeError;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpotSettlementV7EffectBindingErrorV1 {
    StateRootBridge(RestrictedSpotStateRootV5BridgeError),
    SettlementPlan(SettlementEffectErrorV2),
    EconomicActionRecord(EconomicActionErrorV1),
    EconomicAction(EconomicActionBatchErrorV1),
    DerivedCommitment(&'static str),
    InvalidIdentifier(&'static str),
    SourcePlanProfile(&'static str),
    UnsupportedStateDelta(&'static str),
    ArithmeticOverflow(&'static str),
    SourceJournalMismatch,
    PreStateRootMismatch,
    PostStateRootMismatch,
    ExpectedSingletonAction,
    ActionNonceMismatch,
    ActionSemanticsMismatch,
    EffectCommitmentMismatch,
    CellWritesMismatch,
    AssetEffectsMismatch,
    UnsupportedOperationalEffects,
    InvalidJournalVersion(u16),
    JournalLength { actual: usize, expected: usize },
    UnexpectedCompatibilityProfile,
    UnexpectedStateRootScheme,
}

impl From<RestrictedSpotStateRootV5BridgeError> for SpotSettlementV7EffectBindingErrorV1 {
    fn from(error: RestrictedSpotStateRootV5BridgeError) -> Self {
        Self::StateRootBridge(error)
    }
}

impl From<SettlementEffectErrorV2> for SpotSettlementV7EffectBindingErrorV1 {
    fn from(error: SettlementEffectErrorV2) -> Self {
        Self::SettlementPlan(error)
    }
}

impl From<EconomicActionErrorV1> for SpotSettlementV7EffectBindingErrorV1 {
    fn from(error: EconomicActionErrorV1) -> Self {
        Self::EconomicActionRecord(error)
    }
}

impl From<EconomicActionBatchErrorV1> for SpotSettlementV7EffectBindingErrorV1 {
    fn from(error: EconomicActionBatchErrorV1) -> Self {
        Self::EconomicAction(error)
    }
}

impl From<ZrpfErrorV3> for SpotSettlementV7EffectBindingErrorV1 {
    fn from(_: ZrpfErrorV3) -> Self {
        Self::DerivedCommitment("zero commitment")
    }
}

impl fmt::Display for SpotSettlementV7EffectBindingErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StateRootBridge(error) => {
                write!(formatter, "state-root bridge rejected: {error}")
            }
            Self::SettlementPlan(error) => write!(formatter, "settlement plan rejected: {error}"),
            Self::EconomicActionRecord(error) => {
                write!(formatter, "economic action record rejected: {error}")
            }
            Self::EconomicAction(error) => write!(formatter, "economic action rejected: {error}"),
            Self::DerivedCommitment(field) => {
                write!(formatter, "derived zero commitment: {field}")
            }
            Self::InvalidIdentifier(field) => write!(formatter, "invalid identifier: {field}"),
            Self::SourcePlanProfile(field) => {
                write!(
                    formatter,
                    "source settlement plan profile mismatch: {field}"
                )
            }
            Self::UnsupportedStateDelta(field) => {
                write!(formatter, "unsupported Spot state delta: {field}")
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::JournalLength { actual, expected } => write!(
                formatter,
                "binding journal length {actual} differs from exact length {expected}"
            ),
            Self::InvalidJournalVersion(version) => {
                write!(formatter, "invalid binding journal version: {version}")
            }
            _ => formatter.write_str(self.static_message()),
        }
    }
}

impl SpotSettlementV7EffectBindingErrorV1 {
    const fn static_message(&self) -> &'static str {
        match self {
            Self::SourceJournalMismatch => "effect plan source journal mismatch",
            Self::PreStateRootMismatch => "effect plan pre-state root mismatch",
            Self::PostStateRootMismatch => "effect plan post-state root mismatch",
            Self::ExpectedSingletonAction => "restricted Spot profile requires one action",
            Self::ActionNonceMismatch => "economic action nonce differs from ingress nonce",
            Self::ActionSemanticsMismatch => "economic action semantics commitment mismatch",
            Self::EffectCommitmentMismatch => "economic action effect commitment mismatch",
            Self::CellWritesMismatch => "ledger cell writes differ from typed state openings",
            Self::AssetEffectsMismatch => "asset effects differ from typed state deltas",
            Self::UnsupportedOperationalEffects => {
                "restricted Spot profile forbids messages, carries, and rewards"
            }
            Self::UnexpectedCompatibilityProfile => "unexpected compatibility profile",
            Self::UnexpectedStateRootScheme => "unexpected state-root scheme",
            _ => "Spot settlement V7 effect binding rejected",
        }
    }
}
