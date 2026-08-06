use core::fmt;

use crate::{CommitmentV3, EconomicActionBatchErrorV1};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GlobalEconomicEffectPlanErrorV1 {
    EconomicAction(EconomicActionBatchErrorV1),
    InvalidVersion(u16),
    EmptyEffects,
    TooManyEffects { actual: usize, maximum: usize },
    EmptyReconciliations,
    TooManyReconciliations { actual: usize, maximum: usize },
    ZeroAmount(&'static str),
    SelfTransfer(&'static str),
    NonChangingEffect(&'static str),
    CustodyClaimMismatch,
    FeeAllocationMismatch,
    DuplicateEffect,
    DuplicateWriteTarget(&'static str, CommitmentV3),
    DuplicateAssetReconciliation(CommitmentV3),
    NonCanonicalOrder(&'static str),
    MissingAssetReconciliation(CommitmentV3),
    ReconciliationWithoutEffect(CommitmentV3),
    AssetConservationViolation(CommitmentV3),
    OwnedConservationViolation(CommitmentV3),
    SupplyConservationViolation(CommitmentV3),
    LiabilityReconciliationViolation(CommitmentV3),
    ReserveReconciliationViolation(CommitmentV3),
    InternalOutboxDestination,
    OutboxValueEffectMismatch,
    DuplicateOutboxValueEffect,
    PreAndPostStateMatch,
    CommitmentMismatch(&'static str),
    ApplicationMismatch,
    DomainMismatch,
    ProfileMismatch,
    WriterEpochMismatch,
    OccurrenceMismatch,
    RouteMismatch,
    PreStateMismatch,
    EffectCommitmentMismatch,
    AuthorizationMismatch,
    IssueBurnPolicyMismatch,
    ConsumedObjectMismatch,
    AuthorizationGrantSpendMismatch,
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl From<EconomicActionBatchErrorV1> for GlobalEconomicEffectPlanErrorV1 {
    fn from(error: EconomicActionBatchErrorV1) -> Self {
        Self::EconomicAction(error)
    }
}

impl fmt::Display for GlobalEconomicEffectPlanErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EconomicAction(_)
            | Self::InvalidVersion(_)
            | Self::EmptyEffects
            | Self::TooManyEffects { .. }
            | Self::EmptyReconciliations
            | Self::TooManyReconciliations { .. }
            | Self::ZeroAmount(_)
            | Self::SelfTransfer(_)
            | Self::NonChangingEffect(_)
            | Self::CustodyClaimMismatch
            | Self::FeeAllocationMismatch
            | Self::DuplicateEffect
            | Self::DuplicateWriteTarget(_, _)
            | Self::DuplicateAssetReconciliation(_)
            | Self::NonCanonicalOrder(_) => self.fmt_shape(formatter),
            Self::MissingAssetReconciliation(_)
            | Self::ReconciliationWithoutEffect(_)
            | Self::AssetConservationViolation(_)
            | Self::OwnedConservationViolation(_)
            | Self::SupplyConservationViolation(_)
            | Self::LiabilityReconciliationViolation(_)
            | Self::ReserveReconciliationViolation(_)
            | Self::InternalOutboxDestination
            | Self::OutboxValueEffectMismatch
            | Self::DuplicateOutboxValueEffect => self.fmt_reconciliation(formatter),
            Self::PreAndPostStateMatch
            | Self::CommitmentMismatch(_)
            | Self::ApplicationMismatch
            | Self::DomainMismatch
            | Self::ProfileMismatch
            | Self::WriterEpochMismatch
            | Self::OccurrenceMismatch
            | Self::RouteMismatch
            | Self::PreStateMismatch
            | Self::EffectCommitmentMismatch
            | Self::AuthorizationMismatch
            | Self::IssueBurnPolicyMismatch
            | Self::ConsumedObjectMismatch
            | Self::AuthorizationGrantSpendMismatch => self.fmt_binding(formatter),
            Self::ArithmeticOverflow(_)
            | Self::InvalidDerivedCommitment(_)
            | Self::EmptyInput
            | Self::InputTooLarge { .. }
            | Self::PostcardDecode
            | Self::TrailingBytes
            | Self::NonCanonicalEncoding => self.fmt_codec(formatter),
        }
    }
}

impl GlobalEconomicEffectPlanErrorV1 {
    fn fmt_shape(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EconomicAction(error) => write!(formatter, "economic action rejected: {error}"),
            Self::InvalidVersion(version) => {
                write!(formatter, "invalid global effect plan version: {version}")
            }
            Self::EmptyEffects => formatter.write_str("global effect plan is empty"),
            Self::TooManyEffects { actual, maximum } => write!(
                formatter,
                "global effect row count {actual} exceeds {maximum}"
            ),
            Self::EmptyReconciliations => {
                formatter.write_str("global asset reconciliations are empty")
            }
            Self::TooManyReconciliations { actual, maximum } => write!(
                formatter,
                "global asset reconciliation count {actual} exceeds {maximum}"
            ),
            Self::ZeroAmount(kind) => write!(formatter, "zero amount in {kind} effect"),
            Self::SelfTransfer(kind) => write!(formatter, "{kind} source equals destination"),
            Self::NonChangingEffect(kind) => {
                write!(formatter, "{kind} effect does not change state")
            }
            Self::CustodyClaimMismatch => formatter
                .write_str("custody differs from claimant entitlements plus unencumbered reserves"),
            Self::FeeAllocationMismatch => {
                formatter.write_str("fee charged differs from allocations plus carried residue")
            }
            Self::DuplicateEffect => formatter.write_str("duplicate global economic effect row"),
            Self::DuplicateWriteTarget(kind, target) => {
                write!(formatter, "duplicate {kind} write target {target:?}")
            }
            Self::DuplicateAssetReconciliation(asset) => {
                write!(formatter, "duplicate reconciliation for asset {asset:?}")
            }
            Self::NonCanonicalOrder(field) => write!(formatter, "non-canonical order: {field}"),
            _ => formatter.write_str("invalid global effect-plan shape error group"),
        }
    }

    fn fmt_reconciliation(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingAssetReconciliation(asset) => {
                write!(formatter, "missing reconciliation for asset {asset:?}")
            }
            Self::ReconciliationWithoutEffect(asset) => write!(
                formatter,
                "reconciliation has no effect row for asset {asset:?}"
            ),
            Self::AssetConservationViolation(asset) => {
                write!(formatter, "asset flow conservation violated for {asset:?}")
            }
            Self::OwnedConservationViolation(asset) => write!(
                formatter,
                "owned-and-custodied conservation violated for {asset:?}"
            ),
            Self::SupplyConservationViolation(asset) => {
                write!(formatter, "supply conservation violated for {asset:?}")
            }
            Self::LiabilityReconciliationViolation(asset) => write!(
                formatter,
                "liability delta reconciliation violated for {asset:?}"
            ),
            Self::ReserveReconciliationViolation(asset) => write!(
                formatter,
                "reserve delta reconciliation violated for {asset:?}"
            ),
            Self::InternalOutboxDestination => {
                formatter.write_str("same-ledger movement cannot enter the external outbox")
            }
            Self::OutboxValueEffectMismatch => {
                formatter.write_str("external outbox row lacks one exact value effect")
            }
            Self::DuplicateOutboxValueEffect => {
                formatter.write_str("one value effect funds more than one outbox row")
            }
            _ => formatter.write_str("invalid global effect-plan reconciliation error group"),
        }
    }

    fn fmt_binding(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PreAndPostStateMatch => {
                formatter.write_str("global effect plan pre-state equals post-state")
            }
            Self::CommitmentMismatch(field) => {
                write!(formatter, "global effect plan commitment mismatch: {field}")
            }
            Self::ApplicationMismatch => formatter.write_str("effect plan application mismatch"),
            Self::DomainMismatch => formatter.write_str("effect plan domain mismatch"),
            Self::ProfileMismatch => formatter.write_str("effect plan profile mismatch"),
            Self::WriterEpochMismatch => formatter.write_str("effect plan writer epoch mismatch"),
            Self::OccurrenceMismatch => formatter.write_str("effect plan occurrence mismatch"),
            Self::RouteMismatch => formatter.write_str("effect plan route mismatch"),
            Self::PreStateMismatch => formatter.write_str("effect plan pre-state mismatch"),
            Self::EffectCommitmentMismatch => {
                formatter.write_str("authorized action effect commitment mismatch")
            }
            Self::AuthorizationMismatch => formatter.write_str("effect row authorization mismatch"),
            Self::IssueBurnPolicyMismatch => {
                formatter.write_str("effect rows violate the governed route issue/burn policy")
            }
            Self::ConsumedObjectMismatch => {
                formatter.write_str("effect plan consumed objects differ from the occurrence")
            }
            Self::AuthorizationGrantSpendMismatch => formatter
                .write_str("effect plan authorization grant spend differs from the occurrence"),
            _ => formatter.write_str("invalid global effect-plan binding error group"),
        }
    }

    fn fmt_codec(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived commitment: {field}")
            }
            Self::EmptyInput => formatter.write_str("global effect plan input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "global effect plan input length {actual} exceeds {maximum}"
            ),
            Self::PostcardDecode => {
                formatter.write_str("global effect plan postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("global effect plan postcard input has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("global effect plan postcard input is not canonical")
            }
            _ => formatter.write_str("invalid global effect-plan codec error group"),
        }
    }
}
