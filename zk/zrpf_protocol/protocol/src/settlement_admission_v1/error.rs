use core::fmt;

use crate::{SettlementEffectErrorV2, SettlementEpochCertificateErrorV1};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SettlementAdmissionJournalErrorV1 {
    Certificate(SettlementEpochCertificateErrorV1),
    EffectPlan(SettlementEffectErrorV2),
    CertificatePlanMismatch(&'static str),
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    InvalidMagic,
    InvalidVersion(u16),
    TruncatedInput,
    TrailingBytes,
    FrameLengthMismatch,
    CertificateLengthInvalid,
    EffectPlanLengthInvalid,
    CertificateHashMismatch,
    EffectPlanHashMismatch,
    DuplicatedFieldMismatch,
}

impl From<SettlementEpochCertificateErrorV1> for SettlementAdmissionJournalErrorV1 {
    fn from(error: SettlementEpochCertificateErrorV1) -> Self {
        Self::Certificate(error)
    }
}

impl From<SettlementEffectErrorV2> for SettlementAdmissionJournalErrorV1 {
    fn from(error: SettlementEffectErrorV2) -> Self {
        Self::EffectPlan(error)
    }
}

impl fmt::Display for SettlementAdmissionJournalErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Certificate(error) => {
                write!(formatter, "settlement certificate rejected: {error}")
            }
            Self::EffectPlan(error) => {
                write!(formatter, "settlement effect plan rejected: {error}")
            }
            Self::CertificatePlanMismatch(field) => {
                write!(
                    formatter,
                    "settlement certificate and effect plan disagree: {field}"
                )
            }
            Self::ArithmeticOverflow(field) => {
                write!(
                    formatter,
                    "settlement admission arithmetic overflow: {field}"
                )
            }
            Self::InvalidDerivedCommitment(field) => {
                write!(
                    formatter,
                    "invalid derived settlement admission commitment: {field}"
                )
            }
            Self::EmptyInput => formatter.write_str("settlement admission journal input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "settlement admission journal input length {actual} exceeds {maximum}"
            ),
            Self::InvalidMagic => formatter.write_str("invalid settlement admission journal magic"),
            Self::InvalidVersion(version) => {
                write!(
                    formatter,
                    "invalid settlement admission journal version: {version}"
                )
            }
            Self::TruncatedInput => {
                formatter.write_str("settlement admission journal is truncated")
            }
            Self::TrailingBytes => {
                formatter.write_str("settlement admission journal has trailing bytes")
            }
            Self::FrameLengthMismatch => {
                formatter.write_str("settlement admission journal frame length mismatch")
            }
            Self::CertificateLengthInvalid => {
                formatter.write_str("settlement admission certificate length is invalid")
            }
            Self::EffectPlanLengthInvalid => {
                formatter.write_str("settlement admission effect plan length is invalid")
            }
            Self::CertificateHashMismatch => {
                formatter.write_str("settlement admission certificate SHA-256 mismatch")
            }
            Self::EffectPlanHashMismatch => {
                formatter.write_str("settlement admission effect plan SHA-256 mismatch")
            }
            Self::DuplicatedFieldMismatch => formatter.write_str(
                "settlement admission duplicated field differs from canonical inner objects",
            ),
        }
    }
}
