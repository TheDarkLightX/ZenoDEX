use core::fmt;

use super::EconomicActionErrorV1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EconomicActionBatchErrorV1 {
    Action(EconomicActionErrorV1),
    InvalidVersion(u16),
    EmptyActions,
    TooManyActions { actual: usize, maximum: usize },
    ApplicationMismatch,
    DomainMismatch,
    EpochOutsideActionValidity,
    PreStateMismatch,
    DuplicateAction,
    DuplicateActionAuthorizationBinding,
    DuplicateAuthorizationGrantSpend,
    DuplicateConsumedObject,
    NonCanonicalActionOrder,
    CommitmentMismatch(&'static str),
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl From<EconomicActionErrorV1> for EconomicActionBatchErrorV1 {
    fn from(error: EconomicActionErrorV1) -> Self {
        Self::Action(error)
    }
}

impl fmt::Display for EconomicActionBatchErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_semantic(formatter)
    }
}

impl EconomicActionBatchErrorV1 {
    fn fmt_semantic(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Action(error) => write!(formatter, "economic action rejected: {error}"),
            Self::InvalidVersion(version) => {
                write!(
                    formatter,
                    "invalid economic action batch version: {version}"
                )
            }
            Self::EmptyActions => formatter.write_str("economic action batch is empty"),
            Self::TooManyActions { actual, maximum } => {
                write!(
                    formatter,
                    "economic action count {actual} exceeds {maximum}"
                )
            }
            Self::ApplicationMismatch => {
                formatter.write_str("economic actions use different applications")
            }
            Self::DomainMismatch => {
                formatter.write_str("economic actions use different chain or domain IDs")
            }
            Self::EpochOutsideActionValidity => {
                formatter.write_str("batch epoch is outside an action validity interval")
            }
            Self::PreStateMismatch => {
                formatter.write_str("economic action pre-state differs from batch pre-state")
            }
            Self::DuplicateAction => formatter.write_str("duplicate economic action"),
            Self::DuplicateActionAuthorizationBinding => {
                formatter.write_str("duplicate action authorization binding")
            }
            Self::DuplicateAuthorizationGrantSpend => {
                formatter.write_str("duplicate authorization grant-and-nonce spend")
            }
            Self::DuplicateConsumedObject => {
                formatter.write_str("consumed object appears in multiple economic actions")
            }
            Self::NonCanonicalActionOrder => {
                formatter.write_str("economic actions are not strictly ordered by action ID")
            }
            Self::CommitmentMismatch(field) => {
                write!(
                    formatter,
                    "economic action batch commitment mismatch: {field}"
                )
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
            Self::EmptyInput => formatter.write_str("economic action batch input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "economic action batch input length {actual} exceeds {maximum}"
                )
            }
            Self::PostcardDecode => {
                formatter.write_str("economic action batch postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("economic action batch postcard input has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("economic action batch postcard input is not canonical")
            }
            _ => formatter.write_str("economic action batch semantic rejection"),
        }
    }
}
