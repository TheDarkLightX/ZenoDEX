use core::fmt;

use zenodex_zrpf_protocol_v3::ValueTransferErrorV2;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PerpsSourceFinalityReferenceErrorV1 {
    Transfer(ValueTransferErrorV2),
    InvalidContext(&'static str),
    InvalidAction {
        action_index: u32,
        field: &'static str,
    },
    UnsupportedAction {
        action_index: u32,
    },
    NoValueMovingActions,
    MissingTransfer {
        action_index: u32,
    },
    UnexpectedTransfer {
        action_index: u32,
    },
    DuplicateTransferForAction {
        action_index: u32,
    },
    WrongCounterparty {
        action_index: u32,
    },
    TransferMismatch {
        action_index: u32,
        field: &'static str,
    },
    InvalidDerivedCommitment(&'static str),
    RowSetMismatch,
    TooManyRows {
        actual: usize,
        maximum: usize,
    },
    ConservationOverflow,
    ConservationMismatch,
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for PerpsSourceFinalityReferenceErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Transfer(error) => write!(formatter, "value-transfer rejected: {error}"),
            Self::InvalidContext(field) => write!(formatter, "invalid perps context: {field}"),
            Self::InvalidAction {
                action_index,
                field,
            } => {
                write!(formatter, "invalid perps action {action_index}: {field}")
            }
            Self::UnsupportedAction { action_index } => {
                write!(
                    formatter,
                    "perps action {action_index} does not move collateral"
                )
            }
            Self::NoValueMovingActions => formatter.write_str("no value-moving perps actions"),
            Self::MissingTransfer { action_index } => {
                write!(formatter, "perps action {action_index} has no transfer")
            }
            Self::UnexpectedTransfer { action_index } => {
                write!(
                    formatter,
                    "unexpected transfer for perps action {action_index}"
                )
            }
            Self::DuplicateTransferForAction { action_index } => {
                write!(
                    formatter,
                    "duplicate transfer for perps action {action_index}"
                )
            }
            Self::WrongCounterparty { action_index } => {
                write!(
                    formatter,
                    "wrong counterparty for perps action {action_index}"
                )
            }
            Self::TransferMismatch {
                action_index,
                field,
            } => {
                write!(formatter, "perps transfer {action_index} mismatch: {field}")
            }
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived commitment: {field}")
            }
            Self::RowSetMismatch => formatter.write_str("perps collateral row set mismatch"),
            Self::TooManyRows { actual, maximum } => {
                write!(
                    formatter,
                    "perps collateral row count {actual} exceeds {maximum}"
                )
            }
            Self::ConservationOverflow => formatter.write_str("perps collateral total overflow"),
            Self::ConservationMismatch => {
                formatter.write_str("perps collateral rows do not conserve")
            }
            Self::EmptyInput => formatter.write_str("perps collateral proposal is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "perps collateral proposal {actual} exceeds {maximum} bytes"
            ),
            Self::PostcardDecode => {
                formatter.write_str("perps collateral proposal postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("perps collateral proposal has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("perps collateral proposal is not canonical")
            }
        }
    }
}

impl From<ValueTransferErrorV2> for PerpsSourceFinalityReferenceErrorV1 {
    fn from(error: ValueTransferErrorV2) -> Self {
        Self::Transfer(error)
    }
}
