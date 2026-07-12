use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueTransferErrorV2 {
    InvalidTransferVersion(u16),
    InvalidSetVersion(u16),
    InvalidKind(u8),
    InvalidRoute,
    ZeroAmount,
    ActionIndexOutOfRange { actual: u32, maximum: u32 },
    DeadlineBeforeEpoch,
    ScopeMismatch,
    EpochMismatch,
    EmptyTransfers,
    TooManyTransfers { actual: usize, maximum: usize },
    DuplicateTransfer,
    DuplicateActionBinding,
    NonCanonicalTransferOrder,
    InvalidDerivedCommitment(&'static str),
    ArithmeticOverflow(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for ValueTransferErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidTransferVersion(version) => {
                write!(formatter, "invalid value-transfer version: {version}")
            }
            Self::InvalidSetVersion(version) => {
                write!(formatter, "invalid value-transfer set version: {version}")
            }
            Self::InvalidKind(kind) => write!(formatter, "invalid value-transfer kind: {kind}"),
            Self::InvalidRoute => {
                formatter.write_str("value-transfer source and destination lanes must differ")
            }
            Self::ZeroAmount => formatter.write_str("value-transfer amount must be nonzero"),
            Self::ActionIndexOutOfRange { actual, maximum } => write!(
                formatter,
                "value-transfer action index {actual} exceeds {maximum}"
            ),
            Self::DeadlineBeforeEpoch => {
                formatter.write_str("value-transfer deadline precedes its source epoch")
            }
            Self::ScopeMismatch => {
                formatter.write_str("value transfers use different application or domain scopes")
            }
            Self::EpochMismatch => formatter.write_str("value transfers use different epochs"),
            Self::EmptyTransfers => formatter.write_str("value-transfer set is empty"),
            Self::TooManyTransfers { actual, maximum } => {
                write!(formatter, "value-transfer count {actual} exceeds {maximum}")
            }
            Self::DuplicateTransfer => formatter.write_str("duplicate value-transfer identity"),
            Self::DuplicateActionBinding => {
                formatter.write_str("duplicate value-transfer action binding")
            }
            Self::NonCanonicalTransferOrder => {
                formatter.write_str("value transfers are not strictly ordered by identity")
            }
            Self::InvalidDerivedCommitment(field) => {
                write!(
                    formatter,
                    "invalid derived value-transfer commitment: {field}"
                )
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::EmptyInput => formatter.write_str("value-transfer input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "value-transfer input length {actual} exceeds {maximum}"
            ),
            Self::PostcardDecode => formatter.write_str("value-transfer postcard decode failed"),
            Self::TrailingBytes => {
                formatter.write_str("value-transfer postcard input has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("value-transfer postcard input is not canonical")
            }
        }
    }
}
