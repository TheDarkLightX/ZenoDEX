use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssetTransferErrorV1 {
    InvalidStateVersion(u16),
    InvalidCommandVersion(u16),
    InvalidLeafInputVersion(u16),
    ZeroIdentifier(&'static str),
    InvalidStoredBalance,
    InvalidAmount,
    SelfTransfer,
    TooManyBalances { actual: usize, maximum: usize },
    DuplicateBalanceKey,
    NonCanonicalBalanceOrder,
    InvalidStateRoot,
    InvalidCommandHash,
    AssetConservationViolation,
    ArithmeticOverflow(&'static str),
    InvalidDerivedCommitment(&'static str),
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    PostcardEncode,
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl fmt::Display for AssetTransferErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidStateVersion(version) => {
                write!(formatter, "invalid asset transfer state version: {version}")
            }
            Self::InvalidCommandVersion(version) => {
                write!(
                    formatter,
                    "invalid asset transfer command version: {version}"
                )
            }
            Self::InvalidLeafInputVersion(version) => {
                write!(
                    formatter,
                    "invalid asset transfer leaf input version: {version}"
                )
            }
            Self::ZeroIdentifier(field) => write!(formatter, "zero identifier: {field}"),
            Self::InvalidStoredBalance => formatter.write_str("stored balance is outside bounds"),
            Self::InvalidAmount => formatter.write_str("transfer amount is outside bounds"),
            Self::SelfTransfer => formatter.write_str("source and destination are identical"),
            Self::TooManyBalances { actual, maximum } => {
                write!(
                    formatter,
                    "asset transfer balance count {actual} exceeds {maximum}"
                )
            }
            Self::DuplicateBalanceKey => {
                formatter.write_str("duplicate asset transfer balance key")
            }
            Self::NonCanonicalBalanceOrder => {
                formatter.write_str("asset transfer balances are not canonically ordered")
            }
            Self::InvalidStateRoot => formatter.write_str("asset transfer state root is invalid"),
            Self::InvalidCommandHash => {
                formatter.write_str("asset transfer command hash is invalid")
            }
            Self::AssetConservationViolation => {
                formatter.write_str("asset transfer conservation check failed")
            }
            Self::ArithmeticOverflow(field) => write!(formatter, "arithmetic overflow: {field}"),
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived commitment: {field}")
            }
            Self::EmptyInput => formatter.write_str("asset transfer leaf input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "asset transfer leaf input length {actual} exceeds {maximum}"
                )
            }
            Self::PostcardEncode => formatter.write_str("asset transfer postcard encode failed"),
            Self::PostcardDecode => formatter.write_str("asset transfer postcard decode failed"),
            Self::TrailingBytes => formatter.write_str("asset transfer input has trailing bytes"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("asset transfer input is not canonically encoded")
            }
        }
    }
}
