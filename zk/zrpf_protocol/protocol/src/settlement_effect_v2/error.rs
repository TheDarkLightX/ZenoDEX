use core::fmt;

use super::super::economic_action_v1::EconomicActionBatchErrorV1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SettlementEffectErrorV2 {
    ActionBatch(EconomicActionBatchErrorV1),
    InvalidVersion(u16),
    NonChangingValue,
    NonChangingState,
    ZeroEffect,
    CombinedMintAndBurn,
    InvalidEffectShape,
    MissingAuthority,
    UnexpectedAuthority,
    EmptyCollection(&'static str),
    CollectionTooLarge {
        field: &'static str,
        actual: usize,
        maximum: usize,
    },
    DuplicateAction,
    DuplicateCellWrite,
    DuplicateAssetEffect,
    DuplicateMessage,
    DuplicateCarry,
    DuplicateReward,
    UnknownAction,
    ActionWithoutCellWrite,
    ActionWithoutAssetEffect,
    AuthorizationMismatch,
    AuthorizationReused,
    AssetConservationViolation,
    ArithmeticOverflow(&'static str),
    MessageCarryMismatch,
    RewardMismatch,
    NonCanonicalOrder(&'static str),
    CommitmentMismatch(&'static str),
    InvalidDerivedCommitment(&'static str),
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl From<EconomicActionBatchErrorV1> for SettlementEffectErrorV2 {
    fn from(error: EconomicActionBatchErrorV1) -> Self {
        Self::ActionBatch(error)
    }
}

impl fmt::Display for SettlementEffectErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ActionBatch(error) => {
                write!(formatter, "economic action batch rejected: {error}")
            }
            Self::InvalidVersion(version) => {
                write!(formatter, "invalid settlement plan version: {version}")
            }
            Self::EmptyCollection(field) => {
                write!(formatter, "settlement collection is empty: {field}")
            }
            Self::CollectionTooLarge {
                field,
                actual,
                maximum,
            } => write!(
                formatter,
                "settlement collection {field} has {actual} rows; maximum is {maximum}"
            ),
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "settlement arithmetic overflow: {field}")
            }
            Self::NonCanonicalOrder(field) => {
                write!(formatter, "settlement rows are not canonical: {field}")
            }
            Self::CommitmentMismatch(field) => {
                write!(formatter, "settlement commitment mismatch: {field}")
            }
            Self::InvalidDerivedCommitment(field) => {
                write!(formatter, "invalid derived settlement commitment: {field}")
            }
            Self::EmptyInput => formatter.write_str("settlement plan input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "settlement plan input length {actual} exceeds {maximum}"
            ),
            _ => formatter.write_str(self.static_message()),
        }
    }
}

impl SettlementEffectErrorV2 {
    fn static_message(&self) -> &'static str {
        match self {
            Self::NonChangingValue => "cell write does not change its value",
            Self::NonChangingState => "settlement pre-state equals post-state",
            Self::ZeroEffect => "settlement effect is all zero",
            Self::CombinedMintAndBurn => "one effect cannot mint and burn",
            Self::InvalidEffectShape => "asset effect has an invalid typed shape",
            Self::MissingAuthority => "authorized effect lacks authority material",
            Self::UnexpectedAuthority => "ordinary effect contains authority material",
            Self::DuplicateAction => "duplicate economic action",
            Self::DuplicateCellWrite => "duplicate ledger cell write",
            Self::DuplicateAssetEffect => "duplicate asset effect",
            Self::DuplicateMessage => "duplicate message effect",
            Self::DuplicateCarry => "duplicate carry effect",
            Self::DuplicateReward => "duplicate reward effect",
            Self::UnknownAction => "settlement row references an unknown action",
            Self::ActionWithoutCellWrite => "economic action lacks a cell write",
            Self::ActionWithoutAssetEffect => "economic action lacks an asset effect",
            Self::AuthorizationMismatch => {
                "authorized effect does not match its action authorization"
            }
            Self::AuthorizationReused => "one action authorization backs multiple effects",
            Self::AssetConservationViolation => "asset effects do not conserve value",
            Self::MessageCarryMismatch => "message and carry effects do not match",
            Self::RewardMismatch => "reward effect does not match its funded effect and write",
            Self::EmptyInput => "settlement plan input is empty",
            Self::PostcardDecode => "settlement plan postcard decode failed",
            Self::TrailingBytes => "settlement plan postcard input has trailing bytes",
            Self::NonCanonicalEncoding => "settlement plan postcard input is not canonical",
            _ => "settlement effect rejected",
        }
    }
}
