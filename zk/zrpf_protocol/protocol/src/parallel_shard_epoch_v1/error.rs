use core::fmt;

use crate::ZrpfErrorV3;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParallelShardEpochErrorV1 {
    Structural(ZrpfErrorV3),
    InvalidVersion(u16),
    ShardIdsNotStrictlySorted,
    GovernedShardMismatch,
    ScopeMismatch { shard_index: usize },
    SemanticProfileMismatch { shard_index: usize },
    StateRootSchemeMismatch { shard_index: usize },
    NonEmptyCrossShardOutbox { shard_index: usize },
    NonEmptyCrossShardInbox { shard_index: usize },
    NonEmptyCarryQueuePre { shard_index: usize },
    NonEmptyCarryQueuePost { shard_index: usize },
    DerivedRootMismatch(&'static str),
    SemanticEpochRootMismatch,
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    ArithmeticOverflow(&'static str),
    PostcardDecode,
    TrailingBytes,
    NonCanonicalEncoding,
}

impl From<ZrpfErrorV3> for ParallelShardEpochErrorV1 {
    fn from(error: ZrpfErrorV3) -> Self {
        Self::Structural(error)
    }
}

impl fmt::Display for ParallelShardEpochErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Structural(error) => write!(formatter, "structural value rejected: {error}"),
            Self::InvalidVersion(version) => {
                write!(formatter, "invalid parallel shard epoch version: {version}")
            }
            Self::ShardIdsNotStrictlySorted => {
                formatter.write_str("shard IDs are not strictly increasing")
            }
            Self::GovernedShardMismatch => {
                formatter.write_str("state-map shard IDs differ from the governed shard set")
            }
            Self::ScopeMismatch { shard_index } => {
                write!(
                    formatter,
                    "shard {shard_index} has a different execution scope"
                )
            }
            Self::SemanticProfileMismatch { shard_index } => write!(
                formatter,
                "shard {shard_index} has a different semantic profile"
            ),
            Self::StateRootSchemeMismatch { shard_index } => write!(
                formatter,
                "shard {shard_index} has a different state-root scheme"
            ),
            Self::NonEmptyCrossShardOutbox { shard_index } => write!(
                formatter,
                "shard {shard_index} cross-shard outbox is not canonically empty"
            ),
            Self::NonEmptyCrossShardInbox { shard_index } => write!(
                formatter,
                "shard {shard_index} cross-shard inbox is not canonically empty"
            ),
            Self::NonEmptyCarryQueuePre { shard_index } => write!(
                formatter,
                "shard {shard_index} pre-carry queue is not canonically empty"
            ),
            Self::NonEmptyCarryQueuePost { shard_index } => write!(
                formatter,
                "shard {shard_index} post-carry queue is not canonically empty"
            ),
            Self::DerivedRootMismatch(field) => {
                write!(formatter, "parallel shard derived root mismatch: {field}")
            }
            Self::SemanticEpochRootMismatch => {
                formatter.write_str("parallel shard semantic epoch root mismatch")
            }
            Self::EmptyInput => formatter.write_str("parallel shard epoch input is empty"),
            Self::InputTooLarge { actual, maximum } => write!(
                formatter,
                "parallel shard epoch input length {actual} exceeds {maximum}"
            ),
            Self::ArithmeticOverflow(field) => {
                write!(formatter, "parallel shard arithmetic overflow: {field}")
            }
            Self::PostcardDecode => {
                formatter.write_str("parallel shard epoch postcard decode failed")
            }
            Self::TrailingBytes => {
                formatter.write_str("parallel shard epoch input has trailing bytes")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("parallel shard epoch input is noncanonical")
            }
        }
    }
}
