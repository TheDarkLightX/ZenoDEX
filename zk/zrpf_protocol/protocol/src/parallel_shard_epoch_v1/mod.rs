mod codec;
mod epoch;
mod error;
mod hash;
mod shard;

pub use codec::{decode_exact_parallel_shard_epoch_v1, encode_parallel_shard_epoch_v1};
pub use epoch::{ParallelShardEpochInputV1, ParallelShardEpochV1};
pub use error::ParallelShardEpochErrorV1;
pub use hash::{
    canonical_empty_carry_queue_root_v1, canonical_empty_cross_shard_inbox_root_v1,
    canonical_empty_cross_shard_outbox_root_v1,
};
pub use shard::{
    CanonicalShardStateMapV1, DeclaredShardSetV1, ShardCompositionContextV1, ShardIdV1,
    ShardTransitionInputV1, ShardTransitionV1,
};

pub const PARALLEL_SHARD_EPOCH_VERSION_V1: u16 = 1;
pub const PARALLEL_SHARD_COUNT_V1: usize = 2;
pub const MAX_PARALLEL_SHARD_EPOCH_BYTES_V1: usize = 2_048;
