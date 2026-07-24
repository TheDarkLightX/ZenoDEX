use alloc::vec::Vec;

use super::{ParallelShardEpochErrorV1, ParallelShardEpochV1, MAX_PARALLEL_SHARD_EPOCH_BYTES_V1};

pub fn encode_parallel_shard_epoch_v1(
    epoch: &ParallelShardEpochV1,
) -> Result<Vec<u8>, ParallelShardEpochErrorV1> {
    epoch.validate()?;
    let bytes =
        postcard::to_allocvec(epoch).map_err(|_| ParallelShardEpochErrorV1::PostcardDecode)?;
    require_size(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_parallel_shard_epoch_v1(
    bytes: &[u8],
) -> Result<ParallelShardEpochV1, ParallelShardEpochErrorV1> {
    require_size(bytes.len())?;
    let (epoch, remainder) = postcard::take_from_bytes::<ParallelShardEpochV1>(bytes)
        .map_err(|_| ParallelShardEpochErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(ParallelShardEpochErrorV1::TrailingBytes);
    }
    if encode_parallel_shard_epoch_v1(&epoch)?.as_slice() != bytes {
        return Err(ParallelShardEpochErrorV1::NonCanonicalEncoding);
    }
    Ok(epoch)
}

fn require_size(size: usize) -> Result<(), ParallelShardEpochErrorV1> {
    if size == 0 {
        return Err(ParallelShardEpochErrorV1::EmptyInput);
    }
    if size > MAX_PARALLEL_SHARD_EPOCH_BYTES_V1 {
        return Err(ParallelShardEpochErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_PARALLEL_SHARD_EPOCH_BYTES_V1,
        });
    }
    Ok(())
}
