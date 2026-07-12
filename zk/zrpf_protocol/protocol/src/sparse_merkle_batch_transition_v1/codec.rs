use alloc::vec::Vec;

use super::bounded::require_entry_count;
use super::{
    SparseMerkleBatchTransitionErrorV1, ValidatedSparseMerkleBatchTransitionV1,
    MAX_SPARSE_MERKLE_BATCH_TRANSITION_BYTES_V1, SPARSE_MERKLE_BATCH_ENTRY_BYTES_V1,
    SPARSE_MERKLE_BATCH_FIXED_BYTES_V1,
};

pub fn expected_sparse_merkle_batch_transition_bytes_v1(
    entry_count: usize,
) -> Result<usize, SparseMerkleBatchTransitionErrorV1> {
    require_entry_count(entry_count)?;
    let entries_bytes = entry_count
        .checked_mul(SPARSE_MERKLE_BATCH_ENTRY_BYTES_V1)
        .ok_or(SparseMerkleBatchTransitionErrorV1::ArithmeticOverflow(
            "entries_bytes",
        ))?;
    SPARSE_MERKLE_BATCH_FIXED_BYTES_V1
        .checked_add(entries_bytes)
        .ok_or(SparseMerkleBatchTransitionErrorV1::ArithmeticOverflow(
            "encoded_bytes",
        ))
}

pub fn encode_sparse_merkle_batch_transition_v1(
    batch: &ValidatedSparseMerkleBatchTransitionV1,
) -> Result<Vec<u8>, SparseMerkleBatchTransitionErrorV1> {
    batch.validate_self_consistency()?;
    let expected = expected_sparse_merkle_batch_transition_bytes_v1(batch.entries().len())?;
    let mut buffer = Vec::new();
    buffer
        .try_reserve_exact(expected)
        .map_err(|_| SparseMerkleBatchTransitionErrorV1::AllocationFailed("encoded_bytes"))?;
    buffer.resize(expected, 0);
    let encoded_length = postcard::to_slice(batch, &mut buffer)
        .map_err(|_| SparseMerkleBatchTransitionErrorV1::PostcardDecode)?
        .len();
    if encoded_length != expected {
        return Err(SparseMerkleBatchTransitionErrorV1::NonCanonicalEncoding);
    }
    Ok(buffer)
}

pub fn decode_exact_sparse_merkle_batch_transition_v1(
    bytes: &[u8],
) -> Result<ValidatedSparseMerkleBatchTransitionV1, SparseMerkleBatchTransitionErrorV1> {
    require_bounded_input(bytes)?;
    let (batch, remainder) =
        postcard::take_from_bytes::<ValidatedSparseMerkleBatchTransitionV1>(bytes)
            .map_err(|_| SparseMerkleBatchTransitionErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(SparseMerkleBatchTransitionErrorV1::TrailingBytes);
    }
    let expected = expected_sparse_merkle_batch_transition_bytes_v1(batch.entries().len())?;
    if bytes.len() != expected || encode_sparse_merkle_batch_transition_v1(&batch)? != bytes {
        return Err(SparseMerkleBatchTransitionErrorV1::NonCanonicalEncoding);
    }
    Ok(batch)
}

fn require_bounded_input(bytes: &[u8]) -> Result<(), SparseMerkleBatchTransitionErrorV1> {
    if bytes.is_empty() {
        return Err(SparseMerkleBatchTransitionErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_SPARSE_MERKLE_BATCH_TRANSITION_BYTES_V1 {
        return Err(SparseMerkleBatchTransitionErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SPARSE_MERKLE_BATCH_TRANSITION_BYTES_V1,
        });
    }
    Ok(())
}
