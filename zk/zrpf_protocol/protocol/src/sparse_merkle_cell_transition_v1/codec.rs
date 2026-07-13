use alloc::vec::Vec;

use super::{
    SparseMerkleCellTransitionErrorV1, SparseMerkleCellTransitionWitnessV1,
    MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1,
    SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1,
};

pub fn encode_sparse_merkle_cell_transition_witness_v1(
    witness: &SparseMerkleCellTransitionWitnessV1,
) -> Result<Vec<u8>, SparseMerkleCellTransitionErrorV1> {
    witness.validate_self_consistency()?;
    let mut buffer = [0_u8; MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1];
    let encoded_length = postcard::to_slice(witness, &mut buffer)
        .map_err(|_| SparseMerkleCellTransitionErrorV1::PostcardDecode)?
        .len();
    if encoded_length != SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1 {
        return Err(SparseMerkleCellTransitionErrorV1::NonCanonicalEncoding);
    }
    let bytes = buffer[..encoded_length].to_vec();
    require_bounded_input(&bytes)?;
    Ok(bytes)
}

pub fn decode_exact_sparse_merkle_cell_transition_witness_v1(
    bytes: &[u8],
) -> Result<SparseMerkleCellTransitionWitnessV1, SparseMerkleCellTransitionErrorV1> {
    require_bounded_input(bytes)?;
    let (witness, remainder) =
        postcard::take_from_bytes::<SparseMerkleCellTransitionWitnessV1>(bytes)
            .map_err(|_| SparseMerkleCellTransitionErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(SparseMerkleCellTransitionErrorV1::TrailingBytes);
    }
    if encode_sparse_merkle_cell_transition_witness_v1(&witness)?.as_slice() != bytes {
        return Err(SparseMerkleCellTransitionErrorV1::NonCanonicalEncoding);
    }
    Ok(witness)
}

fn require_bounded_input(bytes: &[u8]) -> Result<(), SparseMerkleCellTransitionErrorV1> {
    if bytes.is_empty() {
        return Err(SparseMerkleCellTransitionErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1 {
        return Err(SparseMerkleCellTransitionErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1,
        });
    }
    Ok(())
}
