use alloc::vec::Vec;

use super::{
    ProposedValueAggregateV5, ValueAggregateErrorV5, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};

pub fn encode_value_aggregate_proposal_v5(
    proposal: &ProposedValueAggregateV5,
) -> Result<Vec<u8>, ValueAggregateErrorV5> {
    proposal.validate_self_consistency()?;
    let bytes =
        postcard::to_allocvec(proposal).map_err(|_| ValueAggregateErrorV5::PostcardDecode)?;
    if bytes.len() > MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 {
        return Err(ValueAggregateErrorV5::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_value_aggregate_proposal_v5(
    bytes: &[u8],
) -> Result<ProposedValueAggregateV5, ValueAggregateErrorV5> {
    if bytes.len() > MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 {
        return Err(ValueAggregateErrorV5::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
        });
    }
    let (proposal, remainder) = postcard::take_from_bytes::<ProposedValueAggregateV5>(bytes)
        .map_err(|_| ValueAggregateErrorV5::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(ValueAggregateErrorV5::TrailingBytes);
    }
    if encode_value_aggregate_proposal_v5(&proposal)?.as_slice() != bytes {
        return Err(ValueAggregateErrorV5::NonCanonicalEncoding);
    }
    Ok(proposal)
}
