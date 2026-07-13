use alloc::vec::Vec;

use crate::{ProposedZusdValueFlowV1, ZusdValueFlowErrorV1};

pub const MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1: usize = 1_048_576;

pub fn encode_proposed_zusd_value_flow_v1(
    proposal: &ProposedZusdValueFlowV1,
) -> Result<Vec<u8>, ZusdValueFlowErrorV1> {
    proposal.validate_self_consistency()?;
    let bytes =
        postcard::to_allocvec(proposal).map_err(|_| ZusdValueFlowErrorV1::PostcardDecode)?;
    require_size(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_proposed_zusd_value_flow_v1(
    bytes: &[u8],
) -> Result<ProposedZusdValueFlowV1, ZusdValueFlowErrorV1> {
    require_size(bytes.len())?;
    let (proposal, remainder) = postcard::take_from_bytes::<ProposedZusdValueFlowV1>(bytes)
        .map_err(|_| ZusdValueFlowErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(ZusdValueFlowErrorV1::TrailingBytes);
    }
    if postcard::to_allocvec(&proposal)
        .map_err(|_| ZusdValueFlowErrorV1::PostcardDecode)?
        .as_slice()
        != bytes
    {
        return Err(ZusdValueFlowErrorV1::NonCanonicalEncoding);
    }
    Ok(proposal)
}

fn require_size(size: usize) -> Result<(), ZusdValueFlowErrorV1> {
    if size == 0 {
        return Err(ZusdValueFlowErrorV1::EmptyInput);
    }
    if size > MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1 {
        return Err(ZusdValueFlowErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_PROPOSED_ZUSD_VALUE_FLOW_BYTES_V1,
        });
    }
    Ok(())
}
