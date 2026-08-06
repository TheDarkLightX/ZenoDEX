use alloc::vec::Vec;

use super::{
    LaneStateTransitionErrorV1, LaneStateTransitionWitnessV1,
    MAX_LANE_STATE_TRANSITION_WITNESS_BYTES_V1,
};

pub fn encode_lane_state_transition_witness_v1(
    witness: &LaneStateTransitionWitnessV1,
) -> Result<Vec<u8>, LaneStateTransitionErrorV1> {
    witness.validate_self_consistency()?;
    let bytes =
        postcard::to_allocvec(witness).map_err(|_| LaneStateTransitionErrorV1::PostcardDecode)?;
    require_bounded(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_lane_state_transition_witness_v1(
    bytes: &[u8],
) -> Result<LaneStateTransitionWitnessV1, LaneStateTransitionErrorV1> {
    require_bounded(bytes.len())?;
    let (witness, remainder) = postcard::take_from_bytes::<LaneStateTransitionWitnessV1>(bytes)
        .map_err(|_| LaneStateTransitionErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(LaneStateTransitionErrorV1::TrailingBytes);
    }
    if encode_lane_state_transition_witness_v1(&witness)?.as_slice() != bytes {
        return Err(LaneStateTransitionErrorV1::NonCanonicalEncoding);
    }
    Ok(witness)
}

fn require_bounded(size: usize) -> Result<(), LaneStateTransitionErrorV1> {
    if size == 0 {
        return Err(LaneStateTransitionErrorV1::EmptyInput);
    }
    if size > MAX_LANE_STATE_TRANSITION_WITNESS_BYTES_V1 {
        return Err(LaneStateTransitionErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_LANE_STATE_TRANSITION_WITNESS_BYTES_V1,
        });
    }
    Ok(())
}
