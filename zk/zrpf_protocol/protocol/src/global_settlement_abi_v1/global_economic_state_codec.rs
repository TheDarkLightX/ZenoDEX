use alloc::vec::Vec;

use super::{
    global_economic_state::GlobalEconomicStateWireV1, GlobalEconomicStateErrorV1,
    GlobalEconomicStateV1, MAX_GLOBAL_ECONOMIC_STATE_BYTES_V1,
};

pub fn encode_global_economic_state_v1(
    state: &GlobalEconomicStateV1,
) -> Result<Vec<u8>, GlobalEconomicStateErrorV1> {
    state.validate_self_consistency()?;
    let bytes =
        postcard::to_allocvec(state).map_err(|_| GlobalEconomicStateErrorV1::PostcardEncode)?;
    if bytes.len() > MAX_GLOBAL_ECONOMIC_STATE_BYTES_V1 {
        return Err(GlobalEconomicStateErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_GLOBAL_ECONOMIC_STATE_BYTES_V1,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_global_economic_state_v1(
    bytes: &[u8],
) -> Result<GlobalEconomicStateV1, GlobalEconomicStateErrorV1> {
    require_bounded_input(bytes, MAX_GLOBAL_ECONOMIC_STATE_BYTES_V1)?;
    let (wire, remainder) = postcard::take_from_bytes::<GlobalEconomicStateWireV1>(bytes)
        .map_err(|_| GlobalEconomicStateErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(GlobalEconomicStateErrorV1::TrailingBytes);
    }
    let state =
        GlobalEconomicStateV1::from_parts(wire.state_version, wire.state_root, wire.content)?;
    if encode_global_economic_state_v1(&state)?.as_slice() != bytes {
        return Err(GlobalEconomicStateErrorV1::NonCanonicalEncoding);
    }
    Ok(state)
}

pub(super) fn require_bounded_input(
    bytes: &[u8],
    maximum: usize,
) -> Result<(), GlobalEconomicStateErrorV1> {
    if bytes.is_empty() {
        return Err(GlobalEconomicStateErrorV1::EmptyInput);
    }
    if bytes.len() > maximum {
        return Err(GlobalEconomicStateErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum,
        });
    }
    Ok(())
}
