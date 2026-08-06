use alloc::vec::Vec;

use super::{
    economic_object_release_pin::{
        EconomicObjectReleasePinProofWireV1, EconomicObjectReleasePinV1,
    },
    global_economic_state_codec::require_bounded_input,
    EconomicObjectReleasePinProofV1, GlobalEconomicStateErrorV1,
    MAX_ECONOMIC_OBJECT_RELEASE_PIN_PROOF_BYTES_V1,
};

pub fn encode_economic_object_release_pin_proof_v1(
    proof: &EconomicObjectReleasePinProofV1,
) -> Result<Vec<u8>, GlobalEconomicStateErrorV1> {
    let bytes =
        postcard::to_allocvec(proof).map_err(|_| GlobalEconomicStateErrorV1::PostcardEncode)?;
    if bytes.len() > MAX_ECONOMIC_OBJECT_RELEASE_PIN_PROOF_BYTES_V1 {
        return Err(GlobalEconomicStateErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_ECONOMIC_OBJECT_RELEASE_PIN_PROOF_BYTES_V1,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_economic_object_release_pin_proof_v1(
    bytes: &[u8],
) -> Result<EconomicObjectReleasePinProofV1, GlobalEconomicStateErrorV1> {
    require_bounded_input(bytes, MAX_ECONOMIC_OBJECT_RELEASE_PIN_PROOF_BYTES_V1)?;
    let (wire, remainder) = postcard::take_from_bytes::<EconomicObjectReleasePinProofWireV1>(bytes)
        .map_err(|_| GlobalEconomicStateErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(GlobalEconomicStateErrorV1::TrailingBytes);
    }
    let pin = EconomicObjectReleasePinV1::from_parts(
        wire.pin.pin_version,
        wire.pin.object_id,
        wire.pin.lane_id,
        wire.pin.creating_release_id,
    )?;
    let proof = EconomicObjectReleasePinProofV1::new(pin, wire.sibling_commitments)?;
    if encode_economic_object_release_pin_proof_v1(&proof)?.as_slice() != bytes {
        return Err(GlobalEconomicStateErrorV1::NonCanonicalEncoding);
    }
    Ok(proof)
}
