use alloc::vec::Vec;

use serde::Deserialize;

use super::{
    LaneModuleReleaseContentV1, LaneModuleReleaseErrorV1, LaneModuleReleaseIdV1,
    LaneModuleReleaseStatusV1, LaneModuleReleaseV1, MAX_LANE_MODULE_RELEASE_BYTES_V1,
};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LaneModuleReleaseWireV1 {
    release_version: u16,
    release_id: LaneModuleReleaseIdV1,
    content: LaneModuleReleaseContentV1,
    status: LaneModuleReleaseStatusV1,
}

pub fn encode_lane_module_release_v1(
    release: &LaneModuleReleaseV1,
) -> Result<Vec<u8>, LaneModuleReleaseErrorV1> {
    release.canonical_record_commitment()?;
    let bytes =
        postcard::to_allocvec(release).map_err(|_| LaneModuleReleaseErrorV1::PostcardEncode)?;
    require_bounded_nonempty(&bytes)?;
    Ok(bytes)
}

pub fn decode_exact_lane_module_release_v1(
    bytes: &[u8],
) -> Result<LaneModuleReleaseV1, LaneModuleReleaseErrorV1> {
    require_bounded_nonempty(bytes)?;
    let (wire, remainder): (LaneModuleReleaseWireV1, &[u8]) =
        postcard::take_from_bytes(bytes).map_err(|_| LaneModuleReleaseErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(LaneModuleReleaseErrorV1::TrailingBytes);
    }
    let release = LaneModuleReleaseV1::from_parts(
        wire.release_version,
        wire.release_id,
        wire.content,
        wire.status,
    )?;
    if encode_lane_module_release_v1(&release)?.as_slice() != bytes {
        return Err(LaneModuleReleaseErrorV1::NonCanonicalEncoding);
    }
    Ok(release)
}

fn require_bounded_nonempty(bytes: &[u8]) -> Result<(), LaneModuleReleaseErrorV1> {
    if bytes.is_empty() {
        return Err(LaneModuleReleaseErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_LANE_MODULE_RELEASE_BYTES_V1 {
        return Err(LaneModuleReleaseErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_LANE_MODULE_RELEASE_BYTES_V1,
        });
    }
    Ok(())
}
