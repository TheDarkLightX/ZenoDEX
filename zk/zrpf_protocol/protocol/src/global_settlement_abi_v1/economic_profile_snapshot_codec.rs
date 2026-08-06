use alloc::vec::Vec;

use serde::Deserialize;

use super::{
    EconomicProfileIdV1, EconomicProfileSnapshotContentV1, EconomicProfileSnapshotErrorV1,
    EconomicProfileSnapshotV1, MAX_ECONOMIC_PROFILE_SNAPSHOT_BYTES_V1,
};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct EconomicProfileSnapshotWireV1 {
    profile_version: u16,
    profile_id: EconomicProfileIdV1,
    content: EconomicProfileSnapshotContentV1,
}

pub fn encode_economic_profile_snapshot_v1(
    profile: &EconomicProfileSnapshotV1,
) -> Result<Vec<u8>, EconomicProfileSnapshotErrorV1> {
    let bytes = postcard::to_allocvec(profile)
        .map_err(|_| EconomicProfileSnapshotErrorV1::PostcardEncode)?;
    require_bounded_nonempty(&bytes)?;
    Ok(bytes)
}

pub fn decode_exact_economic_profile_snapshot_v1(
    bytes: &[u8],
) -> Result<EconomicProfileSnapshotV1, EconomicProfileSnapshotErrorV1> {
    require_bounded_nonempty(bytes)?;
    let (wire, remainder): (EconomicProfileSnapshotWireV1, &[u8]) =
        postcard::take_from_bytes(bytes)
            .map_err(|_| EconomicProfileSnapshotErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(EconomicProfileSnapshotErrorV1::TrailingBytes);
    }
    let profile =
        EconomicProfileSnapshotV1::from_parts(wire.profile_version, wire.profile_id, wire.content)?;
    if encode_economic_profile_snapshot_v1(&profile)?.as_slice() != bytes {
        return Err(EconomicProfileSnapshotErrorV1::NonCanonicalEncoding);
    }
    Ok(profile)
}

fn require_bounded_nonempty(bytes: &[u8]) -> Result<(), EconomicProfileSnapshotErrorV1> {
    if bytes.is_empty() {
        return Err(EconomicProfileSnapshotErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_ECONOMIC_PROFILE_SNAPSHOT_BYTES_V1 {
        return Err(EconomicProfileSnapshotErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_ECONOMIC_PROFILE_SNAPSHOT_BYTES_V1,
        });
    }
    Ok(())
}
