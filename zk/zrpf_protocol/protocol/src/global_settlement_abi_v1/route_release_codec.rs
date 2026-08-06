use alloc::vec::Vec;

use serde::Deserialize;

use super::{
    RouteReleaseContentV1, RouteReleaseErrorV1, RouteReleaseIdV1, RouteReleaseV1,
    MAX_ROUTE_RELEASE_BYTES_V1,
};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RouteReleaseWireV1 {
    route_release_version: u16,
    route_release_id: RouteReleaseIdV1,
    content: RouteReleaseContentV1,
}

pub fn encode_route_release_v1(
    route_release: &RouteReleaseV1,
) -> Result<Vec<u8>, RouteReleaseErrorV1> {
    let bytes =
        postcard::to_allocvec(route_release).map_err(|_| RouteReleaseErrorV1::PostcardEncode)?;
    require_bounded_nonempty(&bytes)?;
    Ok(bytes)
}

pub fn decode_exact_route_release_v1(bytes: &[u8]) -> Result<RouteReleaseV1, RouteReleaseErrorV1> {
    require_bounded_nonempty(bytes)?;
    let (wire, remainder): (RouteReleaseWireV1, &[u8]) =
        postcard::take_from_bytes(bytes).map_err(|_| RouteReleaseErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(RouteReleaseErrorV1::TrailingBytes);
    }
    let route_release = RouteReleaseV1::from_parts(
        wire.route_release_version,
        wire.route_release_id,
        wire.content,
    )?;
    if encode_route_release_v1(&route_release)?.as_slice() != bytes {
        return Err(RouteReleaseErrorV1::NonCanonicalEncoding);
    }
    Ok(route_release)
}

fn require_bounded_nonempty(bytes: &[u8]) -> Result<(), RouteReleaseErrorV1> {
    if bytes.is_empty() {
        return Err(RouteReleaseErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_ROUTE_RELEASE_BYTES_V1 {
        return Err(RouteReleaseErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_ROUTE_RELEASE_BYTES_V1,
        });
    }
    Ok(())
}
