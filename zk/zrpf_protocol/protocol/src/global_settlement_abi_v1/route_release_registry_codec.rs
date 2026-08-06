use alloc::vec::Vec;

use serde::Deserialize;

use super::route_release_registry_types::deserialize_route_releases;
use super::{
    RouteReleaseRegistryErrorV1, RouteReleaseRegistryV1, RouteReleaseV1,
    MAX_ROUTE_RELEASE_REGISTRY_BYTES_V1,
};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RouteReleaseRegistryWireV1 {
    registry_version: u16,
    #[serde(deserialize_with = "deserialize_route_releases")]
    routes: Vec<RouteReleaseV1>,
}

pub fn encode_route_release_registry_v1(
    registry: &RouteReleaseRegistryV1,
) -> Result<Vec<u8>, RouteReleaseRegistryErrorV1> {
    registry.canonical_root()?;
    let bytes =
        postcard::to_allocvec(registry).map_err(|_| RouteReleaseRegistryErrorV1::PostcardEncode)?;
    require_bounded_nonempty(&bytes)?;
    Ok(bytes)
}

pub fn decode_exact_route_release_registry_v1(
    bytes: &[u8],
) -> Result<RouteReleaseRegistryV1, RouteReleaseRegistryErrorV1> {
    require_bounded_nonempty(bytes)?;
    let (wire, remainder): (RouteReleaseRegistryWireV1, &[u8]) =
        postcard::take_from_bytes(bytes)
            .map_err(|_| RouteReleaseRegistryErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(RouteReleaseRegistryErrorV1::TrailingBytes);
    }
    let registry = RouteReleaseRegistryV1::from_parts(wire.registry_version, wire.routes)?;
    if encode_route_release_registry_v1(&registry)?.as_slice() != bytes {
        return Err(RouteReleaseRegistryErrorV1::NonCanonicalEncoding);
    }
    Ok(registry)
}

fn require_bounded_nonempty(bytes: &[u8]) -> Result<(), RouteReleaseRegistryErrorV1> {
    if bytes.is_empty() {
        return Err(RouteReleaseRegistryErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_ROUTE_RELEASE_REGISTRY_BYTES_V1 {
        return Err(RouteReleaseRegistryErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_ROUTE_RELEASE_REGISTRY_BYTES_V1,
        });
    }
    Ok(())
}
