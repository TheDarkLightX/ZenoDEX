use serde::Serialize;
use zenodex_zrpf_protocol_v3::{
    decode_exact_route_release_registry_v1, encode_route_release_registry_v1, EconomicLaneIdV1,
    RouteReleaseRegistryErrorV1, RouteReleaseV1, RouteSelectionKeyV1,
    MAX_ROUTE_RELEASES_PER_REGISTRY_V1, MAX_ROUTE_RELEASE_REGISTRY_BYTES_V1,
    ROUTE_RELEASE_REGISTRY_VERSION_V1,
};

use super::support::{canonical_routes, digest, hex32, registry, route};

#[derive(Serialize)]
struct RegistryWireV1 {
    registry_version: u16,
    routes: Vec<RouteReleaseV1>,
}

#[test]
fn exact_codec_roundtrips_with_fixed_root_and_digest() {
    // Arrange
    let registry = codec_registry();

    // Act
    let encoded = encode_route_release_registry_v1(&registry).unwrap();
    let decoded = decode_exact_route_release_registry_v1(&encoded).unwrap();

    // Assert
    assert_eq!(decoded, registry);
    assert_eq!(
        hex32(digest(&encoded)),
        "1daec76c0cc00c1bd466298e13db61d929f95e69bd5fbc92d4fe75c77c54de79"
    );
}

#[test]
fn exact_codec_rejects_stale_nonminimal_trailing_empty_oversized_and_reordered_input() {
    // Arrange
    let registry = codec_registry();
    let encoded = encode_route_release_registry_v1(&registry).unwrap();
    let mut stale = encoded.clone();
    stale[0] = 2;
    let mut nonminimal = vec![0x81, 0x00];
    nonminimal.extend_from_slice(&encoded[1..]);
    let mut trailing = encoded;
    trailing.push(0);
    let oversized = vec![0; MAX_ROUTE_RELEASE_REGISTRY_BYTES_V1 + 1];
    let reordered = reordered_bytes(&registry);
    let too_many = too_many_route_bytes();

    // Act / Assert
    assert_eq!(
        decode_exact_route_release_registry_v1(&stale),
        Err(RouteReleaseRegistryErrorV1::InvalidRegistryVersion(2))
    );
    assert_eq!(
        decode_exact_route_release_registry_v1(&nonminimal),
        Err(RouteReleaseRegistryErrorV1::NonCanonicalEncoding)
    );
    assert_eq!(
        decode_exact_route_release_registry_v1(&trailing),
        Err(RouteReleaseRegistryErrorV1::TrailingBytes)
    );
    assert_eq!(
        decode_exact_route_release_registry_v1(&[]),
        Err(RouteReleaseRegistryErrorV1::EmptyInput)
    );
    assert_eq!(
        decode_exact_route_release_registry_v1(&oversized),
        Err(RouteReleaseRegistryErrorV1::InputTooLarge {
            actual: MAX_ROUTE_RELEASE_REGISTRY_BYTES_V1 + 1,
            maximum: MAX_ROUTE_RELEASE_REGISTRY_BYTES_V1,
        })
    );
    assert!(matches!(
        decode_exact_route_release_registry_v1(&reordered),
        Err(RouteReleaseRegistryErrorV1::NonCanonicalRouteOrder { .. })
    ));
    assert_eq!(
        decode_exact_route_release_registry_v1(&too_many),
        Err(RouteReleaseRegistryErrorV1::PostcardDecode)
    );
}

#[test]
fn json_decode_rejects_unknown_registry_selection_and_selection_entry_fields() {
    // Arrange
    let mut registry_value = serde_json::to_value(codec_registry()).unwrap();
    registry_value
        .as_object_mut()
        .unwrap()
        .insert("unknown_registry_field".to_owned(), serde_json::json!(1));
    let route = route(1, EconomicLaneIdV1::AssetTransfer, 1);
    let selection = RouteSelectionKeyV1::from_route(&route);
    let mut selection_value = serde_json::to_value(&selection).unwrap();
    selection_value
        .as_object_mut()
        .unwrap()
        .insert("unknown_selection_field".to_owned(), serde_json::json!(1));
    let mut entry_value = serde_json::to_value(&selection).unwrap();
    entry_value["module_releases"][0]
        .as_object_mut()
        .unwrap()
        .insert("unknown_entry_field".to_owned(), serde_json::json!(1));

    // Act
    let registry_result =
        serde_json::from_value::<zenodex_zrpf_protocol_v3::RouteReleaseRegistryV1>(registry_value);
    let selection_result = serde_json::from_value::<RouteSelectionKeyV1>(selection_value);
    let entry_result = serde_json::from_value::<RouteSelectionKeyV1>(entry_value);

    // Assert
    assert!(registry_result.is_err());
    assert!(selection_result.is_err());
    assert!(entry_result.is_err());
}

fn codec_registry() -> zenodex_zrpf_protocol_v3::RouteReleaseRegistryV1 {
    registry(vec![
        route(1, EconomicLaneIdV1::AssetTransfer, 1),
        route(2, EconomicLaneIdV1::SpotLiquidity, 2),
    ])
}

fn reordered_bytes(registry: &zenodex_zrpf_protocol_v3::RouteReleaseRegistryV1) -> Vec<u8> {
    let mut routes = registry.routes().to_vec();
    routes.reverse();
    postcard::to_allocvec(&RegistryWireV1 {
        registry_version: ROUTE_RELEASE_REGISTRY_VERSION_V1,
        routes,
    })
    .unwrap()
}

fn too_many_route_bytes() -> Vec<u8> {
    let routes = canonical_routes(
        (1..=u16::try_from(MAX_ROUTE_RELEASES_PER_REGISTRY_V1 + 1).unwrap())
            .map(|seed| route(seed, EconomicLaneIdV1::SpotLiquidity, 1))
            .collect(),
    );
    postcard::to_allocvec(&RegistryWireV1 {
        registry_version: ROUTE_RELEASE_REGISTRY_VERSION_V1,
        routes,
    })
    .unwrap()
}
