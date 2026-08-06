use zenodex_zrpf_protocol_v3::{
    decode_exact_route_release_v1, encode_route_release_v1, EconomicLaneIdV1,
    RouteDependencyRoleV1, RouteReleaseErrorV1, RouteReleaseV1, MAX_ROUTE_RELEASE_BYTES_V1,
};

use super::support::{dependency, digest, hex32, roles, route};

#[test]
fn exact_codec_roundtrips_with_fixed_identity_and_digest() {
    // Arrange
    let route = route(vec![
        dependency(
            EconomicLaneIdV1::SpotLiquidity,
            1,
            roles(&[RouteDependencyRoleV1::Primary]),
        ),
        dependency(
            EconomicLaneIdV1::FarmIncentives,
            2,
            roles(&[RouteDependencyRoleV1::State]),
        ),
    ]);

    // Act
    let encoded = encode_route_release_v1(&route).unwrap();
    let decoded = decode_exact_route_release_v1(&encoded).unwrap();

    // Assert
    assert_eq!(decoded, route);
    assert_eq!(
        hex32(route.route_release_id().into_bytes()),
        "dccc2a3e86d4920bdc366580b3ba7aaf7011b8c444f52c07ced732b37195c5fe"
    );
    assert_eq!(
        hex32(digest(&encoded)),
        "a0656a8be962f49289a168a751ac7982933bbe339581476009c9942cb57b225c"
    );
}

#[test]
fn exact_codec_rejects_stale_counterfeit_and_unknown_variants() {
    // Arrange
    let route = route(vec![dependency(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        roles(&[RouteDependencyRoleV1::Primary]),
    )]);
    let encoded = encode_route_release_v1(&route).unwrap();
    let mut stale = encoded.clone();
    stale[0] = 2;
    let mut counterfeit = encoded.clone();
    counterfeit[1] ^= 1;
    let mut too_many_dependencies = encoded.clone();
    assert_eq!(too_many_dependencies[65], 1);
    too_many_dependencies[65] = 9;
    let mut unknown_role = encoded.clone();
    assert_eq!(unknown_role[99], RouteDependencyRoleV1::Primary.bit());
    unknown_role[99] = 0x80;
    let mut unknown_oracle_policy = encoded.clone();
    assert_eq!(unknown_oracle_policy[228], 0);
    unknown_oracle_policy[228] = 2;
    let mut unknown_issue_burn_policy = encoded.clone();
    assert_eq!(unknown_issue_burn_policy[229], 0);
    unknown_issue_burn_policy[229] = 4;
    // Act / Assert
    assert_eq!(
        decode_exact_route_release_v1(&stale),
        Err(RouteReleaseErrorV1::InvalidRouteReleaseVersion(2))
    );
    assert_eq!(
        decode_exact_route_release_v1(&counterfeit),
        Err(RouteReleaseErrorV1::CounterfeitRouteReleaseId)
    );
    assert_eq!(
        decode_exact_route_release_v1(&unknown_role),
        Err(RouteReleaseErrorV1::PostcardDecode)
    );
    assert_eq!(
        decode_exact_route_release_v1(&too_many_dependencies),
        Err(RouteReleaseErrorV1::PostcardDecode)
    );
    assert_eq!(
        decode_exact_route_release_v1(&unknown_oracle_policy),
        Err(RouteReleaseErrorV1::PostcardDecode)
    );
    assert_eq!(
        decode_exact_route_release_v1(&unknown_issue_burn_policy),
        Err(RouteReleaseErrorV1::PostcardDecode)
    );
}

#[test]
fn exact_codec_rejects_trailing_empty_and_oversized_inputs() {
    // Arrange
    let route = route(vec![dependency(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        roles(&[RouteDependencyRoleV1::Primary]),
    )]);
    let encoded = encode_route_release_v1(&route).unwrap();
    let mut noncanonical = vec![0x81, 0x00];
    noncanonical.extend_from_slice(&encoded[1..]);
    let mut trailing = encoded;
    trailing.push(0);
    let oversized = vec![0; MAX_ROUTE_RELEASE_BYTES_V1 + 1];

    // Act / Assert
    assert_eq!(
        decode_exact_route_release_v1(&noncanonical),
        Err(RouteReleaseErrorV1::NonCanonicalEncoding)
    );
    assert_eq!(
        decode_exact_route_release_v1(&trailing),
        Err(RouteReleaseErrorV1::TrailingBytes)
    );
    assert_eq!(
        decode_exact_route_release_v1(&[]),
        Err(RouteReleaseErrorV1::EmptyInput)
    );
    assert_eq!(
        decode_exact_route_release_v1(&oversized),
        Err(RouteReleaseErrorV1::InputTooLarge {
            actual: MAX_ROUTE_RELEASE_BYTES_V1 + 1,
            maximum: MAX_ROUTE_RELEASE_BYTES_V1,
        })
    );
}

#[test]
fn json_decode_rejects_unknown_struct_fields() {
    // Arrange
    let route = route(vec![dependency(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        roles(&[RouteDependencyRoleV1::Primary]),
    )]);
    let canonical = serde_json::to_value(route).unwrap();

    // Act / Assert
    for pointer in [
        "",
        "/content",
        "/content/dependencies/0",
        "/content/resource_limits",
    ] {
        let mut mutated = canonical.clone();
        mutated
            .pointer_mut(pointer)
            .unwrap()
            .as_object_mut()
            .unwrap()
            .insert("unknown_route_field".to_owned(), serde_json::json!(1));
        assert!(
            serde_json::from_value::<RouteReleaseV1>(mutated).is_err(),
            "unknown field accepted at {pointer}"
        );
    }
}
