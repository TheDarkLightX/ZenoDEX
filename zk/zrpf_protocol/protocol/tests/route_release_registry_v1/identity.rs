use zenodex_zrpf_protocol_v3::{
    EconomicLaneIdV1, RouteDependencyRoleV1, RouteReleaseRegistryErrorV1, RouteReleaseRegistryV1,
    RouteSelectionKeyV1,
};

use super::support::{canonical_routes, custom_route, dependency, hex32, roles, root, route};

#[test]
fn duplicate_route_identity_and_ambiguous_selection_key_are_rejected() {
    // Arrange
    let first = route(1, EconomicLaneIdV1::SpotLiquidity, 1);
    let ambiguous = custom_route(
        first.content().command_variant_root(),
        vec![dependency(
            EconomicLaneIdV1::SpotLiquidity,
            1,
            roles(&[RouteDependencyRoleV1::Primary, RouteDependencyRoleV1::State]),
        )],
        root(99),
    );
    assert_ne!(first.route_release_id(), ambiguous.route_release_id());
    assert_eq!(
        RouteSelectionKeyV1::from_route(&first),
        RouteSelectionKeyV1::from_route(&ambiguous)
    );

    // Act
    let duplicate = RouteReleaseRegistryV1::new(vec![first.clone(), first.clone()]);
    let ambiguous_result = RouteReleaseRegistryV1::new(canonical_routes(vec![first, ambiguous]));

    // Assert
    assert!(matches!(
        duplicate,
        Err(RouteReleaseRegistryErrorV1::DuplicateRouteReleaseId(_))
    ));
    assert_eq!(
        ambiguous_result,
        Err(RouteReleaseRegistryErrorV1::AmbiguousRouteSelection)
    );
}

#[test]
fn canonical_root_binds_route_identity_and_has_a_fixed_vector() {
    // Arrange
    let baseline = RouteReleaseRegistryV1::new(canonical_routes(vec![
        route(1, EconomicLaneIdV1::AssetTransfer, 1),
        route(2, EconomicLaneIdV1::SpotLiquidity, 2),
    ]))
    .unwrap();
    let changed = RouteReleaseRegistryV1::new(canonical_routes(vec![
        route(1, EconomicLaneIdV1::AssetTransfer, 1),
        route(2, EconomicLaneIdV1::SpotLiquidity, 3),
    ]))
    .unwrap();

    // Act
    let baseline_root = baseline.canonical_root().unwrap();
    let changed_root = changed.canonical_root().unwrap();

    // Assert
    assert_ne!(baseline_root, changed_root);
    assert_eq!(
        hex32(baseline_root.into_bytes()),
        "e5747633f19f5c1806dc51106119e6fc8a67a7337dccfd92be24f74ab132c190"
    );
}
