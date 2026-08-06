use zenodex_zrpf_protocol_v3::{
    EconomicLaneIdV1, LaneModuleReleaseRegistryV1, RouteDependencyRoleV1, RouteReleaseErrorV1,
};

use super::support::{dependency, module_registry, roles, route};

#[test]
fn module_release_registry_binding_is_exact_in_count_order_and_release_identity() {
    // Arrange
    let primary = dependency(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        roles(&[RouteDependencyRoleV1::Primary]),
    );
    let state = dependency(
        EconomicLaneIdV1::FarmIncentives,
        2,
        roles(&[RouteDependencyRoleV1::State]),
    );
    let route = route(vec![primary.clone(), state.clone()]);
    let primary_registry = module_registry(&primary, 1);
    let state_registry = module_registry(&state, 2);
    let wrong_release = LaneModuleReleaseRegistryV1::new(
        EconomicLaneIdV1::FarmIncentives,
        vec![super::support::module_release(
            EconomicLaneIdV1::FarmIncentives,
            3,
        )],
    )
    .unwrap();

    // Act
    let correct =
        route.bind_module_release_registries(&[primary_registry.clone(), state_registry.clone()]);
    let missing = route.bind_module_release_registries(core::slice::from_ref(&primary_registry));
    let extra = route.bind_module_release_registries(&[
        primary_registry.clone(),
        state_registry.clone(),
        primary_registry.clone(),
    ]);
    let reordered =
        route.bind_module_release_registries(&[state_registry.clone(), primary_registry.clone()]);
    let unknown = route.bind_module_release_registries(&[primary_registry.clone(), wrong_release]);

    // Assert
    assert_eq!(correct, Ok(()));
    assert_eq!(
        missing,
        Err(RouteReleaseErrorV1::DependencyRegistryCountMismatch {
            actual: 1,
            expected: 2,
        })
    );
    assert_eq!(
        extra,
        Err(RouteReleaseErrorV1::DependencyRegistryCountMismatch {
            actual: 3,
            expected: 2,
        })
    );
    assert!(matches!(
        reordered,
        Err(RouteReleaseErrorV1::DependencyRegistryLaneMismatch { position: 0, .. })
    ));
    assert!(matches!(
        unknown,
        Err(RouteReleaseErrorV1::UnknownDependencyRelease { position: 1, .. })
    ));
}
