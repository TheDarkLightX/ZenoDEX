use zenodex_zrpf_protocol_v3::{
    EconomicLaneIdV1, RouteDependencyRoleV1, RouteReleaseRegistryErrorV1,
};

use super::support::{custom_route, dependency, module_registry, registry, roles, root};

#[test]
fn module_registry_binding_is_exact_in_count_lane_order_and_release_identity() {
    // Arrange
    let registry = registry(vec![custom_route(
        root(1),
        vec![
            dependency(
                EconomicLaneIdV1::SpotLiquidity,
                2,
                roles(&[RouteDependencyRoleV1::State]),
            ),
            dependency(
                EconomicLaneIdV1::AssetTransfer,
                1,
                roles(&[RouteDependencyRoleV1::Primary]),
            ),
        ],
        root(50),
    )]);
    let asset = module_registry(EconomicLaneIdV1::AssetTransfer, 1);
    let spot = module_registry(EconomicLaneIdV1::SpotLiquidity, 2);
    let farm = module_registry(EconomicLaneIdV1::FarmIncentives, 3);
    let wrong_spot_release = module_registry(EconomicLaneIdV1::SpotLiquidity, 4);
    let before = registry.clone();

    // Act
    let exact = registry.bind_module_release_registries(&[asset.clone(), spot.clone()]);
    let missing = registry.bind_module_release_registries(core::slice::from_ref(&asset));
    let extra = registry.bind_module_release_registries(&[asset.clone(), spot.clone(), farm]);
    let reordered = registry.bind_module_release_registries(&[spot.clone(), asset.clone()]);
    let duplicate = registry.bind_module_release_registries(&[asset.clone(), asset.clone()]);
    let unknown = registry.bind_module_release_registries(&[asset, wrong_spot_release]);

    // Assert
    assert_eq!(exact, Ok(()));
    assert_eq!(
        missing,
        Err(RouteReleaseRegistryErrorV1::ModuleRegistryCountMismatch {
            actual: 1,
            expected: 2,
        })
    );
    assert_eq!(
        extra,
        Err(RouteReleaseRegistryErrorV1::ModuleRegistryCountMismatch {
            actual: 3,
            expected: 2,
        })
    );
    assert!(matches!(
        reordered,
        Err(RouteReleaseRegistryErrorV1::ModuleRegistryLaneMismatch { position: 0, .. })
    ));
    assert!(matches!(
        duplicate,
        Err(RouteReleaseRegistryErrorV1::ModuleRegistryLaneMismatch { position: 1, .. })
    ));
    assert!(matches!(
        unknown,
        Err(RouteReleaseRegistryErrorV1::UnknownDependencyRelease { .. })
    ));
    assert_eq!(registry, before);
}
