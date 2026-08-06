use zenodex_zrpf_protocol_v3::{
    EconomicLaneIdV1, EconomicProfileRegistryRootsV1, EconomicProfileSnapshotErrorV1,
    EconomicProfileTransitionModeV1, LaneModuleReleaseErrorV1, LaneModuleReleaseRegistryV1,
    LaneModuleReleaseStatusV1, RouteDependencyLifecyclePurposeV1, RouteReleaseRegistryV1,
};

use super::support::{economic_fixture, module_release, profile, root, route_with_purpose};

#[test]
fn exact_economic_registry_binding_accepts_and_rejects_without_mutation() {
    // Arrange
    let fixture = economic_fixture(
        &[EconomicLaneIdV1::SpotLiquidity],
        EconomicLaneIdV1::SpotLiquidity,
        LaneModuleReleaseStatusV1::ActiveNew,
    );
    let before = fixture.profile.clone();

    // Act
    let result = fixture.profile.bind_economic_registries(
        &fixture.lane_registry,
        &fixture.module_registries,
        &fixture.route_registry,
    );

    // Assert
    assert_eq!(result, Ok(()));
    assert_eq!(fixture.profile, before);
}

#[test]
fn profile_lane_and_route_roots_must_match_exactly() {
    // Arrange
    let fixture = economic_fixture(
        &[EconomicLaneIdV1::SpotLiquidity],
        EconomicLaneIdV1::SpotLiquidity,
        LaneModuleReleaseStatusV1::ActiveNew,
    );
    let roots = fixture.profile.content().registry_roots();
    let wrong_lane_root = EconomicProfileRegistryRootsV1::new(
        root(900),
        roots.route_release_registry_root(),
        roots.proof_shape_registry_root(),
        roots.verifier_registry_root(),
        roots.migration_registry_root(),
        roots.policy_registry_root(),
        roots.terminal_registry_root(),
    );
    let wrong_route_root = EconomicProfileRegistryRootsV1::new(
        roots.economic_lane_registry_root(),
        root(901),
        roots.proof_shape_registry_root(),
        roots.verifier_registry_root(),
        roots.migration_registry_root(),
        roots.policy_registry_root(),
        roots.terminal_registry_root(),
    );

    // Act
    let lane_result = profile(
        0,
        0,
        fixture.profile.content().transition_mode(),
        None,
        wrong_lane_root,
    )
    .bind_economic_registries(
        &fixture.lane_registry,
        &fixture.module_registries,
        &fixture.route_registry,
    );
    let route_result = profile(
        0,
        0,
        fixture.profile.content().transition_mode(),
        None,
        wrong_route_root,
    )
    .bind_economic_registries(
        &fixture.lane_registry,
        &fixture.module_registries,
        &fixture.route_registry,
    );

    // Assert
    assert_eq!(
        lane_result,
        Err(EconomicProfileSnapshotErrorV1::EconomicLaneRegistryRootMismatch)
    );
    assert_eq!(
        route_result,
        Err(EconomicProfileSnapshotErrorV1::RouteReleaseRegistryRootMismatch)
    );
}

#[test]
fn module_registry_binding_is_exact_at_eleven_twelve_thirteen_order_and_root() {
    // Arrange
    let fixture = economic_fixture(
        &[EconomicLaneIdV1::SpotLiquidity],
        EconomicLaneIdV1::SpotLiquidity,
        LaneModuleReleaseStatusV1::ActiveNew,
    );
    let missing = &fixture.module_registries[..11];
    let mut extra = fixture.module_registries.clone();
    extra.push(fixture.module_registries[0].clone());
    let mut reversed = fixture.module_registries.clone();
    reversed.reverse();
    let mut wrong_root = fixture.module_registries.clone();
    wrong_root[0] = LaneModuleReleaseRegistryV1::new(
        EconomicLaneIdV1::AssetTransfer,
        vec![super::support::module_release(
            EconomicLaneIdV1::AssetTransfer,
            999,
            LaneModuleReleaseStatusV1::Candidate,
        )],
    )
    .unwrap();

    // Act
    let missing_result = fixture.profile.bind_economic_registries(
        &fixture.lane_registry,
        missing,
        &fixture.route_registry,
    );
    let extra_result = fixture.profile.bind_economic_registries(
        &fixture.lane_registry,
        &extra,
        &fixture.route_registry,
    );
    let reversed_result = fixture.profile.bind_economic_registries(
        &fixture.lane_registry,
        &reversed,
        &fixture.route_registry,
    );
    let wrong_root_result = fixture.profile.bind_economic_registries(
        &fixture.lane_registry,
        &wrong_root,
        &fixture.route_registry,
    );

    // Assert
    assert_eq!(
        missing_result,
        Err(EconomicProfileSnapshotErrorV1::WrongModuleRegistryCount {
            actual: 11,
            expected: 12,
        })
    );
    assert_eq!(
        extra_result,
        Err(EconomicProfileSnapshotErrorV1::WrongModuleRegistryCount {
            actual: 13,
            expected: 12,
        })
    );
    assert!(matches!(
        reversed_result,
        Err(EconomicProfileSnapshotErrorV1::ModuleRegistryLaneMismatch { position: 0, .. })
    ));
    assert!(matches!(
        wrong_root_result,
        Err(EconomicProfileSnapshotErrorV1::ModuleRegistryBinding { .. })
    ));
}

#[test]
fn enabled_and_disabled_lanes_have_exact_primary_route_coverage() {
    // Arrange
    let disabled_route = economic_fixture(
        &[],
        EconomicLaneIdV1::SpotLiquidity,
        LaneModuleReleaseStatusV1::ActiveNew,
    );
    let missing_enabled = economic_fixture(
        &[
            EconomicLaneIdV1::AssetTransfer,
            EconomicLaneIdV1::SpotLiquidity,
        ],
        EconomicLaneIdV1::AssetTransfer,
        LaneModuleReleaseStatusV1::ActiveNew,
    );

    // Act
    let disabled_result = disabled_route.profile.bind_economic_registries(
        &disabled_route.lane_registry,
        &disabled_route.module_registries,
        &disabled_route.route_registry,
    );
    let missing_result = missing_enabled.profile.bind_economic_registries(
        &missing_enabled.lane_registry,
        &missing_enabled.module_registries,
        &missing_enabled.route_registry,
    );

    // Assert
    assert_eq!(
        disabled_result,
        Err(EconomicProfileSnapshotErrorV1::DisabledLaneHasPrimaryRoute(
            EconomicLaneIdV1::SpotLiquidity
        ))
    );
    assert_eq!(
        missing_result,
        Err(
            EconomicProfileSnapshotErrorV1::EnabledLaneHasNoPrimaryRoute(
                EconomicLaneIdV1::SpotLiquidity
            )
        )
    );
}

#[test]
fn executable_route_dependencies_admit_only_active_new_and_drain_only_releases() {
    // Arrange / Act / Assert
    for status in [
        LaneModuleReleaseStatusV1::Candidate,
        LaneModuleReleaseStatusV1::Shadow,
        LaneModuleReleaseStatusV1::ActiveNew,
        LaneModuleReleaseStatusV1::DrainOnly,
        LaneModuleReleaseStatusV1::VerifyOnly,
        LaneModuleReleaseStatusV1::Retired,
        LaneModuleReleaseStatusV1::Revoked,
    ] {
        let fixture = economic_fixture(
            &[EconomicLaneIdV1::SpotLiquidity],
            EconomicLaneIdV1::SpotLiquidity,
            status,
        );
        let result = fixture.profile.bind_economic_registries(
            &fixture.lane_registry,
            &fixture.module_registries,
            &fixture.route_registry,
        );
        if matches!(
            status,
            LaneModuleReleaseStatusV1::ActiveNew | LaneModuleReleaseStatusV1::DrainOnly
        ) {
            assert_eq!(result, Ok(()));
        } else {
            assert!(matches!(
                result,
                Err(EconomicProfileSnapshotErrorV1::DependencyReleaseAdmission {
                    source: LaneModuleReleaseErrorV1::StatusDisallowsExistingObject(actual),
                    ..
                }) if actual == status
            ));
        }
    }
}

#[test]
fn active_new_lifecycle_purpose_rejects_a_drain_only_dependency() {
    // Arrange.
    let mut fixture = economic_fixture(
        &[EconomicLaneIdV1::SpotLiquidity],
        EconomicLaneIdV1::SpotLiquidity,
        LaneModuleReleaseStatusV1::DrainOnly,
    );
    let drain_release = fixture.module_registries
        [usize::from(EconomicLaneIdV1::SpotLiquidity.code())]
    .releases()[0]
        .clone();
    let route = route_with_purpose(
        50,
        &drain_release,
        RouteDependencyLifecyclePurposeV1::ActiveNewRelease,
    );
    fixture.route_registry = RouteReleaseRegistryV1::new(vec![route]).unwrap();
    let roots = EconomicProfileRegistryRootsV1::new(
        fixture.lane_registry.canonical_commitment().unwrap(),
        fixture.route_registry.canonical_root().unwrap(),
        root(600),
        root(601),
        root(602),
        root(603),
        root(604),
    );
    fixture.profile = profile(0, 0, EconomicProfileTransitionModeV1::Genesis, None, roots);

    // Act.
    let result = fixture.profile.bind_economic_registries(
        &fixture.lane_registry,
        &fixture.module_registries,
        &fixture.route_registry,
    );

    // Assert.
    assert!(matches!(
        result,
        Err(EconomicProfileSnapshotErrorV1::DependencyReleaseAdmission {
            source: LaneModuleReleaseErrorV1::StatusDisallowsNewObject(
                LaneModuleReleaseStatusV1::DrainOnly
            ),
            ..
        })
    ));
}

#[test]
fn route_dependency_release_must_occur_in_the_profile_bound_module_registry() {
    // Arrange
    let fixture = economic_fixture(
        &[EconomicLaneIdV1::SpotLiquidity],
        EconomicLaneIdV1::SpotLiquidity,
        LaneModuleReleaseStatusV1::ActiveNew,
    );
    let mut module_registries = fixture.module_registries.clone();
    let replacement = module_release(
        EconomicLaneIdV1::SpotLiquidity,
        900,
        LaneModuleReleaseStatusV1::ActiveNew,
    );
    module_registries[usize::from(EconomicLaneIdV1::SpotLiquidity.code())] =
        LaneModuleReleaseRegistryV1::new(EconomicLaneIdV1::SpotLiquidity, vec![replacement])
            .unwrap();
    let entries = module_registries
        .iter()
        .map(|registry| {
            let command_status = if registry.lane_id() == EconomicLaneIdV1::SpotLiquidity {
                zenodex_zrpf_protocol_v3::EconomicLaneCommandStatusV1::Enabled
            } else {
                zenodex_zrpf_protocol_v3::EconomicLaneCommandStatusV1::Disabled
            };
            zenodex_zrpf_protocol_v3::EconomicLaneRegistryEntryV1::new(
                registry.lane_id(),
                command_status,
                registry.canonical_root().unwrap(),
            )
        })
        .collect();
    let lane_registry =
        zenodex_zrpf_protocol_v3::GlobalEconomicLaneRegistryV1::new(entries).unwrap();
    let roots = fixture.profile.content().registry_roots();
    let profile = profile(
        0,
        0,
        fixture.profile.content().transition_mode(),
        None,
        EconomicProfileRegistryRootsV1::new(
            lane_registry.canonical_commitment().unwrap(),
            roots.route_release_registry_root(),
            roots.proof_shape_registry_root(),
            roots.verifier_registry_root(),
            roots.migration_registry_root(),
            roots.policy_registry_root(),
            roots.terminal_registry_root(),
        ),
    );

    // Act
    let result = profile.bind_economic_registries(
        &lane_registry,
        &module_registries,
        &fixture.route_registry,
    );

    // Assert
    assert!(matches!(
        result,
        Err(EconomicProfileSnapshotErrorV1::UnknownDependencyRelease {
            lane_id: EconomicLaneIdV1::SpotLiquidity,
            ..
        })
    ));
}
