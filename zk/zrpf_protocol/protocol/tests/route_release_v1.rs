use zenodex_zrpf_protocol_v3::{
    EconomicLaneIdV1, RouteDependencyRoleV1, RouteDependencyRolesV1, RouteIssueBurnPolicyV1,
    RouteModuleDependencyV1, RouteOraclePolicyV1, RouteReleaseErrorV1, RouteResourceLimitsV1,
    MAX_ROUTE_DEPENDENCIES_V1,
};

#[path = "route_release_v1/binding.rs"]
mod binding;
#[path = "route_release_v1/codec.rs"]
mod codec;
#[path = "route_release_v1/identity.rs"]
mod identity;
#[path = "route_release_v1/support.rs"]
mod support;

use support::{content, dependency, roles, root, route};

#[test]
fn dependency_count_boundaries_are_zero_one_eight_and_nine() {
    // Arrange
    let zero_dependencies = boundary_dependencies(0);
    let one_dependency = boundary_dependencies(1);
    let maximum_dependencies = boundary_dependencies(MAX_ROUTE_DEPENDENCIES_V1);
    let above_maximum_dependencies = boundary_dependencies(MAX_ROUTE_DEPENDENCIES_V1 + 1);

    // Act
    let empty = content(
        zero_dependencies,
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
    );
    let one_result = content(
        one_dependency,
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
    );
    let maximum_result = content(
        maximum_dependencies,
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
    );
    let above_result = content(
        above_maximum_dependencies,
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
    );

    // Assert
    assert_eq!(empty, Err(RouteReleaseErrorV1::EmptyDependencies));
    assert_eq!(one_result.unwrap().dependencies().len(), 1);
    assert_eq!(
        maximum_result.unwrap().dependencies().len(),
        MAX_ROUTE_DEPENDENCIES_V1
    );
    assert_eq!(
        above_result,
        Err(RouteReleaseErrorV1::TooManyDependencies {
            actual: MAX_ROUTE_DEPENDENCIES_V1 + 1,
            maximum: MAX_ROUTE_DEPENDENCIES_V1,
        })
    );
}

fn boundary_dependencies(count: usize) -> Vec<RouteModuleDependencyV1> {
    (0..count)
        .map(|index| {
            let role = if index == 0 {
                RouteDependencyRoleV1::Primary
            } else {
                RouteDependencyRoleV1::State
            };
            dependency(
                EconomicLaneIdV1::ALL[index],
                u8::try_from(index + 1).unwrap(),
                roles(&[role]),
            )
        })
        .collect()
}

#[test]
fn role_sets_are_closed_nonempty_unique_and_multi_role() {
    // Arrange / Act
    let empty = RouteDependencyRolesV1::new(&[]);
    let duplicate = RouteDependencyRolesV1::new(&[
        RouteDependencyRoleV1::Primary,
        RouteDependencyRoleV1::Primary,
    ]);
    let combined = RouteDependencyRolesV1::new(&[
        RouteDependencyRoleV1::Primary,
        RouteDependencyRoleV1::Custody,
        RouteDependencyRoleV1::Terminal,
    ])
    .unwrap();

    // Assert
    assert_eq!(empty, Err(RouteReleaseErrorV1::EmptyDependencyRoles));
    assert_eq!(
        duplicate,
        Err(RouteReleaseErrorV1::DuplicateDependencyRole(
            RouteDependencyRoleV1::Primary
        ))
    );
    assert!(combined.contains(RouteDependencyRoleV1::Primary));
    assert!(combined.contains(RouteDependencyRoleV1::Custody));
    assert!(combined.contains(RouteDependencyRoleV1::Terminal));
    assert_eq!(combined.bits(), 0b100_1001);
}

#[test]
fn primary_role_cardinality_is_exactly_one() {
    // Arrange
    let no_primary = vec![dependency(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        roles(&[RouteDependencyRoleV1::State]),
    )];
    let one_primary = vec![dependency(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        roles(&[RouteDependencyRoleV1::Primary]),
    )];
    let two_primary = vec![
        dependency(
            EconomicLaneIdV1::SpotLiquidity,
            1,
            roles(&[RouteDependencyRoleV1::Primary]),
        ),
        dependency(
            EconomicLaneIdV1::OracleMarket,
            2,
            roles(&[RouteDependencyRoleV1::Primary]),
        ),
    ];

    // Act
    let zero = content(
        no_primary,
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
    );
    let one = content(
        one_primary,
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
    );
    let two = content(
        two_primary,
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
    );

    // Assert
    assert_eq!(zero, Err(RouteReleaseErrorV1::PrimaryDependencyCount(0)));
    assert!(one.is_ok());
    assert_eq!(two, Err(RouteReleaseErrorV1::PrimaryDependencyCount(2)));
}

#[test]
fn duplicate_lane_rejects_without_mutating_caller_owned_dependencies() {
    // Arrange
    let dependencies = vec![
        dependency(
            EconomicLaneIdV1::SpotLiquidity,
            1,
            roles(&[RouteDependencyRoleV1::Primary]),
        ),
        dependency(
            EconomicLaneIdV1::SpotLiquidity,
            2,
            roles(&[RouteDependencyRoleV1::State]),
        ),
    ];
    let before = dependencies.clone();

    // Act
    let result = content(
        dependencies.clone(),
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
    );

    // Assert
    assert_eq!(
        result,
        Err(RouteReleaseErrorV1::DuplicateDependencyLane(
            EconomicLaneIdV1::SpotLiquidity
        ))
    );
    assert_eq!(dependencies, before);
}

#[test]
fn oracle_policy_and_dependency_role_are_coherent() {
    // Arrange
    let primary = dependency(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        roles(&[RouteDependencyRoleV1::Primary]),
    );
    let oracle = dependency(
        EconomicLaneIdV1::OracleMarket,
        2,
        roles(&[RouteDependencyRoleV1::Oracle]),
    );
    let second_oracle = dependency(
        EconomicLaneIdV1::StrategyEscrow,
        3,
        roles(&[RouteDependencyRoleV1::Oracle]),
    );
    let required = RouteOraclePolicyV1::Required {
        policy_root: root(60),
    };

    // Act
    let forbidden_with_role = content(
        vec![primary.clone(), oracle.clone()],
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
    );
    let required_without_role = content(
        vec![primary.clone()],
        required,
        RouteIssueBurnPolicyV1::Forbidden,
    );
    let required_once = content(
        vec![primary.clone(), oracle.clone()],
        required,
        RouteIssueBurnPolicyV1::Forbidden,
    );
    let required_twice = content(
        vec![primary, oracle, second_oracle],
        required,
        RouteIssueBurnPolicyV1::Forbidden,
    );

    // Assert
    assert_eq!(
        forbidden_with_role,
        Err(RouteReleaseErrorV1::OracleDependencyCount(1))
    );
    assert_eq!(
        required_without_role,
        Err(RouteReleaseErrorV1::OracleDependencyCount(0))
    );
    assert!(required_once.is_ok());
    assert_eq!(
        required_twice,
        Err(RouteReleaseErrorV1::OracleDependencyCount(2))
    );
}

#[test]
fn issue_burn_policy_and_dependency_role_are_coherent() {
    // Arrange
    let primary = dependency(
        EconomicLaneIdV1::ZusdMonetary,
        1,
        roles(&[RouteDependencyRoleV1::Primary]),
    );
    let issue_burn = dependency(
        EconomicLaneIdV1::AssetTransfer,
        2,
        roles(&[RouteDependencyRoleV1::IssueBurn]),
    );
    let second_issue_burn = dependency(
        EconomicLaneIdV1::ZdexTokenomics,
        3,
        roles(&[RouteDependencyRoleV1::IssueBurn]),
    );
    let authorized = RouteIssueBurnPolicyV1::IssueAndBurn {
        policy_root: root(61),
    };

    // Act
    let forbidden_with_role = content(
        vec![primary.clone(), issue_burn.clone()],
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
    );
    let authorized_without_role = content(
        vec![primary.clone()],
        RouteOraclePolicyV1::Forbidden,
        authorized,
    );
    let authorized_once = content(
        vec![primary.clone(), issue_burn.clone()],
        RouteOraclePolicyV1::Forbidden,
        authorized,
    );
    let authorized_twice = content(
        vec![primary, issue_burn, second_issue_burn],
        RouteOraclePolicyV1::Forbidden,
        authorized,
    );

    // Assert
    assert_eq!(
        forbidden_with_role,
        Err(RouteReleaseErrorV1::IssueBurnDependencyCount(1))
    );
    assert_eq!(
        authorized_without_role,
        Err(RouteReleaseErrorV1::IssueBurnDependencyCount(0))
    );
    assert!(authorized_once.is_ok());
    assert_eq!(
        authorized_twice,
        Err(RouteReleaseErrorV1::IssueBurnDependencyCount(2))
    );
}

#[test]
fn dependency_order_is_semantic_and_changes_route_identity() {
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

    // Act
    let first = route(vec![primary.clone(), state.clone()]);
    let second = route(vec![state, primary]);

    // Assert
    assert_ne!(first.route_release_id(), second.route_release_id());
    assert_ne!(
        first.content().dependencies(),
        second.content().dependencies()
    );
}

#[test]
fn resource_limits_cover_zero_one_and_integer_maxima() {
    // Arrange / Act
    let one = RouteResourceLimitsV1::new(1, 1, 1).unwrap();
    let maxima = RouteResourceLimitsV1::new(u32::MAX, u32::MAX, u64::MAX).unwrap();

    // Assert
    assert_eq!(
        RouteResourceLimitsV1::new(0, 1, 1),
        Err(RouteReleaseErrorV1::ZeroResourceLimit(
            "max_total_journal_bytes"
        ))
    );
    assert_eq!(
        RouteResourceLimitsV1::new(1, 0, 1),
        Err(RouteReleaseErrorV1::ZeroResourceLimit(
            "max_private_port_bytes"
        ))
    );
    assert_eq!(
        RouteResourceLimitsV1::new(1, 1, 0),
        Err(RouteReleaseErrorV1::ZeroResourceLimit(
            "max_composition_cycles"
        ))
    );
    assert_eq!(one.max_total_journal_bytes(), 1);
    assert_eq!(one.max_private_port_bytes(), 1);
    assert_eq!(one.max_composition_cycles(), 1);
    assert_eq!(maxima.max_total_journal_bytes(), u32::MAX);
    assert_eq!(maxima.max_private_port_bytes(), u32::MAX);
    assert_eq!(maxima.max_composition_cycles(), u64::MAX);
}
