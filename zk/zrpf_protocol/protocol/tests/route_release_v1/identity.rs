use std::collections::BTreeSet;

use zenodex_zrpf_protocol_v3::{
    EconomicLaneIdV1, RouteDependencyRoleV1, RouteIssueBurnPolicyV1, RouteModuleDependencyV1,
    RouteOraclePolicyV1, RouteReleaseContentV1, RouteReleaseErrorV1, RouteReleaseIdV1,
    RouteReleaseV1, RouteResourceLimitsV1,
};

use super::support::{dependency, roles, root};

#[test]
fn command_dependency_and_schema_fields_are_content_bound() {
    // Arrange
    let base_dependency = dependency(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        roles(&[RouteDependencyRoleV1::Primary]),
    );
    let limits = RouteResourceLimitsV1::new(32_768, 16_384, 2_000_000).unwrap();
    let base = route_id(root(50), base_dependency.clone(), root(51), limits);
    let release_changed = dependency(
        EconomicLaneIdV1::SpotLiquidity,
        2,
        roles(&[RouteDependencyRoleV1::Primary]),
    );
    let role_changed = RouteModuleDependencyV1::new(
        base_dependency.lane_id(),
        base_dependency.module_release_id(),
        roles(&[RouteDependencyRoleV1::Primary, RouteDependencyRoleV1::State]),
        base_dependency.receipt_journal_schema_root(),
        base_dependency.input_port_schema_root(),
        base_dependency.output_port_schema_root(),
    );
    let receipt_changed = with_schema_roots(&base_dependency, root(70), root(22), root(23));
    let input_changed = with_schema_roots(&base_dependency, root(21), root(71), root(23));
    let output_changed = with_schema_roots(&base_dependency, root(21), root(22), root(72));

    // Act
    let identities = [
        base,
        route_id(root(52), base_dependency, root(51), limits),
        route_id(root(50), release_changed, root(51), limits),
        route_id(root(50), role_changed, root(51), limits),
        route_id(root(50), receipt_changed, root(51), limits),
        route_id(root(50), input_changed, root(51), limits),
        route_id(root(50), output_changed, root(51), limits),
    ];

    // Assert
    assert_eq!(
        identities.iter().copied().collect::<BTreeSet<_>>().len(),
        identities.len()
    );
}

#[test]
fn port_pairing_and_resource_limits_are_content_bound() {
    // Arrange
    let dependency = dependency(
        EconomicLaneIdV1::SpotLiquidity,
        1,
        roles(&[RouteDependencyRoleV1::Primary]),
    );
    let limits = RouteResourceLimitsV1::new(32_768, 16_384, 2_000_000).unwrap();

    // Act
    let identities = [
        route_id(root(50), dependency.clone(), root(51), limits),
        route_id(root(50), dependency.clone(), root(53), limits),
        route_id(
            root(50),
            dependency.clone(),
            root(51),
            RouteResourceLimitsV1::new(32_769, 16_384, 2_000_000).unwrap(),
        ),
        route_id(
            root(50),
            dependency.clone(),
            root(51),
            RouteResourceLimitsV1::new(32_768, 16_385, 2_000_000).unwrap(),
        ),
        route_id(
            root(50),
            dependency,
            root(51),
            RouteResourceLimitsV1::new(32_768, 16_384, 2_000_001).unwrap(),
        ),
    ];

    // Assert
    assert_eq!(
        identities.iter().copied().collect::<BTreeSet<_>>().len(),
        identities.len()
    );
}

#[test]
fn zero_route_release_id_is_rejected() {
    // Arrange
    let zero_id = [0; 32];

    // Act
    let result = RouteReleaseIdV1::new(zero_id);

    // Assert
    assert_eq!(result, Err(RouteReleaseErrorV1::ZeroRouteReleaseId));
}

#[test]
fn oracle_policy_root_is_content_bound() {
    // Arrange
    let oracle_dependency = dependency(
        EconomicLaneIdV1::OracleMarket,
        1,
        roles(&[
            RouteDependencyRoleV1::Primary,
            RouteDependencyRoleV1::Oracle,
        ]),
    );
    // Act
    let oracle_a = policy_route_id(
        oracle_dependency.clone(),
        RouteOraclePolicyV1::Required {
            policy_root: root(80),
        },
        RouteIssueBurnPolicyV1::Forbidden,
    );
    let oracle_b = policy_route_id(
        oracle_dependency,
        RouteOraclePolicyV1::Required {
            policy_root: root(81),
        },
        RouteIssueBurnPolicyV1::Forbidden,
    );
    // Assert
    assert_ne!(oracle_a, oracle_b);
}

#[test]
fn every_issue_burn_mode_and_policy_root_is_content_bound() {
    // Arrange
    let dependency = dependency(
        EconomicLaneIdV1::AssetTransfer,
        2,
        roles(&[
            RouteDependencyRoleV1::Primary,
            RouteDependencyRoleV1::IssueBurn,
        ]),
    );

    // Act
    let issue_pair = issue_burn_policy_pair(
        &dependency,
        RouteIssueBurnPolicyV1::IssueOnly {
            policy_root: root(82),
        },
        RouteIssueBurnPolicyV1::IssueOnly {
            policy_root: root(83),
        },
    );
    let burn_pair = issue_burn_policy_pair(
        &dependency,
        RouteIssueBurnPolicyV1::BurnOnly {
            policy_root: root(84),
        },
        RouteIssueBurnPolicyV1::BurnOnly {
            policy_root: root(85),
        },
    );
    let both_pair = issue_burn_policy_pair(
        &dependency,
        RouteIssueBurnPolicyV1::IssueAndBurn {
            policy_root: root(86),
        },
        RouteIssueBurnPolicyV1::IssueAndBurn {
            policy_root: root(87),
        },
    );
    let mode_identities = issue_burn_mode_identities(&dependency);

    // Assert
    assert_ne!(issue_pair.0, issue_pair.1);
    assert_ne!(burn_pair.0, burn_pair.1);
    assert_ne!(both_pair.0, both_pair.1);
    assert_eq!(
        mode_identities
            .iter()
            .copied()
            .collect::<BTreeSet<_>>()
            .len(),
        mode_identities.len()
    );
}

fn issue_burn_mode_identities(dependency: &RouteModuleDependencyV1) -> [RouteReleaseIdV1; 3] {
    [
        issue_burn_route_id(
            dependency.clone(),
            RouteIssueBurnPolicyV1::IssueOnly {
                policy_root: root(88),
            },
        ),
        issue_burn_route_id(
            dependency.clone(),
            RouteIssueBurnPolicyV1::BurnOnly {
                policy_root: root(88),
            },
        ),
        issue_burn_route_id(
            dependency.clone(),
            RouteIssueBurnPolicyV1::IssueAndBurn {
                policy_root: root(88),
            },
        ),
    ]
}

fn route_id(
    command_variant_root: zenodex_zrpf_protocol_v3::CommitmentV3,
    dependency: RouteModuleDependencyV1,
    port_pairing_root: zenodex_zrpf_protocol_v3::CommitmentV3,
    resource_limits: RouteResourceLimitsV1,
) -> RouteReleaseIdV1 {
    let content = RouteReleaseContentV1::new(
        command_variant_root,
        vec![dependency],
        port_pairing_root,
        RouteOraclePolicyV1::Forbidden,
        RouteIssueBurnPolicyV1::Forbidden,
        resource_limits,
    )
    .unwrap();
    assert_eq!(content.command_variant_root(), command_variant_root);
    assert_eq!(content.port_pairing_root(), port_pairing_root);
    assert_eq!(content.resource_limits(), resource_limits);
    RouteReleaseV1::new(content).unwrap().route_release_id()
}

fn policy_route_id(
    dependency: RouteModuleDependencyV1,
    oracle_policy: RouteOraclePolicyV1,
    issue_burn_policy: RouteIssueBurnPolicyV1,
) -> RouteReleaseIdV1 {
    let content = RouteReleaseContentV1::new(
        root(50),
        vec![dependency],
        root(51),
        oracle_policy,
        issue_burn_policy,
        RouteResourceLimitsV1::new(32_768, 16_384, 2_000_000).unwrap(),
    )
    .unwrap();
    assert_eq!(content.oracle_policy(), oracle_policy);
    assert_eq!(content.issue_burn_policy(), issue_burn_policy);
    RouteReleaseV1::new(content).unwrap().route_release_id()
}

fn issue_burn_policy_pair(
    dependency: &RouteModuleDependencyV1,
    first: RouteIssueBurnPolicyV1,
    second: RouteIssueBurnPolicyV1,
) -> (RouteReleaseIdV1, RouteReleaseIdV1) {
    (
        issue_burn_route_id(dependency.clone(), first),
        issue_burn_route_id(dependency.clone(), second),
    )
}

fn issue_burn_route_id(
    dependency: RouteModuleDependencyV1,
    issue_burn_policy: RouteIssueBurnPolicyV1,
) -> RouteReleaseIdV1 {
    policy_route_id(
        dependency,
        RouteOraclePolicyV1::Forbidden,
        issue_burn_policy,
    )
}

fn with_schema_roots(
    dependency: &RouteModuleDependencyV1,
    receipt_journal_schema_root: zenodex_zrpf_protocol_v3::CommitmentV3,
    input_port_schema_root: zenodex_zrpf_protocol_v3::CommitmentV3,
    output_port_schema_root: zenodex_zrpf_protocol_v3::CommitmentV3,
) -> RouteModuleDependencyV1 {
    RouteModuleDependencyV1::new(
        dependency.lane_id(),
        dependency.module_release_id(),
        dependency.roles(),
        receipt_journal_schema_root,
        input_port_schema_root,
        output_port_schema_root,
    )
}
