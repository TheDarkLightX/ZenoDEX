use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    CommitmentV3, EconomicLaneIdV1, LaneModuleMigrationCompatibilityV1, LaneModuleMigrationModeV1,
    LaneModuleProvenanceRootsV1, LaneModuleReleaseContentV1, LaneModuleReleaseRegistryV1,
    LaneModuleReleaseStatusV1, LaneModuleReleaseV1, LaneModuleResourceLimitsV1,
    LaneModuleSchemaRootsV1, LaneModuleTerminalCoverageV1, ProgramIdV3, RouteDependencyRoleV1,
    RouteDependencyRolesV1, RouteIssueBurnPolicyV1, RouteModuleDependencyV1, RouteOraclePolicyV1,
    RouteReleaseContentV1, RouteReleaseErrorV1, RouteReleaseV1, RouteResourceLimitsV1,
    TerminalCoverageStatusV1,
};

pub fn root(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).expect("fixture commitment is nonzero")
}

pub fn roles(values: &[RouteDependencyRoleV1]) -> RouteDependencyRolesV1 {
    RouteDependencyRolesV1::new(values).expect("fixture roles are valid")
}

pub fn module_release(lane_id: EconomicLaneIdV1, seed: u8) -> LaneModuleReleaseV1 {
    let content = LaneModuleReleaseContentV1::new(
        lane_id,
        LaneModuleSchemaRootsV1::new(root(seed), root(seed + 1), root(seed + 2), root(seed + 3)),
        root(seed + 4),
        LaneModuleProvenanceRootsV1::new(
            ProgramIdV3::new([seed + 5; 32]).unwrap(),
            root(seed + 6),
            root(seed + 7),
            root(seed + 8),
        ),
        LaneModuleTerminalCoverageV1::new(TerminalCoverageStatusV1::Complete, root(seed + 9)),
        LaneModuleMigrationCompatibilityV1::new(
            LaneModuleMigrationModeV1::Genesis,
            None,
            root(seed + 10),
        )
        .unwrap(),
        LaneModuleResourceLimitsV1::new(1_024, 65_536, 4_096, 1_000_000).unwrap(),
    );
    LaneModuleReleaseV1::new(content, LaneModuleReleaseStatusV1::Candidate).unwrap()
}

pub fn dependency(
    lane_id: EconomicLaneIdV1,
    seed: u8,
    roles: RouteDependencyRolesV1,
) -> RouteModuleDependencyV1 {
    let release = module_release(lane_id, seed);
    RouteModuleDependencyV1::new(
        lane_id,
        release.release_id(),
        roles,
        root(seed + 20),
        root(seed + 21),
        root(seed + 22),
    )
}

pub fn content(
    dependencies: Vec<RouteModuleDependencyV1>,
    oracle_policy: RouteOraclePolicyV1,
    issue_burn_policy: RouteIssueBurnPolicyV1,
) -> Result<RouteReleaseContentV1, RouteReleaseErrorV1> {
    RouteReleaseContentV1::new(
        root(50),
        dependencies,
        root(51),
        oracle_policy,
        issue_burn_policy,
        RouteResourceLimitsV1::new(32_768, 16_384, 2_000_000).unwrap(),
    )
}

pub fn route(dependencies: Vec<RouteModuleDependencyV1>) -> RouteReleaseV1 {
    RouteReleaseV1::new(
        content(
            dependencies,
            RouteOraclePolicyV1::Forbidden,
            RouteIssueBurnPolicyV1::Forbidden,
        )
        .unwrap(),
    )
    .unwrap()
}

pub fn module_registry(
    dependency: &RouteModuleDependencyV1,
    seed: u8,
) -> LaneModuleReleaseRegistryV1 {
    let matching = module_release(dependency.lane_id(), seed);
    assert_eq!(matching.release_id(), dependency.module_release_id());
    LaneModuleReleaseRegistryV1::new(dependency.lane_id(), vec![matching]).unwrap()
}

pub fn hex32(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

pub fn digest(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
