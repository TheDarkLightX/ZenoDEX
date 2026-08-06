use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    CommitmentV3, EconomicLaneIdV1, LaneModuleMigrationCompatibilityV1, LaneModuleMigrationModeV1,
    LaneModuleProvenanceRootsV1, LaneModuleReleaseContentV1, LaneModuleReleaseRegistryV1,
    LaneModuleReleaseStatusV1, LaneModuleReleaseV1, LaneModuleResourceLimitsV1,
    LaneModuleSchemaRootsV1, LaneModuleTerminalCoverageV1, ProgramIdV3,
    RouteDependencyLifecyclePurposeV1, RouteDependencyRoleV1, RouteDependencyRolesV1,
    RouteIssueBurnPolicyV1, RouteModuleDependencyV1, RouteModuleReleaseSelectionV1,
    RouteOraclePolicyV1, RouteReleaseContentV1, RouteReleaseRegistryV1, RouteReleaseV1,
    RouteResourceLimitsV1, RouteSelectionKeyV1, TerminalCoverageStatusV1,
};

pub fn root(seed: u16) -> CommitmentV3 {
    let mut bytes = [0u8; 32];
    bytes[..2].copy_from_slice(&seed.max(1).to_be_bytes());
    bytes[31] = 1;
    CommitmentV3::new(bytes).expect("fixture commitment is nonzero")
}

pub fn roles(values: &[RouteDependencyRoleV1]) -> RouteDependencyRolesV1 {
    RouteDependencyRolesV1::new(values).expect("fixture roles are valid")
}

pub fn module_release(lane_id: EconomicLaneIdV1, seed: u16) -> LaneModuleReleaseV1 {
    let content = LaneModuleReleaseContentV1::new(
        lane_id,
        LaneModuleSchemaRootsV1::new(root(seed), root(seed + 1), root(seed + 2), root(seed + 3)),
        root(seed + 4),
        LaneModuleProvenanceRootsV1::new(
            ProgramIdV3::new(root(seed + 5).into_bytes()).unwrap(),
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

pub fn module_registry(lane_id: EconomicLaneIdV1, seed: u16) -> LaneModuleReleaseRegistryV1 {
    LaneModuleReleaseRegistryV1::new(lane_id, vec![module_release(lane_id, seed)]).unwrap()
}

pub fn module_release_selection(
    lane_id: EconomicLaneIdV1,
    seed: u16,
) -> RouteModuleReleaseSelectionV1 {
    RouteModuleReleaseSelectionV1::new(lane_id, module_release(lane_id, seed).release_id())
}

pub fn dependency(
    lane_id: EconomicLaneIdV1,
    seed: u16,
    roles: RouteDependencyRolesV1,
) -> RouteModuleDependencyV1 {
    RouteModuleDependencyV1::new(
        lane_id,
        module_release(lane_id, seed).release_id(),
        RouteDependencyLifecyclePurposeV1::PinnedExistingObjects,
        roles,
        root(seed + 20),
        root(seed + 21),
        root(seed + 22),
    )
}

pub fn route(command_seed: u16, lane_id: EconomicLaneIdV1, release_seed: u16) -> RouteReleaseV1 {
    custom_route(
        root(command_seed),
        vec![dependency(
            lane_id,
            release_seed,
            roles(&[RouteDependencyRoleV1::Primary]),
        )],
        root(50),
    )
}

pub fn custom_route(
    command_variant_root: CommitmentV3,
    dependencies: Vec<RouteModuleDependencyV1>,
    port_pairing_root: CommitmentV3,
) -> RouteReleaseV1 {
    RouteReleaseV1::new(
        RouteReleaseContentV1::new(
            command_variant_root,
            dependencies,
            port_pairing_root,
            RouteOraclePolicyV1::Forbidden,
            RouteIssueBurnPolicyV1::Forbidden,
            RouteResourceLimitsV1::new(32_768, 16_384, 2_000_000).unwrap(),
        )
        .unwrap(),
    )
    .unwrap()
}

pub fn canonical_routes(mut routes: Vec<RouteReleaseV1>) -> Vec<RouteReleaseV1> {
    routes.sort_by_key(RouteSelectionKeyV1::from_route);
    routes
}

pub fn registry(routes: Vec<RouteReleaseV1>) -> RouteReleaseRegistryV1 {
    RouteReleaseRegistryV1::new(canonical_routes(routes)).unwrap()
}

pub fn digest(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

pub fn hex32(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
