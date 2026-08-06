use zenodex_zrpf_protocol_v3::{
    CommitmentV3, EconomicLaneCommandStatusV1, EconomicLaneIdV1, EconomicLaneRegistryEntryV1,
    EconomicProfileIdV1, EconomicProfileRegistryRootsV1, EconomicProfileSnapshotContentV1,
    EconomicProfileSnapshotV1, EconomicProfileTransitionModeV1, GlobalEconomicLaneRegistryV1,
    LaneModuleMigrationCompatibilityV1, LaneModuleMigrationModeV1, LaneModuleProvenanceRootsV1,
    LaneModuleReleaseContentV1, LaneModuleReleaseRegistryV1, LaneModuleReleaseStatusV1,
    LaneModuleReleaseV1, LaneModuleResourceLimitsV1, LaneModuleSchemaRootsV1,
    LaneModuleTerminalCoverageV1, ProgramIdV3, RouteDependencyLifecyclePurposeV1,
    RouteDependencyRoleV1, RouteDependencyRolesV1, RouteIssueBurnPolicyV1, RouteModuleDependencyV1,
    RouteOraclePolicyV1, RouteReleaseContentV1, RouteReleaseRegistryV1, RouteReleaseV1,
    RouteResourceLimitsV1, TerminalCoverageStatusV1,
};

pub struct EconomicRegistryFixture {
    pub profile: EconomicProfileSnapshotV1,
    pub lane_registry: GlobalEconomicLaneRegistryV1,
    pub module_registries: Vec<LaneModuleReleaseRegistryV1>,
    pub route_registry: RouteReleaseRegistryV1,
}

pub fn root(seed: u16) -> CommitmentV3 {
    let mut bytes = [0u8; 32];
    bytes[..2].copy_from_slice(&seed.max(1).to_be_bytes());
    bytes[31] = 1;
    CommitmentV3::new(bytes).unwrap()
}

pub fn profile_id(seed: u8) -> EconomicProfileIdV1 {
    EconomicProfileIdV1::new([seed.max(1); 32]).unwrap()
}

pub fn registry_roots(seed: u16) -> EconomicProfileRegistryRootsV1 {
    EconomicProfileRegistryRootsV1::new(
        root(seed),
        root(seed + 1),
        root(seed + 2),
        root(seed + 3),
        root(seed + 4),
        root(seed + 5),
        root(seed + 6),
    )
}

pub fn profile(
    authority_epoch: u64,
    writer_epoch: u64,
    mode: EconomicProfileTransitionModeV1,
    predecessor: Option<EconomicProfileIdV1>,
    roots: EconomicProfileRegistryRootsV1,
) -> EconomicProfileSnapshotV1 {
    EconomicProfileSnapshotV1::new(
        EconomicProfileSnapshotContentV1::new(
            authority_epoch,
            writer_epoch,
            mode,
            predecessor,
            roots,
        )
        .unwrap(),
    )
    .unwrap()
}

pub fn module_release(
    lane_id: EconomicLaneIdV1,
    seed: u16,
    status: LaneModuleReleaseStatusV1,
) -> LaneModuleReleaseV1 {
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
    LaneModuleReleaseV1::new(content, status).unwrap()
}

pub fn route(command_seed: u16, release: &LaneModuleReleaseV1) -> RouteReleaseV1 {
    let lifecycle_purpose = if release.status() == LaneModuleReleaseStatusV1::ActiveNew {
        RouteDependencyLifecyclePurposeV1::ActiveNewRelease
    } else {
        RouteDependencyLifecyclePurposeV1::PinnedExistingObjects
    };
    route_with_purpose(command_seed, release, lifecycle_purpose)
}

pub fn route_with_purpose(
    command_seed: u16,
    release: &LaneModuleReleaseV1,
    lifecycle_purpose: RouteDependencyLifecyclePurposeV1,
) -> RouteReleaseV1 {
    let roles = RouteDependencyRolesV1::new(&[RouteDependencyRoleV1::Primary]).unwrap();
    let dependency = RouteModuleDependencyV1::new(
        release.content().lane_id(),
        release.release_id(),
        lifecycle_purpose,
        roles,
        root(command_seed + 20),
        root(command_seed + 21),
        root(command_seed + 22),
    );
    RouteReleaseV1::new(
        RouteReleaseContentV1::new(
            root(command_seed),
            vec![dependency],
            root(command_seed + 30),
            RouteOraclePolicyV1::Forbidden,
            RouteIssueBurnPolicyV1::Forbidden,
            RouteResourceLimitsV1::new(32_768, 16_384, 2_000_000).unwrap(),
        )
        .unwrap(),
    )
    .unwrap()
}

pub fn economic_fixture(
    enabled_lanes: &[EconomicLaneIdV1],
    route_lane: EconomicLaneIdV1,
    route_release_status: LaneModuleReleaseStatusV1,
) -> EconomicRegistryFixture {
    let mut module_registries = Vec::with_capacity(EconomicLaneIdV1::ALL.len());
    let mut selected_route_release = None;
    for (index, lane_id) in EconomicLaneIdV1::ALL.iter().copied().enumerate() {
        let status = if lane_id == route_lane {
            route_release_status
        } else {
            LaneModuleReleaseStatusV1::Candidate
        };
        let release = module_release(lane_id, index as u16 * 40 + 100, status);
        if lane_id == route_lane {
            selected_route_release = Some(release.clone());
        }
        module_registries.push(LaneModuleReleaseRegistryV1::new(lane_id, vec![release]).unwrap());
    }
    let entries: Vec<_> = module_registries
        .iter()
        .map(|registry| {
            let command_status = if enabled_lanes.contains(&registry.lane_id()) {
                EconomicLaneCommandStatusV1::Enabled
            } else {
                EconomicLaneCommandStatusV1::Disabled
            };
            EconomicLaneRegistryEntryV1::new(
                registry.lane_id(),
                command_status,
                registry.canonical_root().unwrap(),
            )
        })
        .collect();
    let lane_registry = GlobalEconomicLaneRegistryV1::new(entries).unwrap();
    let route_registry =
        RouteReleaseRegistryV1::new(vec![route(50, &selected_route_release.unwrap())]).unwrap();
    let roots = EconomicProfileRegistryRootsV1::new(
        lane_registry.canonical_commitment().unwrap(),
        route_registry.canonical_root().unwrap(),
        root(600),
        root(601),
        root(602),
        root(603),
        root(604),
    );
    EconomicRegistryFixture {
        profile: profile(0, 0, EconomicProfileTransitionModeV1::Genesis, None, roots),
        lane_registry,
        module_registries,
        route_registry,
    }
}

pub fn hex32(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}
