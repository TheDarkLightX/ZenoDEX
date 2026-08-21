//! RIPR evidence for the profile-selected route/full-state projection obligation.
//!
//! Direct structural checks are the semantic oracle. The shared golden root is
//! an additional Python/Rust canonical-encoding drift detector.

use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    hash_global_v1, project_route_global_state_v1, AbiErrorV1, EconomicProfileSnapshotV1,
    EvidenceStatusV1, GlobalEconomicStateV1, LaneCompositionJournalV1, LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1, LaneIdV1, LaneModuleReleaseV1, LaneRegistryV1, LaneStateRootV1,
    ProfileStatusV1, ReleaseStatusV1, RootV1, RouteCompositionJournalV1,
    RouteGlobalStateProjectionCandidateV1, RouteRegistryV1, RouteReleaseV1, ALL_LANE_IDS_V1,
    GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1,
};

const COMMAND_KIND: &str = "PROJECT_ROUTE_STATE";

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "projection test root", false).unwrap()
}

fn zero_root() -> RootV1 {
    RootV1::parse(ZERO_ROOT_V1, "projection test zero root", true).unwrap()
}

fn active_evidence() -> Vec<EvidenceStatusV1> {
    vec![
        EvidenceStatusV1::IMPLEMENTED,
        EvidenceStatusV1::MIGRATABLE,
        EvidenceStatusV1::MOUNTED,
        EvidenceStatusV1::NO_BYPASS,
        EvidenceStatusV1::PROVED,
        EvidenceStatusV1::RELEASE_BACKED,
        EvidenceStatusV1::SPECIFIED,
        EvidenceStatusV1::TERMINAL_COMPLETE,
        EvidenceStatusV1::TESTED,
    ]
}

fn is_selected(lane_id: LaneIdV1) -> bool {
    matches!(
        lane_id,
        LaneIdV1::ASSET_TRANSFER | LaneIdV1::ZDEX_TOKENOMICS
    )
}

fn lane_release(lane_id: LaneIdV1, ordinal: u64) -> LaneModuleReleaseV1 {
    let selected = is_selected(lane_id);
    let offset = ordinal * 32;
    let state_schema_root = root(100 + offset);
    let command_variants = if selected {
        vec![COMMAND_KIND.to_owned()]
    } else {
        vec![]
    };
    let guest_image_id = root(101 + offset);
    let specification_root = root(102 + offset);
    let source_root = root(103 + offset);
    let toolchain_root = root(104 + offset);
    let terminal_coverage_root = root(105 + offset);
    let migration_compatibility_root = root(106 + offset);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "lane_id": lane_id,
        "state_schema_root": state_schema_root,
        "command_variants": command_variants,
        "terminal_command_variants": [],
        "guest_image_id": guest_image_id,
        "specification_root": specification_root,
        "source_root": source_root,
        "toolchain_root": toolchain_root,
        "terminal_coverage_root": terminal_coverage_root,
        "migration_compatibility_root": migration_compatibility_root,
        "max_cycles": 1_000_000,
        "max_journal_bytes": 65_536,
    });
    let release = LaneModuleReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        release_id: hash_global_v1("global-lane-module-release-content-v1", &content).unwrap(),
        semantic_version: "1.0.0-projection-test".to_owned(),
        state_schema_root,
        command_variants,
        terminal_command_variants: vec![],
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        terminal_coverage_root,
        migration_compatibility_root,
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status: if selected {
            ReleaseStatusV1::ACTIVE_NEW
        } else {
            ReleaseStatusV1::SHADOW
        },
        accepts_new_objects: selected,
        evidence_statuses: if selected {
            active_evidence()
        } else {
            vec![EvidenceStatusV1::DISABLED_PROVED_NO_WRITER]
        },
    };
    release.validate().unwrap();
    release
}

fn coordinator_release(lane_id: LaneIdV1, ordinal: u64) -> LaneCoordinatorReleaseV1 {
    let selected = is_selected(lane_id);
    let offset = ordinal * 32;
    let coordinator_schema_root = root(700 + offset);
    let guest_image_id = root(701 + offset);
    let specification_root = root(702 + offset);
    let source_root = root(703 + offset);
    let toolchain_root = root(704 + offset);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "lane_id": lane_id,
        "coordinator_schema_root": coordinator_schema_root,
        "guest_image_id": guest_image_id,
        "specification_root": specification_root,
        "source_root": source_root,
        "toolchain_root": toolchain_root,
        "max_cycles": 1_000_000,
        "max_journal_bytes": 65_536,
    });
    let release = LaneCoordinatorReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        coordinator_release_id: hash_global_v1(
            "global-lane-coordinator-release-content-v1",
            &content,
        )
        .unwrap(),
        semantic_version: "1.0.0-projection-test".to_owned(),
        coordinator_schema_root,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status: if selected {
            ReleaseStatusV1::ACTIVE_NEW
        } else {
            ReleaseStatusV1::SHADOW
        },
        accepts_new_objects: selected,
        evidence_statuses: if selected {
            active_evidence()
        } else {
            vec![EvidenceStatusV1::DISABLED_PROVED_NO_WRITER]
        },
    };
    release.validate().unwrap();
    release
}

fn route(lanes: &LaneRegistryV1) -> RouteReleaseV1 {
    let ordered_lanes = vec![LaneIdV1::ASSET_TRANSFER, LaneIdV1::ZDEX_TOKENOMICS];
    let module_release_ids = ordered_lanes
        .iter()
        .map(|lane_id| lanes.release_for(*lane_id).unwrap().release_id.clone())
        .collect::<Vec<_>>();
    let dependency_roles = vec!["VALUE_OWNER".to_owned(), "FEE_SINK".to_owned()];
    let port_schema_roots = vec![root(1_201), root(1_202)];
    let guest_image_id = root(1_203);
    let specification_root = root(1_204);
    let source_root = root(1_205);
    let toolchain_root = root(1_206);
    let oracle_policy_root = root(1_207);
    let issue_burn_policy_root = root(1_208);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "command_kind": COMMAND_KIND,
        "ordered_lanes": ordered_lanes,
        "module_release_ids": module_release_ids,
        "dependency_roles": dependency_roles,
        "port_schema_roots": port_schema_roots,
        "guest_image_id": guest_image_id,
        "specification_root": specification_root,
        "source_root": source_root,
        "toolchain_root": toolchain_root,
        "oracle_policy_root": oracle_policy_root,
        "issue_burn_policy_root": issue_burn_policy_root,
        "max_cycles": 2_000_000,
        "max_journal_bytes": 131_072,
    });
    let route = RouteReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        route_release_id: hash_global_v1("global-route-release-content-v1", &content).unwrap(),
        semantic_version: "1.0.0-projection-test".to_owned(),
        command_kind: COMMAND_KIND.to_owned(),
        ordered_lanes,
        module_release_ids,
        dependency_roles,
        port_schema_roots,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        oracle_policy_root,
        issue_burn_policy_root,
        max_cycles: 2_000_000,
        max_journal_bytes: 131_072,
        status: ReleaseStatusV1::ACTIVE_NEW,
        accepts_new_objects: true,
        evidence_statuses: active_evidence(),
    };
    route.validate().unwrap();
    route
}

fn profile(
    lanes: &LaneRegistryV1,
    coordinators: &LaneCoordinatorRegistryV1,
    routes: &RouteRegistryV1,
) -> EconomicProfileSnapshotV1 {
    let lane_registry_root = lanes.registry_root().unwrap();
    let lane_coordinator_registry_root = coordinators.registry_root().unwrap();
    let route_registry_root = routes.registry_root().unwrap();
    let proof_shape_root = root(1_301);
    let root_image_id = root(1_302);
    let verifier_registry_root = root(1_303);
    let migration_registry_root = root(1_304);
    let policy_registry_root = root(1_305);
    let terminal_registry_root = root(1_306);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "authority_epoch": 17,
        "lane_registry_root": lane_registry_root,
        "lane_coordinator_registry_root": lane_coordinator_registry_root,
        "route_registry_root": route_registry_root,
        "proof_shape_root": proof_shape_root,
        "root_image_id": root_image_id,
        "verifier_registry_root": verifier_registry_root,
        "migration_registry_root": migration_registry_root,
        "policy_registry_root": policy_registry_root,
        "terminal_registry_root": terminal_registry_root,
    });
    let profile = EconomicProfileSnapshotV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        profile_id: hash_global_v1("global-economic-profile-content-v1", &content).unwrap(),
        authority_epoch: 17,
        lane_registry_root,
        lane_coordinator_registry_root,
        route_registry_root,
        proof_shape_root,
        root_image_id,
        verifier_registry_root,
        migration_registry_root,
        policy_registry_root,
        terminal_registry_root,
        status: ProfileStatusV1::ACTIVE,
    };
    profile
        .validate_registries(lanes, coordinators, routes)
        .unwrap();
    profile
}

fn state(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    selected_root_delta: u64,
) -> GlobalEconomicStateV1 {
    GlobalEconomicStateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-projection-test".to_owned(),
        deployment_root: root(1_400),
        writer_epoch: profile.authority_epoch,
        height: 41,
        profile_root: profile.profile_id.clone(),
        lane_roots: lanes
            .releases
            .iter()
            .enumerate()
            .map(|(index, release)| LaneStateRootV1 {
                lane_id: release.lane_id,
                module_release_id: release.release_id.clone(),
                enabled: release.accepts_new_objects,
                state_root: root(
                    2_001
                        + index as u64
                        + if release.accepts_new_objects {
                            selected_root_delta
                        } else {
                            0
                        },
                ),
            })
            .collect(),
        balances: vec![],
        supplies: vec![],
        custody: vec![],
        liabilities: vec![],
        reserves: vec![],
        oracle_occurrences: vec![],
        replay_state: vec![],
        terminal_obligations: vec![],
        history_root: zero_root(),
        outbox: vec![],
    }
}

struct Fixture {
    profile: EconomicProfileSnapshotV1,
    lanes: LaneRegistryV1,
    coordinators: LaneCoordinatorRegistryV1,
    routes: RouteRegistryV1,
    route: RouteReleaseV1,
    lane_journals: Vec<LaneCompositionJournalV1>,
    route_journal: RouteCompositionJournalV1,
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
}

impl Fixture {
    fn candidate(&self) -> RouteGlobalStateProjectionCandidateV1<'_> {
        RouteGlobalStateProjectionCandidateV1 {
            profile: &self.profile,
            lanes: &self.lanes,
            coordinators: &self.coordinators,
            routes: &self.routes,
            route: &self.route,
            lane_journals: &self.lane_journals,
            route_journal: &self.route_journal,
            pre_state: &self.pre_state,
            post_state: &self.post_state,
        }
    }
}

fn fixture() -> Fixture {
    let lanes = LaneRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane_id)| lane_release(*lane_id, index as u64 + 1))
            .collect(),
    };
    let coordinators = LaneCoordinatorRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane_id)| coordinator_release(*lane_id, index as u64 + 1))
            .collect(),
    };
    let route = route(&lanes);
    let routes = RouteRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        routes: vec![route.clone()],
    };
    let profile = profile(&lanes, &coordinators, &routes);
    let pre_state = state(&profile, &lanes, 0);
    let post_state = state(&profile, &lanes, 10_000);
    let occurrence_id = root(1_500);
    let lane_journals = route
        .ordered_lanes
        .iter()
        .enumerate()
        .map(|(index, lane_id)| {
            let lane_index = ALL_LANE_IDS_V1
                .iter()
                .position(|item| item == lane_id)
                .unwrap();
            LaneCompositionJournalV1 {
                schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
                chain_id: pre_state.chain_id.clone(),
                deployment_root: pre_state.deployment_root.clone(),
                profile_root: profile.profile_id.clone(),
                writer_epoch: profile.authority_epoch,
                lane_id: *lane_id,
                coordinator_release_id: coordinators
                    .release_for(*lane_id)
                    .unwrap()
                    .coordinator_release_id
                    .clone(),
                command_occurrence_id: occurrence_id.clone(),
                ordered_module_journal_roots: vec![root(1_600 + index as u64)],
                pre_lane_root: pre_state.lane_roots[lane_index].state_root.clone(),
                post_lane_root: post_state.lane_roots[lane_index].state_root.clone(),
                effect_plan_root: root(1_700 + index as u64),
                terminal_obligations_root: root(1_800 + index as u64),
            }
        })
        .collect::<Vec<_>>();
    let route_journal = RouteCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: pre_state.chain_id.clone(),
        deployment_root: pre_state.deployment_root.clone(),
        profile_root: profile.profile_id.clone(),
        writer_epoch: profile.authority_epoch,
        route_release_id: route.route_release_id.clone(),
        command_occurrence_id: occurrence_id,
        ordered_lane_journal_roots: lane_journals
            .iter()
            .map(|journal| journal.journal_root().unwrap())
            .collect(),
        pre_state_root: pre_state.state_root().unwrap(),
        post_state_root: post_state.state_root().unwrap(),
        effect_plan_root: root(1_900),
        terminal_obligations_root: root(1_901),
    };
    Fixture {
        profile,
        lanes,
        coordinators,
        routes,
        route,
        lane_journals,
        route_journal,
        pre_state,
        post_state,
    }
}

#[test]
fn projection_matches_python_golden_root() {
    let fixture = fixture();

    let projection = project_route_global_state_v1(fixture.candidate()).unwrap();

    assert_eq!(projection.ordered_lane_ids(), fixture.route.ordered_lanes);
    assert_eq!(
        projection.pre_state_root(),
        &fixture.route_journal.pre_state_root
    );
    assert_eq!(
        projection.post_state_root(),
        &fixture.route_journal.post_state_root
    );
    assert_eq!(
        projection.projection_root().unwrap().as_str(),
        "0x11a9c2b222c1c9019efd6803b96bec024f4db47f50087e11bdf389093d46ded7"
    );
}

#[test]
fn rejects_inactive_profile_and_route_journal_profile_or_epoch_substitution() {
    let fixture = fixture();
    let mut inactive_profile = fixture.profile.clone();
    inactive_profile.status = ProfileStatusV1::SHADOW;
    let mut candidate = fixture.candidate();
    candidate.profile = &inactive_profile;
    assert_eq!(
        project_route_global_state_v1(candidate),
        Err(AbiErrorV1::InvalidBinding(
            "route global projection active profile"
        ))
    );

    let mut wrong_profile = fixture.route_journal.clone();
    wrong_profile.profile_root = root(9_000);
    let mut candidate = fixture.candidate();
    candidate.route_journal = &wrong_profile;
    assert!(matches!(
        project_route_global_state_v1(candidate),
        Err(AbiErrorV1::InvalidBinding(_))
    ));

    let mut wrong_epoch = fixture.route_journal.clone();
    wrong_epoch.writer_epoch += 1;
    let mut candidate = fixture.candidate();
    candidate.route_journal = &wrong_epoch;
    assert!(matches!(
        project_route_global_state_v1(candidate),
        Err(AbiErrorV1::InvalidBinding(_))
    ));
}

#[test]
fn rejects_global_and_selected_lane_root_substitution() {
    let fixture = fixture();
    let mut wrong_route_journal = fixture.route_journal.clone();
    wrong_route_journal.pre_state_root = root(9_001);
    let mut candidate = fixture.candidate();
    candidate.route_journal = &wrong_route_journal;
    assert!(matches!(
        project_route_global_state_v1(candidate),
        Err(AbiErrorV1::InvalidBinding(_))
    ));

    let mut wrong_lanes = fixture.lane_journals.clone();
    wrong_lanes[0].pre_lane_root = root(9_002);
    let mut bound_route_journal = fixture.route_journal.clone();
    bound_route_journal.ordered_lane_journal_roots = wrong_lanes
        .iter()
        .map(|journal| journal.journal_root().unwrap())
        .collect();
    let mut candidate = fixture.candidate();
    candidate.lane_journals = &wrong_lanes;
    candidate.route_journal = &bound_route_journal;
    assert_eq!(
        project_route_global_state_v1(candidate),
        Err(AbiErrorV1::InvalidBinding(
            "route global projection selected lane root"
        ))
    );
}

#[test]
fn rejects_hidden_unselected_lane_and_metadata_changes() {
    let fixture = fixture();
    let sibling = ALL_LANE_IDS_V1
        .iter()
        .position(|lane| *lane == LaneIdV1::PERPS_MARKET)
        .unwrap();
    let mut changed_post = fixture.post_state.clone();
    changed_post.lane_roots[sibling].state_root = root(9_003);
    let mut changed_route = fixture.route_journal.clone();
    changed_route.post_state_root = changed_post.state_root().unwrap();
    let mut candidate = fixture.candidate();
    candidate.post_state = &changed_post;
    candidate.route_journal = &changed_route;
    assert_eq!(
        project_route_global_state_v1(candidate),
        Err(AbiErrorV1::InvalidBinding(
            "route global projection unselected lane changed"
        ))
    );

    let mut metadata_post = fixture.post_state.clone();
    metadata_post.lane_roots[sibling].module_release_id = root(9_004);
    let mut metadata_route = fixture.route_journal.clone();
    metadata_route.post_state_root = metadata_post.state_root().unwrap();
    let mut candidate = fixture.candidate();
    candidate.post_state = &metadata_post;
    candidate.route_journal = &metadata_route;
    assert!(matches!(
        project_route_global_state_v1(candidate),
        Err(AbiErrorV1::InvalidBinding("global state lane release"))
    ));
}

#[test]
fn rejects_lane_journal_reorder_duplicate_and_omission() {
    let fixture = fixture();
    let reordered = vec![
        fixture.lane_journals[1].clone(),
        fixture.lane_journals[0].clone(),
    ];
    let duplicated = vec![
        fixture.lane_journals[0].clone(),
        fixture.lane_journals[0].clone(),
    ];
    let omitted = vec![fixture.lane_journals[0].clone()];

    for journals in [&reordered, &duplicated, &omitted] {
        let mut candidate = fixture.candidate();
        candidate.lane_journals = journals;
        assert!(matches!(
            project_route_global_state_v1(candidate),
            Err(AbiErrorV1::InvalidOrder(_) | AbiErrorV1::InvalidBinding(_))
        ));
    }
}

#[test]
fn rejects_route_and_coordinator_substitution() {
    let fixture = fixture();
    let mut wrong_route = fixture.route.clone();
    wrong_route.semantic_version = "forged-display-version".to_owned();
    let mut candidate = fixture.candidate();
    candidate.route = &wrong_route;
    assert_eq!(
        project_route_global_state_v1(candidate),
        Err(AbiErrorV1::InvalidBinding(
            "route global projection governed route"
        ))
    );

    let mut wrong_lanes = fixture.lane_journals.clone();
    wrong_lanes[0].coordinator_release_id = root(9_006);
    let mut wrong_route_journal = fixture.route_journal.clone();
    wrong_route_journal.ordered_lane_journal_roots = wrong_lanes
        .iter()
        .map(|journal| journal.journal_root().unwrap())
        .collect();
    let mut candidate = fixture.candidate();
    candidate.lane_journals = &wrong_lanes;
    candidate.route_journal = &wrong_route_journal;
    assert_eq!(
        project_route_global_state_v1(candidate),
        Err(AbiErrorV1::InvalidBinding(
            "route global projection exact lane journal context"
        ))
    );
}

#[test]
fn coherent_selected_lane_transition_changes_projection_root() {
    let fixture = fixture();
    let original = project_route_global_state_v1(fixture.candidate()).unwrap();
    let selected = ALL_LANE_IDS_V1
        .iter()
        .position(|lane| *lane == LaneIdV1::ASSET_TRANSFER)
        .unwrap();
    let mut changed_post = fixture.post_state.clone();
    changed_post.lane_roots[selected].state_root = root(9_007);
    let mut changed_lanes = fixture.lane_journals.clone();
    changed_lanes[0].post_lane_root = root(9_007);
    let mut changed_route = fixture.route_journal.clone();
    changed_route.ordered_lane_journal_roots = changed_lanes
        .iter()
        .map(|journal| journal.journal_root().unwrap())
        .collect();
    changed_route.post_state_root = changed_post.state_root().unwrap();
    let mut candidate = fixture.candidate();
    candidate.post_state = &changed_post;
    candidate.lane_journals = &changed_lanes;
    candidate.route_journal = &changed_route;

    let changed = project_route_global_state_v1(candidate).unwrap();

    assert_ne!(
        changed.projection_root().unwrap(),
        original.projection_root().unwrap()
    );
}
