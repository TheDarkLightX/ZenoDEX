use serde_json::{json, Value};
use zenodex_global_settlement_abi_v1::{
    hash_global_v1, EconomicProfileSnapshotV1, EvidenceStatusV1, LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1, LaneIdV1, LaneModuleReleaseV1, LaneRegistryV1, ProfileStatusV1,
    ReleaseStatusV1, RootV1, RouteRegistryV1, RouteReleaseV1, ALL_LANE_IDS_V1,
    ASSET_TRANSFER_COMMAND_KIND_V1, GLOBAL_SETTLEMENT_ABI_V1,
};

use super::authenticated_command::authentication_policy_registry_root_v1;
use super::root;

pub(super) struct ReleaseAwareRegistriesV1 {
    pub profile: EconomicProfileSnapshotV1,
    pub lanes: LaneRegistryV1,
    pub coordinators: LaneCoordinatorRegistryV1,
    pub routes: RouteRegistryV1,
}

fn synthetic_active_evidence_for_closed_test_profile() -> Vec<EvidenceStatusV1> {
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

fn release_status(lane_id: LaneIdV1) -> (ReleaseStatusV1, bool, Vec<EvidenceStatusV1>) {
    if lane_id == LaneIdV1::ASSET_TRANSFER {
        (
            ReleaseStatusV1::ACTIVE_NEW,
            true,
            synthetic_active_evidence_for_closed_test_profile(),
        )
    } else {
        (
            ReleaseStatusV1::SHADOW,
            false,
            vec![EvidenceStatusV1::DISABLED_PROVED_NO_WRITER],
        )
    }
}

struct LaneReleaseContentV1<'a> {
    lane_id: LaneIdV1,
    state_schema_root: &'a RootV1,
    command_variants: &'a [String],
    guest_image_id: &'a RootV1,
    roots: &'a [RootV1; 5],
}

fn lane_release_content(content: LaneReleaseContentV1<'_>) -> Value {
    json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "lane_id": content.lane_id,
        "state_schema_root": content.state_schema_root,
        "command_variants": content.command_variants,
        "terminal_command_variants": Vec::<String>::new(),
        "guest_image_id": content.guest_image_id,
        "specification_root": content.roots[0],
        "source_root": content.roots[1],
        "toolchain_root": content.roots[2],
        "terminal_coverage_root": content.roots[3],
        "migration_compatibility_root": content.roots[4],
        "max_cycles": 1_000_000,
        "max_journal_bytes": 65_536,
    })
}

fn lane_release(lane_id: LaneIdV1, ordinal: u64, asset_image: &RootV1) -> LaneModuleReleaseV1 {
    let is_asset = lane_id == LaneIdV1::ASSET_TRANSFER;
    let offset = ordinal * 16;
    let command_variants = if is_asset {
        vec![ASSET_TRANSFER_COMMAND_KIND_V1.to_owned()]
    } else {
        vec![]
    };
    let state_schema_root = root(100 + offset);
    let guest_image_id = if is_asset {
        asset_image.clone()
    } else {
        root(101 + offset)
    };
    let roots = [
        root(102 + offset),
        root(103 + offset),
        root(104 + offset),
        root(105 + offset),
        root(106 + offset),
    ];
    let content = lane_release_content(LaneReleaseContentV1 {
        lane_id,
        state_schema_root: &state_schema_root,
        command_variants: &command_variants,
        guest_image_id: &guest_image_id,
        roots: &roots,
    });
    let (status, accepts_new_objects, evidence_statuses) = release_status(lane_id);
    let release = LaneModuleReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        release_id: hash_global_v1("global-lane-module-release-content-v1", &content).unwrap(),
        semantic_version: "1.0.0-test".to_owned(),
        state_schema_root,
        command_variants,
        terminal_command_variants: vec![],
        guest_image_id,
        specification_root: roots[0].clone(),
        source_root: roots[1].clone(),
        toolchain_root: roots[2].clone(),
        terminal_coverage_root: roots[3].clone(),
        migration_compatibility_root: roots[4].clone(),
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status,
        accepts_new_objects,
        evidence_statuses,
    };
    release.validate().unwrap();
    release
}

fn coordinator_release_content(
    lane_id: LaneIdV1,
    coordinator_schema_root: &RootV1,
    guest_image_id: &RootV1,
    roots: &[RootV1; 3],
) -> Value {
    json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "lane_id": lane_id,
        "coordinator_schema_root": coordinator_schema_root,
        "guest_image_id": guest_image_id,
        "specification_root": roots[0],
        "source_root": roots[1],
        "toolchain_root": roots[2],
        "max_cycles": 1_000_000,
        "max_journal_bytes": 65_536,
    })
}

fn coordinator_release(
    lane_id: LaneIdV1,
    ordinal: u64,
    asset_image: &RootV1,
) -> LaneCoordinatorReleaseV1 {
    let offset = ordinal * 16;
    let coordinator_schema_root = root(300 + offset);
    let guest_image_id = if lane_id == LaneIdV1::ASSET_TRANSFER {
        asset_image.clone()
    } else {
        root(301 + offset)
    };
    let roots = [root(302 + offset), root(303 + offset), root(304 + offset)];
    let content =
        coordinator_release_content(lane_id, &coordinator_schema_root, &guest_image_id, &roots);
    let (status, accepts_new_objects, evidence_statuses) = release_status(lane_id);
    let release = LaneCoordinatorReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id,
        coordinator_release_id: hash_global_v1(
            "global-lane-coordinator-release-content-v1",
            &content,
        )
        .unwrap(),
        semantic_version: "1.0.0-test".to_owned(),
        coordinator_schema_root,
        guest_image_id,
        specification_root: roots[0].clone(),
        source_root: roots[1].clone(),
        toolchain_root: roots[2].clone(),
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status,
        accepts_new_objects,
        evidence_statuses,
    };
    release.validate().unwrap();
    release
}

fn asset_route(module_release_id: &RootV1) -> RouteReleaseV1 {
    let ordered_lanes = vec![LaneIdV1::ASSET_TRANSFER];
    let module_release_ids = vec![module_release_id.clone()];
    let dependency_roles = vec!["VALUE_OWNER".to_owned()];
    let port_schema_roots = vec![root(500)];
    let roots = [
        root(520),
        root(530),
        root(540),
        root(550),
        root(510),
        root(511),
    ];
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "command_kind": ASSET_TRANSFER_COMMAND_KIND_V1,
        "ordered_lanes": ordered_lanes,
        "module_release_ids": module_release_ids,
        "dependency_roles": dependency_roles,
        "port_schema_roots": port_schema_roots,
        "guest_image_id": roots[0],
        "specification_root": roots[1],
        "source_root": roots[2],
        "toolchain_root": roots[3],
        "oracle_policy_root": roots[4],
        "issue_burn_policy_root": roots[5],
        "max_cycles": 2_000_000,
        "max_journal_bytes": 131_072,
    });
    let route = RouteReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        route_release_id: hash_global_v1("global-route-release-content-v1", &content).unwrap(),
        semantic_version: "1.0.0-test".to_owned(),
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        ordered_lanes,
        module_release_ids,
        dependency_roles,
        port_schema_roots,
        guest_image_id: roots[0].clone(),
        specification_root: roots[1].clone(),
        source_root: roots[2].clone(),
        toolchain_root: roots[3].clone(),
        oracle_policy_root: roots[4].clone(),
        issue_burn_policy_root: roots[5].clone(),
        max_cycles: 2_000_000,
        max_journal_bytes: 131_072,
        status: ReleaseStatusV1::ACTIVE_NEW,
        accepts_new_objects: true,
        evidence_statuses: synthetic_active_evidence_for_closed_test_profile(),
    };
    route.validate().unwrap();
    route
}

fn closed_registries(
    module_image: &RootV1,
    coordinator_image: &RootV1,
) -> (LaneRegistryV1, LaneCoordinatorRegistryV1, RouteRegistryV1) {
    let lanes = LaneRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane)| lane_release(*lane, index as u64 + 1, module_image))
            .collect(),
    };
    let asset_release_id = lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .unwrap()
        .release_id
        .clone();
    let coordinators = LaneCoordinatorRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        releases: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane)| coordinator_release(*lane, index as u64 + 1, coordinator_image))
            .collect(),
    };
    let routes = RouteRegistryV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        routes: vec![asset_route(&asset_release_id)],
    };
    (lanes, coordinators, routes)
}

fn active_profile(
    lanes: &LaneRegistryV1,
    coordinators: &LaneCoordinatorRegistryV1,
    routes: &RouteRegistryV1,
) -> EconomicProfileSnapshotV1 {
    let lane_registry_root = lanes.registry_root().unwrap();
    let lane_coordinator_registry_root = coordinators.registry_root().unwrap();
    let route_registry_root = routes.registry_root().unwrap();
    let roots = [root(600), root(601), root(602), root(603), root(605)];
    let policy_registry_root = authentication_policy_registry_root_v1(routes);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "authority_epoch": 7,
        "lane_registry_root": lane_registry_root,
        "lane_coordinator_registry_root": lane_coordinator_registry_root,
        "route_registry_root": route_registry_root,
        "proof_shape_root": roots[0],
        "root_image_id": roots[1],
        "verifier_registry_root": roots[2],
        "migration_registry_root": roots[3],
        "policy_registry_root": policy_registry_root,
        "terminal_registry_root": roots[4],
    });
    EconomicProfileSnapshotV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        profile_id: hash_global_v1("global-economic-profile-content-v1", &content).unwrap(),
        authority_epoch: 7,
        lane_registry_root,
        lane_coordinator_registry_root,
        route_registry_root,
        proof_shape_root: roots[0].clone(),
        root_image_id: roots[1].clone(),
        verifier_registry_root: roots[2].clone(),
        migration_registry_root: roots[3].clone(),
        policy_registry_root,
        terminal_registry_root: roots[4].clone(),
        status: ProfileStatusV1::ACTIVE,
    }
}

pub(super) fn release_aware_registries_v1(
    module_image: &RootV1,
    coordinator_image: &RootV1,
) -> ReleaseAwareRegistriesV1 {
    let (lanes, coordinators, routes) = closed_registries(module_image, coordinator_image);
    let profile = active_profile(&lanes, &coordinators, &routes);
    profile
        .validate_registries(&lanes, &coordinators, &routes)
        .unwrap();
    ReleaseAwareRegistriesV1 {
        profile,
        lanes,
        coordinators,
        routes,
    }
}
