#![allow(dead_code)]
//! Adapt the retained governed lane scenario; fixture statuses grant no authority.
#[path = "../../asset_lane_coordinator_risc0/host/tests/support/mod.rs"]
mod historical;

use zenodex_asset_lane_coordinator_risc0_shared::prepare_asset_lane_coordinator_v1;
use zenodex_asset_transfer_route_composer_risc0_shared::{
    AssetTransferRouteGuestInputV1, ASSET_TRANSFER_ROUTE_INPUT_SCHEMA_V1,
};
use zenodex_global_settlement_abi_v1::*;

pub use historical::root;

fn content_root<T: serde::Serialize>(domain: &str, value: &T, omitted: &[&str]) -> RootV1 {
    let mut content = serde_json::to_value(value).unwrap();
    for key in omitted {
        content.as_object_mut().unwrap().remove(*key);
    }
    hash_global_v1(domain, &content).unwrap()
}

pub fn input(
    module_image: RootV1,
    coordinator_image: RootV1,
    route_image: RootV1,
) -> AssetTransferRouteGuestInputV1 {
    input_at(module_image, coordinator_image, route_image, None, 10)
}

pub fn input_at(
    module_image: RootV1,
    coordinator_image: RootV1,
    route_image: RootV1,
    root_image: Option<RootV1>,
    predecessor_height: u64,
) -> AssetTransferRouteGuestInputV1 {
    let mut fixture =
        historical::release_aware_asset_lane_fixture_v1(module_image, coordinator_image);
    let route = &mut fixture.routes.routes[0];
    route.guest_image_id = route_image;
    route.route_release_id = content_root(
        "global-route-release-content-v1",
        route,
        &[
            "route_release_id",
            "semantic_version",
            "status",
            "accepts_new_objects",
            "evidence_statuses",
        ],
    );
    fixture.occurrence.route_release_id = route.route_release_id.clone();
    fixture.profile.route_registry_root = fixture.routes.registry_root().unwrap();
    if let Some(root_image) = root_image {
        fixture.profile.root_image_id = root_image;
    }
    fixture.occurrence.height = predecessor_height.checked_add(1).unwrap();
    fixture.profile.profile_id = content_root(
        "global-economic-profile-content-v1",
        &fixture.profile,
        &["profile_id", "status"],
    );
    fixture.occurrence.profile_root = fixture.profile.profile_id.clone();
    fixture.guest_input.module_input.context.profile_root = fixture.profile.profile_id.clone();
    fixture.guest_input.coordinator_context.profile_root = fixture.profile.profile_id.clone();
    let lane = prepare_asset_lane_coordinator_v1(fixture.guest_input.clone()).unwrap();
    let projection = &lane.module_accepted.private_port.pre_state;
    let pre_state = GlobalEconomicStateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: fixture.occurrence.chain_id.clone(),
        deployment_root: fixture.occurrence.deployment_root.clone(),
        writer_epoch: fixture.profile.authority_epoch,
        height: fixture.occurrence.height - 1,
        profile_root: fixture.profile.profile_id.clone(),
        lane_roots: ALL_LANE_IDS_V1
            .into_iter()
            .map(|lane_id| LaneStateRootV1 {
                lane_id,
                module_release_id: fixture
                    .lanes
                    .release_for(lane_id)
                    .unwrap()
                    .release_id
                    .clone(),
                enabled: lane_id == LaneIdV1::ASSET_TRANSFER,
                state_root: if lane_id == LaneIdV1::ASSET_TRANSFER {
                    projection.state_root().unwrap()
                } else {
                    root(700)
                },
            })
            .collect(),
        balances: projection.balances.clone(),
        supplies: projection.supplies.clone(),
        custody: projection.custody.clone(),
        liabilities: vec![],
        reserves: vec![],
        oracle_occurrences: vec![],
        replay_state: vec![],
        terminal_obligations: vec![],
        history_root: root(701),
        outbox: vec![],
    };
    fixture.occurrence.pre_state_root = pre_state.state_root().unwrap();
    let occurrence_id = fixture.occurrence.occurrence_id().unwrap();
    fixture
        .guest_input
        .module_input
        .context
        .command_occurrence_id = occurrence_id.clone();
    fixture
        .guest_input
        .coordinator_context
        .command_occurrence_id = occurrence_id.clone();
    let lane = prepare_asset_lane_coordinator_v1(fixture.guest_input.clone()).unwrap();
    let projection = &lane.module_accepted.private_port.post_state;
    let mut post_state = pre_state.clone();
    post_state.height = fixture.occurrence.height;
    post_state.lane_roots[0].state_root = projection.state_root().unwrap();
    post_state.balances = projection.balances.clone();
    post_state.supplies = projection.supplies.clone();
    post_state.custody = projection.custody.clone();
    post_state.replay_state.push(ReplayStateV1 {
        replay_id: fixture.occurrence.replay_id().unwrap().as_str().to_owned(),
        occurrence_id,
    });
    AssetTransferRouteGuestInputV1 {
        schema: ASSET_TRANSFER_ROUTE_INPUT_SCHEMA_V1.to_owned(),
        lane_input: fixture.guest_input,
        profile: fixture.profile,
        lanes: fixture.lanes,
        coordinators: fixture.coordinators,
        routes: fixture.routes,
        policy_registry: fixture.policy_registry,
        asset_policy_registry: fixture.asset_policy_registry,
        occurrence: fixture.occurrence,
        pre_state,
        post_state,
    }
}
