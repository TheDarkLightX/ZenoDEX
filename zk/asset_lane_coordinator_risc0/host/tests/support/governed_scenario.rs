use zenodex_asset_lane_coordinator_risc0_shared::{
    AssetLaneCoordinatorGuestInputV1, ASSET_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1,
};
use zenodex_global_settlement_abi_v1::{
    canonical_economic_command_body_bytes_v1, AssetLaneCoordinatorContextV1,
    AssetLaneModuleCompatibilityV1, AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1,
    AssetTransferLaneModuleInputV1, AssetTransferPolicyV1, AssetTransferStateV1, EconomicAmountV1,
    EconomicCommandOccurrenceV1, LaneIdV1, RootV1, ASSET_LANE_COORDINATOR_SCHEMA_V1,
    ASSET_TRANSFER_COMMAND_KIND_V1, ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1, GLOBAL_SETTLEMENT_ABI_V1,
};

use super::authenticated_command::authenticate_occurrence_v1;
use super::governed_registries::{release_aware_registries_v1, ReleaseAwareRegistriesV1};
use super::{root, ReleaseAwareAssetLaneFixtureV1};

/// Module state carrying exactly the governed policy rows.
fn asset_state(
    module_release_id: RootV1,
    policies: Vec<AssetTransferPolicyV1>,
) -> AssetTransferStateV1 {
    AssetTransferStateV1 {
        schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        module_release_id,
        policies,
        balances: vec![
            EconomicAmountV1 {
                owner: "alice".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: "accounts".to_owned(),
                amount_atoms: 100,
            },
            EconomicAmountV1 {
                owner: "bob".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: "accounts".to_owned(),
                amount_atoms: 10,
            },
            EconomicAmountV1 {
                owner: "treasury".to_owned(),
                asset: "USD".to_owned(),
                custody_domain: "accounts".to_owned(),
                amount_atoms: 5,
            },
        ],
        supplies: vec![AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: 115,
        }],
    }
}

fn occurrence(
    registries: &ReleaseAwareRegistriesV1,
    pre_state: &AssetTransferStateV1,
    command: &AssetTransferCommandV1,
) -> EconomicCommandOccurrenceV1 {
    let route = registries
        .routes
        .route_for_command(ASSET_TRANSFER_COMMAND_KIND_V1, None)
        .unwrap();
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-real-release-aware-asset-lane-proof".to_owned(),
        deployment_root: root(1),
        height: 11,
        tx_index: 2,
        op_index: 3,
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        command_body_hash: command.command_body_hash().unwrap(),
        route_release_id: route.route_release_id.clone(),
        subject_id: "alice".to_owned(),
        grant_root: root(5),
        nonce: 9,
        profile_root: registries.profile.profile_id.clone(),
        pre_state_root: pre_state.state_root().unwrap(),
        consumed_object_ids: vec![],
    }
}

fn command() -> AssetTransferCommandV1 {
    AssetTransferCommandV1 {
        command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
        asset: "USD".to_owned(),
        sender: "alice".to_owned(),
        recipient: "bob".to_owned(),
        amount_atoms: 30,
        max_fee_atoms: 2,
    }
}

fn module_input(
    registries: &ReleaseAwareRegistriesV1,
    occurrence: &EconomicCommandOccurrenceV1,
    pre_state: AssetTransferStateV1,
    command: AssetTransferCommandV1,
    module_release_id: RootV1,
) -> AssetTransferLaneModuleInputV1 {
    AssetTransferLaneModuleInputV1 {
        schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: AssetTransferContextV1 {
            chain_id: occurrence.chain_id.clone(),
            deployment_root: occurrence.deployment_root.clone(),
            profile_root: registries.profile.profile_id.clone(),
            writer_epoch: registries.profile.authority_epoch,
            module_release_id,
            command_occurrence_id: occurrence.occurrence_id().unwrap(),
            subject_id: occurrence.subject_id.clone(),
            grant_root: occurrence.grant_root.clone(),
        },
        pre_state,
        command,
        asset_policy_registry_root: registries
            .asset_policy_registry
            .asset_policy_root()
            .unwrap(),
        fee_policy_registry_root: registries.asset_policy_registry.fee_policy_root().unwrap(),
        custody: vec![],
    }
}

fn coordinator_context(
    registries: &ReleaseAwareRegistriesV1,
    occurrence: &EconomicCommandOccurrenceV1,
    module_input: &AssetTransferLaneModuleInputV1,
    module_release_id: RootV1,
) -> AssetLaneCoordinatorContextV1 {
    let release = registries
        .coordinators
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .unwrap();
    AssetLaneCoordinatorContextV1 {
        schema: ASSET_LANE_COORDINATOR_SCHEMA_V1.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: registries.profile.profile_id.clone(),
        writer_epoch: registries.profile.authority_epoch,
        coordinator_release_id: release.coordinator_release_id.clone(),
        command_occurrence_id: occurrence.occurrence_id().unwrap(),
        asset_policy_registry_root: module_input.asset_policy_registry_root.clone(),
        fee_policy_registry_root: module_input.fee_policy_registry_root.clone(),
        compatible_modules: vec![AssetLaneModuleCompatibilityV1 {
            module_release_id,
            module_schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        }],
    }
}

pub fn release_aware_asset_lane_fixture_v1(
    module_image: RootV1,
    coordinator_image: RootV1,
) -> ReleaseAwareAssetLaneFixtureV1 {
    let registries = release_aware_registries_v1(&module_image, &coordinator_image);
    let module_release_id = registries
        .lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .unwrap()
        .release_id
        .clone();
    let pre_state = asset_state(
        module_release_id.clone(),
        registries.asset_policy_registry.policies.clone(),
    );
    let command = command();
    let occurrence = occurrence(&registries, &pre_state, &command);
    let authenticated_command = authenticate_occurrence_v1(
        &registries.profile,
        &registries.routes,
        &occurrence,
        canonical_economic_command_body_bytes_v1(ASSET_TRANSFER_COMMAND_KIND_V1, &command).unwrap(),
        &registries.policy_registry,
    );
    let module_input = module_input(
        &registries,
        &occurrence,
        pre_state,
        command,
        module_release_id.clone(),
    );
    let coordinator_context =
        coordinator_context(&registries, &occurrence, &module_input, module_release_id);
    ReleaseAwareAssetLaneFixtureV1 {
        profile: registries.profile,
        lanes: registries.lanes,
        coordinators: registries.coordinators,
        routes: registries.routes,
        policy_registry: registries.policy_registry,
        asset_policy_registry: registries.asset_policy_registry,
        occurrence,
        authenticated_command,
        guest_input: AssetLaneCoordinatorGuestInputV1 {
            schema: ASSET_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1.to_owned(),
            module_input,
            coordinator_context,
        },
    }
}
