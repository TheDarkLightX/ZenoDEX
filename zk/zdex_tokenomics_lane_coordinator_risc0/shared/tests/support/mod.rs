use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    build_zdex_tokenomics_burn_module_journal_v1, build_zdex_tokenomics_burn_private_port_v1,
    hash_global_v1, EvidenceStatusV1, LaneIdV1, LaneModuleReleaseV1, ReleaseStatusV1, RootV1,
    ZDEXAMMPurchaseJournalV1, ZDEXAmountBucketV1, ZDEXBurnRouteContextV1,
    ZDEXFeeDestinationAmountV1, ZDEXFeeDestinationV1, ZDEXFeeStateV1, ZDEXHyperdeflationPolicyV1,
    ZDEXPurchaseAndBurnCommandV1, ZDEXSupplyStateV1, ZDEXTokenomicsBurnCoordinatorContextV1,
    ZDEXTokenomicsLaneStateV1, GLOBAL_SETTLEMENT_ABI_V1, PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
};
use zenodex_zdex_hyperdeflation_burn_risc0_shared::{
    prepare_zdex_hyperdeflation_burn_v1, ZDEXHyperdeflationBurnGuestInputV1,
    ZDEX_HYPERDEFLATION_BURN_GUEST_INPUT_SCHEMA_V1,
};
use zenodex_zdex_tokenomics_lane_coordinator_risc0_shared::{
    ZDEXTokenomicsLaneCoordinatorGuestInputV1,
    ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1,
};

pub struct Fixture {
    #[allow(dead_code)]
    pub child_input: ZDEXHyperdeflationBurnGuestInputV1,
    pub coordinator_input: ZDEXTokenomicsLaneCoordinatorGuestInputV1,
}

pub fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "ZDEX tokenomics RISC0 test root",
        false,
    )
    .unwrap()
}

pub fn fixture(child_image_id: RootV1) -> Fixture {
    let module_release = shadow_module_release(child_image_id);
    let policy = ZDEXHyperdeflationPolicyV1 {
        asset_id: root(1),
        retained_numerator: 9,
        retained_denominator: 10,
        maximum_decimals: 64,
        maximum_decimal_step: 8,
    };
    let purchase_journal = ZDEXAMMPurchaseJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "tau-testnet".to_owned(),
        deployment_root: root(10),
        profile_root: root(11),
        writer_epoch: 7,
        route_release_id: root(2),
        command_occurrence_id: root(12),
        spot_module_release_id: root(13),
        issue_burn_policy_root: policy.policy_root().unwrap(),
        buyback_budget_occurrence_root: root(14),
        quote_asset_id: root(15),
        zdex_asset_id: policy.asset_id.clone(),
        quote_source_bucket_id: "protocol:buyback:quote".to_owned(),
        quote_pool_bucket_id: "pool:quote".to_owned(),
        zdex_pool_bucket_id: "pool:zdex".to_owned(),
        burn_bucket_id: "route:buyburn:source".to_owned(),
        quote_amount_in_atoms: 50,
        purchased_zdex_atoms: 100,
        quote_source_pre_atoms: 1000,
        quote_source_post_atoms: 950,
        quote_pool_pre_atoms: 200,
        quote_pool_post_atoms: 250,
        zdex_pool_pre_atoms: 600,
        zdex_pool_post_atoms: 500,
        burn_bucket_pre_atoms: 0,
        burn_bucket_post_atoms: 100,
        quote_owned_atoms: 1200,
        quote_supply_atoms: 2000,
        zdex_owned_atoms: 1000,
        zdex_supply_atoms: 1000,
        pre_spot_lane_root: root(16),
        post_spot_lane_root: root(17),
        effect_plan_root: RootV1::parse(
            "0x4be4052113d9a659b62fba88fa0385d814cb1ec8163b72182bae4b44bdd19a3c",
            "ZDEX purchase effect root",
            false,
        )
        .unwrap(),
    };
    let pre_state = ZDEXSupplyStateV1 {
        asset_id: policy.asset_id.clone(),
        policy_root: policy.policy_root().unwrap(),
        decimals: 8,
        precision_epoch: 0,
        live_supply_atoms: 1000,
        buckets: vec![
            ZDEXAmountBucketV1 {
                bucket_id: purchase_journal.burn_bucket_id.clone(),
                amount_atoms: 100,
            },
            ZDEXAmountBucketV1 {
                bucket_id: "wallet:alice".to_owned(),
                amount_atoms: 900,
            },
        ],
        burn_budget_epoch: 5,
        remaining_epoch_burn_cap_atoms: 100,
    };
    let purchase_occurrence_root = purchase_journal.journal_root().unwrap();
    let child_input = ZDEXHyperdeflationBurnGuestInputV1 {
        schema: ZDEX_HYPERDEFLATION_BURN_GUEST_INPUT_SCHEMA_V1.to_owned(),
        policy,
        pre_state: pre_state.clone(),
        route_context: ZDEXBurnRouteContextV1 {
            route_release_id: purchase_journal.route_release_id.clone(),
            policy_root: pre_state.policy_root.clone(),
            purchase_occurrence_root: purchase_occurrence_root.clone(),
            burn_source_bucket_id: purchase_journal.burn_bucket_id.clone(),
            purchased_zdex_atoms: 100,
            source_reserve_floor_atoms: 0,
            remaining_epoch_burn_cap_atoms: 100,
            route_safe_output_cap_atoms: 100,
            burn_budget_epoch: pre_state.burn_budget_epoch,
        },
        command: ZDEXPurchaseAndBurnCommandV1 {
            expected_pre_state_root: pre_state.state_root().unwrap(),
            expected_precision_epoch: pre_state.precision_epoch,
            expected_purchase_occurrence_root: purchase_occurrence_root,
            source_bucket_id: purchase_journal.burn_bucket_id.clone(),
            purchased_zdex_atoms: 100,
        },
        purchase_journal,
        tokenomics_module_release_id: module_release.release_id.clone(),
    };
    let burn = prepare_zdex_hyperdeflation_burn_v1(child_input.clone()).unwrap();
    let burn_journal = burn.projection.journal().clone();
    let module_effects = burn.projection.effects().clone();
    let private_port =
        build_zdex_tokenomics_burn_private_port_v1(&burn_journal, &module_effects).unwrap();
    let module_journal =
        build_zdex_tokenomics_burn_module_journal_v1(&burn_journal, &module_effects, &private_port)
            .unwrap();
    let context = ZDEXTokenomicsBurnCoordinatorContextV1 {
        schema: "zenodex/zdex-tokenomics-burn-coordinator/v1".to_owned(),
        chain_id: burn_journal.chain_id.clone(),
        deployment_root: burn_journal.deployment_root.clone(),
        profile_root: burn_journal.profile_root.clone(),
        writer_epoch: burn_journal.writer_epoch,
        coordinator_release_id: root(42),
        route_release_id: burn_journal.route_release_id.clone(),
        tokenomics_module_release_id: module_release.release_id.clone(),
        command_occurrence_id: burn_journal.command_occurrence_id.clone(),
        issue_burn_policy_root: burn_journal.issue_burn_policy_root.clone(),
    };
    let coordinator_input = ZDEXTokenomicsLaneCoordinatorGuestInputV1 {
        schema: ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1.to_owned(),
        module_release,
        context,
        module_journal,
        private_port,
        pre_state: lane_state(burn.projection.accepted().pre_state().clone()),
        post_state: lane_state(burn.projection.accepted().post_state().clone()),
        burn_journal,
        module_effects,
    };
    coordinator_input.validate().unwrap();
    Fixture {
        child_input,
        coordinator_input,
    }
}

pub fn rebind_release_id(release: &mut LaneModuleReleaseV1) {
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "lane_id": release.lane_id,
        "state_schema_root": release.state_schema_root,
        "command_variants": release.command_variants,
        "terminal_command_variants": release.terminal_command_variants,
        "guest_image_id": release.guest_image_id,
        "specification_root": release.specification_root,
        "source_root": release.source_root,
        "toolchain_root": release.toolchain_root,
        "terminal_coverage_root": release.terminal_coverage_root,
        "migration_compatibility_root": release.migration_compatibility_root,
        "max_cycles": release.max_cycles,
        "max_journal_bytes": release.max_journal_bytes,
    });
    release.release_id = hash_global_v1("global-lane-module-release-content-v1", &content).unwrap();
}

fn shadow_module_release(guest_image_id: RootV1) -> LaneModuleReleaseV1 {
    let mut release = LaneModuleReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        lane_id: LaneIdV1::ZDEX_TOKENOMICS,
        release_id: root(99),
        semantic_version: "1.0.0-shadow-risc0-test".to_owned(),
        state_schema_root: root(100),
        command_variants: vec![PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1.to_owned()],
        terminal_command_variants: vec![],
        guest_image_id,
        specification_root: root(102),
        source_root: root(103),
        toolchain_root: root(104),
        terminal_coverage_root: root(105),
        migration_compatibility_root: root(106),
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status: ReleaseStatusV1::SHADOW,
        accepts_new_objects: false,
        evidence_statuses: Vec::<EvidenceStatusV1>::new(),
    };
    rebind_release_id(&mut release);
    release.validate().unwrap();
    release
}

fn lane_state(supply_state: ZDEXSupplyStateV1) -> ZDEXTokenomicsLaneStateV1 {
    ZDEXTokenomicsLaneStateV1 {
        schema: "zenodex/zdex-tokenomics-lane-state/v1".to_owned(),
        supply_state,
        fee_allocation_states: vec![ZDEXFeeStateV1 {
            fee_asset_id: root(15),
            policy_root: root(30),
            fee_ingress_atoms: 1000,
            unallocated_reserve_atoms: 100,
            destination_balances: [
                ZDEXFeeDestinationV1::BUYBACK,
                ZDEXFeeDestinationV1::QUALIFIED_HOST_POOL,
                ZDEXFeeDestinationV1::TREASURY,
                ZDEXFeeDestinationV1::PROOF_REWARDS,
                ZDEXFeeDestinationV1::COVER_RESERVE,
                ZDEXFeeDestinationV1::LP_REBATES,
            ]
            .into_iter()
            .map(|destination| ZDEXFeeDestinationAmountV1 {
                destination,
                allocation_atoms: 0,
            })
            .collect(),
            owned_and_custodied_atoms: 2000,
            supply_atoms: 2000,
        }],
        staking_state_root: root(31),
        host_claims_state_root: root(32),
        treasury_claims_state_root: root(33),
        proof_rewards_state_root: root(34),
        cover_reserve_state_root: root(35),
        lp_rebates_state_root: root(36),
    }
}
