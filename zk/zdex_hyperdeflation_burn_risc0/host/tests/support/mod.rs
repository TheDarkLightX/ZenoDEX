use zenodex_global_settlement_abi_v1::{
    RootV1, ZDEXAMMPurchaseJournalV1, ZDEXAmountBucketV1, ZDEXBurnRouteContextV1,
    ZDEXHyperdeflationPolicyV1, ZDEXPurchaseAndBurnCommandV1, ZDEXSupplyStateV1,
    GLOBAL_SETTLEMENT_ABI_V1,
};
use zenodex_zdex_hyperdeflation_burn_risc0_shared::{
    ZDEXHyperdeflationBurnGuestInputV1, ZDEX_HYPERDEFLATION_BURN_GUEST_INPUT_SCHEMA_V1,
};

pub fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "ZDEX hyperdeflation burn host test root",
        false,
    )
    .unwrap()
}

fn root_hex(value: &str) -> RootV1 {
    RootV1::parse(value, "ZDEX hyperdeflation burn host golden root", false).unwrap()
}

pub fn guest_input(source_atoms: u128) -> ZDEXHyperdeflationBurnGuestInputV1 {
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
        effect_plan_root: root_hex(
            "0x4be4052113d9a659b62fba88fa0385d814cb1ec8163b72182bae4b44bdd19a3c",
        ),
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
                amount_atoms: source_atoms,
            },
            ZDEXAmountBucketV1 {
                bucket_id: "wallet:alice".to_owned(),
                amount_atoms: 1000 - source_atoms,
            },
        ],
        burn_budget_epoch: 5,
        remaining_epoch_burn_cap_atoms: 100,
    };
    let purchase_occurrence_root = purchase_journal.journal_root().unwrap();
    ZDEXHyperdeflationBurnGuestInputV1 {
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
            remaining_epoch_burn_cap_atoms: u128::MAX,
            route_safe_output_cap_atoms: u128::MAX,
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
        tokenomics_module_release_id: root(20),
    }
}
