use zenodex_global_settlement_abi_v1::{
    candidate_zdex_fee_allocation_policy_v1, RootV1, ZDEXAmountBucketV1,
    ZDEXAtomicBuybackTokenomicsStateV1, ZDEXBuybackSpendPolicyV1, ZDEXBuybackSpendStateV1,
    ZDEXFeeDestinationAmountV1, ZDEXFeeStateV1, ZDEXSupplyStateV1, ZDEXTokenomicsLaneStateV1,
    ZDEX_ATOMIC_BUYBACK_TOKENOMICS_STATE_SCHEMA_V1, ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1,
    ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1, ZDEX_FEE_DESTINATIONS_V1,
    ZDEX_TOKENOMICS_LANE_STATE_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "atomic buyback state test root",
        false,
    )
    .unwrap()
}

fn fixture() -> ZDEXAtomicBuybackTokenomicsStateV1 {
    let fee_policy = candidate_zdex_fee_allocation_policy_v1();
    let spend_policy = ZDEXBuybackSpendPolicyV1 {
        schema: ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1.to_owned(),
        quote_asset_id: root(12),
        minimum_quote_spend_atoms: 1,
        per_command_quote_cap_atoms: 200,
        minimum_interval_blocks: 1,
    };
    ZDEXAtomicBuybackTokenomicsStateV1 {
        schema: ZDEX_ATOMIC_BUYBACK_TOKENOMICS_STATE_SCHEMA_V1.to_owned(),
        tokenomics: ZDEXTokenomicsLaneStateV1 {
            schema: ZDEX_TOKENOMICS_LANE_STATE_SCHEMA_V1.to_owned(),
            supply_state: ZDEXSupplyStateV1 {
                asset_id: root(13),
                policy_root: RootV1::parse(
                    "0xcb070529c2bf31b8ce80398afa34856354ed480282ec0dac0f28ac5d5423dafd",
                    "atomic buyback supply policy",
                    false,
                )
                .unwrap(),
                decimals: 8,
                precision_epoch: 0,
                live_supply_atoms: 1000,
                buckets: vec![ZDEXAmountBucketV1 {
                    bucket_id: "0x6534da5c7fe4a5941ea8385952e3b430c0b85e7630fba8d278ab8df1cdf469e1"
                        .to_owned(),
                    amount_atoms: 1000,
                }],
                burn_budget_epoch: 0,
                remaining_epoch_burn_cap_atoms: 500,
            },
            fee_allocation_states: vec![ZDEXFeeStateV1 {
                fee_asset_id: root(12),
                policy_root: fee_policy.policy_root().unwrap(),
                fee_ingress_atoms: 125,
                unallocated_reserve_atoms: 0,
                destination_balances: ZDEX_FEE_DESTINATIONS_V1
                    .iter()
                    .copied()
                    .enumerate()
                    .map(|(index, destination)| ZDEXFeeDestinationAmountV1 {
                        destination,
                        allocation_atoms: if index == 0 { 100 } else { 0 },
                    })
                    .collect(),
                owned_and_custodied_atoms: 10_000,
                supply_atoms: 10_000,
            }],
            staking_state_root: root(800),
            host_claims_state_root: root(801),
            treasury_claims_state_root: root(802),
            proof_rewards_state_root: root(803),
            cover_reserve_state_root: root(804),
            lp_rebates_state_root: root(805),
        },
        buyback_spend_states: vec![ZDEXBuybackSpendStateV1 {
            schema: ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1.to_owned(),
            quote_asset_id: root(12),
            policy_root: spend_policy.policy_root().unwrap(),
            last_execution_height: None,
        }],
    }
}

#[test]
fn complete_state_matches_python_canonical_root() {
    let state = fixture();
    assert_eq!(
        state.state_root().unwrap().as_str(),
        "0xbe4d33885b016577761152ef3765ea7998e4a54a37c6d129273970bda6d92666"
    );
}

#[test]
fn cadence_registry_must_exactly_cover_fee_assets() {
    let mut state = fixture();
    state.buyback_spend_states.clear();

    assert!(state.validate().is_err());
}

#[test]
fn post_state_replacement_is_exact_and_rejects_unknown_assets() {
    let state = fixture();
    let mut fee_post = state.tokenomics.fee_allocation_states[0].clone();
    fee_post.destination_balances[0].allocation_atoms = 14;
    let mut cadence_post = state.buyback_spend_states[0].clone();
    cadence_post.last_execution_height = Some(11);

    let post = state.with_buyback_result(&fee_post, &cadence_post).unwrap();
    assert_eq!(post.tokenomics.fee_allocation_states[0], fee_post);
    assert_eq!(post.buyback_spend_states[0], cadence_post);

    let mut foreign = fee_post;
    foreign.fee_asset_id = root(99);
    assert!(state.with_buyback_result(&foreign, &cadence_post).is_err());
}
