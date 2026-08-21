use zenodex_global_settlement_abi_v1::{
    refine_zdex_burn_leaf_v1, transition_zdex_purchase_and_burn_v1, RootV1,
    ZDEXAMMPurchaseJournalV1, ZDEXAmountBucketV1, ZDEXBurnRouteContextV1,
    ZDEXHyperdeflationPolicyV1, ZDEXPurchaseAndBurnCommandV1, ZDEXPurchaseAndBurnResultV1,
    ZDEXSupplyStateV1, GLOBAL_SETTLEMENT_ABI_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "ZDEX refinement test root",
        false,
    )
    .unwrap()
}

fn root_hex(value: &str) -> RootV1 {
    RootV1::parse(value, "ZDEX refinement golden root", false).unwrap()
}

fn policy() -> ZDEXHyperdeflationPolicyV1 {
    ZDEXHyperdeflationPolicyV1 {
        asset_id: root(1),
        retained_numerator: 9,
        retained_denominator: 10,
        maximum_decimals: 64,
        maximum_decimal_step: 8,
    }
}

fn purchase(policy: &ZDEXHyperdeflationPolicyV1) -> ZDEXAMMPurchaseJournalV1 {
    ZDEXAMMPurchaseJournalV1 {
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
    }
}

fn accepted(
    policy: &ZDEXHyperdeflationPolicyV1,
    purchase: &ZDEXAMMPurchaseJournalV1,
    source_atoms: u128,
    burned_atoms: u128,
    checked_supply_atoms: u128,
) -> zenodex_global_settlement_abi_v1::ZDEXPurchaseAndBurnAcceptedV1 {
    accepted_with_route_caps(
        policy,
        purchase,
        source_atoms,
        burned_atoms,
        checked_supply_atoms,
        u128::MAX,
        u128::MAX,
    )
}

#[allow(clippy::too_many_arguments)]
fn accepted_with_route_caps(
    policy: &ZDEXHyperdeflationPolicyV1,
    purchase: &ZDEXAMMPurchaseJournalV1,
    source_atoms: u128,
    burned_atoms: u128,
    checked_supply_atoms: u128,
    route_epoch_cap_atoms: u128,
    route_safe_output_cap_atoms: u128,
) -> zenodex_global_settlement_abi_v1::ZDEXPurchaseAndBurnAcceptedV1 {
    let state = ZDEXSupplyStateV1 {
        asset_id: policy.asset_id.clone(),
        policy_root: policy.policy_root().unwrap(),
        decimals: 8,
        precision_epoch: 0,
        live_supply_atoms: checked_supply_atoms,
        buckets: vec![
            ZDEXAmountBucketV1 {
                bucket_id: purchase.burn_bucket_id.clone(),
                amount_atoms: source_atoms,
            },
            ZDEXAmountBucketV1 {
                bucket_id: "wallet:alice".to_owned(),
                amount_atoms: checked_supply_atoms - source_atoms,
            },
        ],
        burn_budget_epoch: 5,
        remaining_epoch_burn_cap_atoms: 100,
    };
    let context = ZDEXBurnRouteContextV1 {
        route_release_id: purchase.route_release_id.clone(),
        policy_root: policy.policy_root().unwrap(),
        purchase_occurrence_root: purchase.journal_root().unwrap(),
        burn_source_bucket_id: purchase.burn_bucket_id.clone(),
        purchased_zdex_atoms: burned_atoms,
        source_reserve_floor_atoms: 0,
        remaining_epoch_burn_cap_atoms: route_epoch_cap_atoms,
        route_safe_output_cap_atoms,
        burn_budget_epoch: state.burn_budget_epoch,
    };
    let command = ZDEXPurchaseAndBurnCommandV1 {
        expected_pre_state_root: state.state_root().unwrap(),
        expected_precision_epoch: state.precision_epoch,
        expected_purchase_occurrence_root: purchase.journal_root().unwrap(),
        source_bucket_id: purchase.burn_bucket_id.clone(),
        purchased_zdex_atoms: burned_atoms,
    };
    let result = transition_zdex_purchase_and_burn_v1(policy, &state, &context, &command).unwrap();
    let ZDEXPurchaseAndBurnResultV1::Accepted(accepted) = result else {
        panic!("coherent refinement fixture must accept")
    };
    *accepted
}

#[test]
fn refinement_derives_python_parity_journal_and_effects() {
    // Arrange
    let policy = policy();
    let purchase = purchase(&policy);
    let accepted = accepted(&policy, &purchase, 100, 100, 1000);

    // Act
    let projection = refine_zdex_burn_leaf_v1(&accepted, &purchase, &root(20)).unwrap();

    // Assert
    assert_eq!(
        purchase.journal_root().unwrap().as_str(),
        "0xc7bc06f6e2475adba501f493450ca57fcf24a738e179f7ba11079281a9144dc8"
    );
    assert_eq!(
        projection.journal().journal_root().unwrap().as_str(),
        "0xe6c3831c5f376c3436ad48a94132ffa00a4775042c8bc4700df11ca1e1fa515b"
    );
    assert_eq!(
        projection.effects().effect_plan_root().unwrap().as_str(),
        "0x6853ced9af428e73b826a9f2c356a5966c5cedd300bc28ec1258d10402ef2dc2"
    );
    assert_eq!(
        projection.journal().route_context_root.as_str(),
        "0x5512d60e46a0728396903fb766dd516a6865620bd0373e79a704912d3c38a451"
    );
    assert_eq!(
        projection.journal().pre_tokenomics_burn_substate_root,
        accepted.pre_state().state_root().unwrap()
    );
    assert_eq!(
        projection.journal().post_tokenomics_burn_substate_root,
        accepted.post_state().state_root().unwrap()
    );
    assert_eq!(projection.journal().burned_zdex_atoms, 100);
    assert!(projection.effects().lane_writes.is_empty());
    assert!(projection.effects().external_outbox_enqueue.is_empty());
}

#[test]
fn nonlimiting_route_cap_substitution_changes_the_public_burn_journal() {
    // Arrange: each route context admits the same state transition and amount.
    let policy = policy();
    let purchase = purchase(&policy);
    let unbounded =
        accepted_with_route_caps(&policy, &purchase, 100, 100, 1000, u128::MAX, u128::MAX);
    let bounded = accepted_with_route_caps(&policy, &purchase, 100, 100, 1000, 1000, 1000);

    // Act
    let unbounded_projection = refine_zdex_burn_leaf_v1(&unbounded, &purchase, &root(20)).unwrap();
    let bounded_projection = refine_zdex_burn_leaf_v1(&bounded, &purchase, &root(20)).unwrap();

    // Assert: acceptance-affecting policy inputs remain publicly distinguishable.
    assert_ne!(
        unbounded_projection.journal().journal_root().unwrap(),
        bounded_projection.journal().journal_root().unwrap()
    );
}

#[test]
fn refinement_rejects_purchase_effect_root_substitution() {
    let policy = policy();
    let mut purchase = purchase(&policy);
    let accepted = accepted(&policy, &purchase, 100, 100, 1000);
    purchase.effect_plan_root = root(99);

    assert!(refine_zdex_burn_leaf_v1(&accepted, &purchase, &root(20)).is_err());
}

#[test]
fn refinement_rejects_route_policy_asset_bucket_and_totals_substitutions() {
    let policy = policy();
    let purchase = purchase(&policy);
    let accepted = accepted(&policy, &purchase, 100, 100, 1000);
    let mut substitutions = vec![];

    let mut candidate = purchase.clone();
    candidate.route_release_id = root(99);
    substitutions.push(candidate);
    let mut candidate = purchase.clone();
    candidate.issue_burn_policy_root = root(99);
    substitutions.push(candidate);
    let mut candidate = purchase.clone();
    candidate.zdex_asset_id = root(99);
    substitutions.push(candidate);
    let mut candidate = purchase.clone();
    candidate.burn_bucket_id = "route:other-burn-source".to_owned();
    substitutions.push(candidate);
    let mut candidate = purchase.clone();
    candidate.zdex_owned_atoms = 1100;
    substitutions.push(candidate);
    let mut candidate = purchase.clone();
    candidate.zdex_supply_atoms = 1100;
    substitutions.push(candidate);

    for candidate in substitutions {
        assert!(refine_zdex_burn_leaf_v1(&accepted, &candidate, &root(20)).is_err());
    }
}

#[test]
fn refinement_rejects_partial_transient_bucket_drain() {
    let policy = policy();
    let purchase = purchase(&policy);
    let accepted = accepted(&policy, &purchase, 150, 100, 1000);

    assert!(refine_zdex_burn_leaf_v1(&accepted, &purchase, &root(20)).is_err());
}

#[test]
fn refinement_rejects_coherent_purchase_amount_substitution() {
    let policy = policy();
    let mut purchase = purchase(&policy);
    purchase.purchased_zdex_atoms = 99;
    purchase.zdex_pool_post_atoms = 501;
    purchase.burn_bucket_post_atoms = 99;
    purchase.effect_plan_root =
        root_hex("0xd84de45dd47e7671a23b1e19a9bcadccf93562ce5c08c81e9cfe464718557e42");
    let accepted = accepted(&policy, &purchase, 100, 100, 1000);

    assert!(refine_zdex_burn_leaf_v1(&accepted, &purchase, &root(20)).is_err());
}

#[test]
fn refinement_rejects_self_consistent_policy_asset_and_total_substitutions() {
    let policy = policy();
    let purchase = purchase(&policy);

    let mut policy_substitution = purchase.clone();
    policy_substitution.issue_burn_policy_root = root(99);
    let policy_accepted = accepted(&policy, &policy_substitution, 100, 100, 1000);

    let mut asset_substitution = purchase.clone();
    asset_substitution.zdex_asset_id = root(99);
    asset_substitution.effect_plan_root =
        root_hex("0x7aae069342bd96623c2fb870848a45f3d4904a663af2560b6659c1ec81374c24");
    let asset_accepted = accepted(&policy, &asset_substitution, 100, 100, 1000);

    let mut total_substitution = purchase;
    total_substitution.zdex_owned_atoms = 1100;
    total_substitution.zdex_supply_atoms = 1100;
    total_substitution.effect_plan_root =
        root_hex("0xc8683d4ba8a08f5a76255cfbe5d085f95cd3b78f569c4934a7a42d3704879aaf");
    let total_accepted = accepted(&policy, &total_substitution, 100, 100, 1000);

    for (accepted, candidate) in [
        (policy_accepted, policy_substitution),
        (asset_accepted, asset_substitution),
        (total_accepted, total_substitution),
    ] {
        assert!(refine_zdex_burn_leaf_v1(&accepted, &candidate, &root(20)).is_err());
    }
}
