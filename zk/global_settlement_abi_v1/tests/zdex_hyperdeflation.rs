use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    compute_zdex_burn_capacity_v1, retained_supply_atoms_v1, transition_zdex_precision_rescale_v1,
    transition_zdex_purchase_and_burn_v1, RootV1, ZDEXAmountBucketV1, ZDEXBurnRejectCodeV1,
    ZDEXBurnRouteContextV1, ZDEXHyperdeflationPolicyV1, ZDEXPrecisionRejectCodeV1,
    ZDEXPrecisionRescaleCommandV1, ZDEXPrecisionRescaleResultV1, ZDEXPurchaseAndBurnCommandV1,
    ZDEXPurchaseAndBurnResultV1, ZDEXSupplyStateV1, MAX_DECIMAL_SCALE_STEP_V1,
    MAX_ZDEX_PROJECTION_BUCKETS_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "ZDEX hyperdeflation test root",
        false,
    )
    .unwrap()
}

fn policy(numerator: u64, denominator: u64) -> ZDEXHyperdeflationPolicyV1 {
    ZDEXHyperdeflationPolicyV1 {
        asset_id: root(1),
        retained_numerator: numerator,
        retained_denominator: denominator,
        maximum_decimals: 64,
        maximum_decimal_step: 8,
    }
}

fn state(
    policy: &ZDEXHyperdeflationPolicyV1,
    source_atoms: u128,
    holder_atoms: u128,
) -> ZDEXSupplyStateV1 {
    let mut buckets = vec![ZDEXAmountBucketV1 {
        bucket_id: "route:buyburn:source".to_owned(),
        amount_atoms: source_atoms,
    }];
    if holder_atoms > 0 {
        buckets.push(ZDEXAmountBucketV1 {
            bucket_id: "wallet:alice".to_owned(),
            amount_atoms: holder_atoms,
        });
    }
    ZDEXSupplyStateV1 {
        asset_id: policy.asset_id.clone(),
        policy_root: policy.policy_root().unwrap(),
        decimals: 8,
        precision_epoch: 0,
        live_supply_atoms: source_atoms + holder_atoms,
        buckets,
        burn_budget_epoch: 0,
        remaining_epoch_burn_cap_atoms: source_atoms + holder_atoms,
    }
}

fn context(policy: &ZDEXHyperdeflationPolicyV1, purchased_atoms: u128) -> ZDEXBurnRouteContextV1 {
    ZDEXBurnRouteContextV1 {
        route_release_id: root(2),
        policy_root: policy.policy_root().unwrap(),
        purchase_occurrence_root: root(3),
        burn_source_bucket_id: "route:buyburn:source".to_owned(),
        purchased_zdex_atoms: purchased_atoms,
        source_reserve_floor_atoms: 0,
        remaining_epoch_burn_cap_atoms: u128::MAX,
        route_safe_output_cap_atoms: u128::MAX,
        burn_budget_epoch: 0,
    }
}

fn burn_command(state: &ZDEXSupplyStateV1, purchased_atoms: u128) -> ZDEXPurchaseAndBurnCommandV1 {
    ZDEXPurchaseAndBurnCommandV1 {
        expected_pre_state_root: state.state_root().unwrap(),
        expected_precision_epoch: state.precision_epoch,
        expected_purchase_occurrence_root: root(3),
        source_bucket_id: "route:buyburn:source".to_owned(),
        purchased_zdex_atoms: purchased_atoms,
    }
}

fn assert_burn_reject(
    policy: &ZDEXHyperdeflationPolicyV1,
    state: &ZDEXSupplyStateV1,
    context: &ZDEXBurnRouteContextV1,
    command: &ZDEXPurchaseAndBurnCommandV1,
    expected: ZDEXBurnRejectCodeV1,
) {
    let result = transition_zdex_purchase_and_burn_v1(policy, state, context, command).unwrap();
    let ZDEXPurchaseAndBurnResultV1::Rejected(rejected) = result else {
        panic!("invalid burn must reject")
    };
    assert_eq!(rejected.code(), expected);
    assert_eq!(rejected.pre_state(), rejected.post_state());
    assert!(rejected.effects().is_empty());
}

fn assert_precision_reject(
    policy: &ZDEXHyperdeflationPolicyV1,
    state: &ZDEXSupplyStateV1,
    command: &ZDEXPrecisionRescaleCommandV1,
    expected: ZDEXPrecisionRejectCodeV1,
) {
    let result = transition_zdex_precision_rescale_v1(policy, state, command).unwrap();
    let ZDEXPrecisionRescaleResultV1::Rejected(rejected) = result else {
        panic!("invalid precision rescale must reject")
    };
    assert_eq!(rejected.code(), expected);
    assert_eq!(rejected.pre_state(), rejected.post_state());
    assert!(rejected.effects().is_empty());
}

#[test]
fn rust_matches_python_burn_roots_and_exact_capacity() {
    // Arrange
    let policy = policy(9, 10);
    let state = state(&policy, 600, 400);

    // Act
    let result = transition_zdex_purchase_and_burn_v1(
        &policy,
        &state,
        &context(&policy, 100),
        &burn_command(&state, 100),
    )
    .unwrap();

    // Assert
    let ZDEXPurchaseAndBurnResultV1::Accepted(accepted) = result else {
        panic!("exact-capacity burn must accept")
    };
    assert_eq!(
        policy.policy_root().unwrap().as_str(),
        "0x12748f215bca2c960007fe74b5de2236129f5c285bbcd9b98c07736839ba46c6"
    );
    assert_eq!(
        state.state_root().unwrap().as_str(),
        "0xeee0aa653a5af6aa7dd08c8f0d45d6c9184dabbc3901b60fba465444a4dbc305"
    );
    assert_eq!(
        accepted.post_state().state_root().unwrap().as_str(),
        "0x687eacda4d4e96e65bcefd01b9665a9417d661148462fd50fd40b974a2097119"
    );
    assert_eq!(accepted.capacity().retained_supply_atoms, 900);
    assert_eq!(accepted.capacity().maximum_burn_atoms, 100);
    assert_eq!(accepted.effect().source_debit_atoms, 100);
    assert_eq!(accepted.effect().authorized_burn_atoms, 100);
    assert_eq!(accepted.effect().authorized_issue_atoms, 0);
}

#[test]
fn ceil_retention_and_widened_u128_u64_arithmetic_match_independent_oracles() {
    let half = policy(1, 2);
    assert_eq!(retained_supply_atoms_v1(5, &half).unwrap(), 3);
    let boundary = ZDEXHyperdeflationPolicyV1 {
        maximum_decimals: u64::MAX,
        maximum_decimal_step: MAX_DECIMAL_SCALE_STEP_V1,
        ..policy(u64::MAX - 1, u64::MAX)
    };
    let retained = retained_supply_atoms_v1(u128::MAX, &boundary).unwrap();
    let quotient = u128::MAX / u128::from(u64::MAX);
    let remainder = u128::MAX % u128::from(u64::MAX);
    let independent = quotient * u128::from(u64::MAX - 1)
        + (remainder * u128::from(u64::MAX - 1)).div_ceil(u128::from(u64::MAX));
    assert_eq!(retained, independent);
    assert!((1..=u128::MAX).contains(&retained));
    let boundary_state = ZDEXSupplyStateV1 {
        decimals: u64::MAX,
        precision_epoch: u64::MAX,
        burn_budget_epoch: u64::MAX,
        remaining_epoch_burn_cap_atoms: u128::MAX,
        ..state(&boundary, u128::MAX, 0)
    };
    assert_eq!(
        boundary.policy_root().unwrap().as_str(),
        "0xad1bc096a89e8ba0327640f77f2ae0946db17b4fdb25f99fa2ed217f073c6536"
    );
    assert_eq!(
        boundary_state.state_root().unwrap().as_str(),
        "0x9083fedb16da97f36e8c097322bfced6519e2dd4419607f1134f9f93cc2054ed"
    );
}

#[test]
fn exhaustive_small_domain_preserves_positive_supply_and_ceil_oracle() {
    for supply_atoms in 1..=40_u128 {
        for denominator in 2..10_u64 {
            for numerator in 1..denominator {
                let policy = policy(numerator, denominator);
                let state = state(&policy, supply_atoms, 0);
                let retained_oracle =
                    (u128::from(numerator) * supply_atoms).div_ceil(u128::from(denominator));
                let capacity = compute_zdex_burn_capacity_v1(
                    &policy,
                    &state,
                    &context(&policy, 1),
                    "route:buyburn:source",
                )
                .unwrap()
                .unwrap();
                assert_eq!(capacity.retained_supply_atoms, retained_oracle);
                assert_eq!(capacity.maximum_burn_atoms, supply_atoms - retained_oracle);
                if capacity.maximum_burn_atoms == 0 {
                    continue;
                }
                let burn = capacity.maximum_burn_atoms;
                let result = transition_zdex_purchase_and_burn_v1(
                    &policy,
                    &state,
                    &context(&policy, burn),
                    &burn_command(&state, burn),
                )
                .unwrap();
                let ZDEXPurchaseAndBurnResultV1::Accepted(accepted) = result else {
                    panic!("bounded exact-capacity burn must accept")
                };
                assert_eq!(accepted.post_state().live_supply_atoms, retained_oracle);
                assert!(accepted.post_state().live_supply_atoms > 0);
            }
        }
    }
}

#[test]
fn sequential_burns_consume_committed_epoch_capacity() {
    let policy = policy(1, 2);
    let mut state = state(&policy, 10, 0);
    state.remaining_epoch_burn_cap_atoms = 5;
    let mut first_context = context(&policy, 3);
    first_context.remaining_epoch_burn_cap_atoms = 5;
    let first = transition_zdex_purchase_and_burn_v1(
        &policy,
        &state,
        &first_context,
        &burn_command(&state, 3),
    )
    .unwrap();
    let ZDEXPurchaseAndBurnResultV1::Accepted(first) = first else {
        panic!("first bounded burn must accept")
    };
    assert_eq!(first.post_state().remaining_epoch_burn_cap_atoms, 2);

    let mut second_context = first_context;
    second_context.purchase_occurrence_root = root(4);
    let mut second_command = burn_command(first.post_state(), 3);
    second_command.expected_purchase_occurrence_root = root(4);
    assert_burn_reject(
        &policy,
        first.post_state(),
        &second_context,
        &second_command,
        ZDEXBurnRejectCodeV1::PURCHASE_EXCEEDS_BURN_CAPACITY,
    );
}

#[test]
fn burn_rejects_state_outside_policy_precision_envelope() {
    let policy = ZDEXHyperdeflationPolicyV1 {
        maximum_decimals: 8,
        ..policy(1, 2)
    };
    let mut state = state(&policy, 10, 0);
    state.decimals = 9;
    assert_burn_reject(
        &policy,
        &state,
        &context(&policy, 1),
        &burn_command(&state, 1),
        ZDEXBurnRejectCodeV1::STATE_OUTSIDE_POLICY,
    );
}

#[test]
fn burn_rejections_are_typed_exact_noops_with_precedence() {
    let policy = policy(1, 2);
    let state = state(&policy, 10, 0);
    let cases = [
        (
            ZDEXPurchaseAndBurnCommandV1 {
                purchased_zdex_atoms: 0,
                ..burn_command(&state, 1)
            },
            context(&policy, 1),
            ZDEXBurnRejectCodeV1::ZERO_PURCHASE,
        ),
        (
            ZDEXPurchaseAndBurnCommandV1 {
                expected_purchase_occurrence_root: root(99),
                ..burn_command(&state, 1)
            },
            context(&policy, 1),
            ZDEXBurnRejectCodeV1::PURCHASE_BINDING_MISMATCH,
        ),
        (
            burn_command(&state, 6),
            context(&policy, 6),
            ZDEXBurnRejectCodeV1::PURCHASE_EXCEEDS_BURN_CAPACITY,
        ),
    ];
    for (command, context, code) in cases {
        let result =
            transition_zdex_purchase_and_burn_v1(&policy, &state, &context, &command).unwrap();
        let ZDEXPurchaseAndBurnResultV1::Rejected(rejected) = result else {
            panic!("invalid burn must reject")
        };
        assert_eq!(rejected.code(), code);
        assert_eq!(rejected.pre_state(), rejected.post_state());
        assert!(rejected.effects().is_empty());
    }
}

#[test]
fn every_burn_reject_code_has_exact_noop_evidence() {
    let state_policy = policy(9, 10);
    let base_state = state(&state_policy, 10, 0);

    let caller_policy = policy(1, 2);
    assert_burn_reject(
        &caller_policy,
        &base_state,
        &context(&caller_policy, 1),
        &burn_command(&base_state, 1),
        ZDEXBurnRejectCodeV1::POLICY_MISMATCH,
    );

    let outside_policy_state = ZDEXSupplyStateV1 {
        decimals: 65,
        ..base_state.clone()
    };
    assert_burn_reject(
        &state_policy,
        &outside_policy_state,
        &context(&state_policy, 1),
        &burn_command(&outside_policy_state, 1),
        ZDEXBurnRejectCodeV1::STATE_OUTSIDE_POLICY,
    );

    let mut command = burn_command(&base_state, 1);
    command.expected_pre_state_root = root(99);
    assert_burn_reject(
        &state_policy,
        &base_state,
        &context(&state_policy, 1),
        &command,
        ZDEXBurnRejectCodeV1::STALE_STATE,
    );
    let mut command = burn_command(&base_state, 1);
    command.expected_precision_epoch = 1;
    assert_burn_reject(
        &state_policy,
        &base_state,
        &context(&state_policy, 1),
        &command,
        ZDEXBurnRejectCodeV1::PRECISION_EPOCH_MISMATCH,
    );
    let mut wrong_budget_context = context(&state_policy, 1);
    wrong_budget_context.burn_budget_epoch = 1;
    assert_burn_reject(
        &state_policy,
        &base_state,
        &wrong_budget_context,
        &burn_command(&base_state, 1),
        ZDEXBurnRejectCodeV1::BURN_BUDGET_EPOCH_MISMATCH,
    );
    let mut command = burn_command(&base_state, 1);
    command.expected_purchase_occurrence_root = root(99);
    assert_burn_reject(
        &state_policy,
        &base_state,
        &context(&state_policy, 1),
        &command,
        ZDEXBurnRejectCodeV1::PURCHASE_BINDING_MISMATCH,
    );
    let mut unknown_context = context(&state_policy, 1);
    unknown_context.burn_source_bucket_id = "pool:unknown".to_owned();
    let mut unknown_command = burn_command(&base_state, 1);
    unknown_command.source_bucket_id = "pool:unknown".to_owned();
    assert_burn_reject(
        &state_policy,
        &base_state,
        &unknown_context,
        &unknown_command,
        ZDEXBurnRejectCodeV1::SOURCE_BUCKET_UNKNOWN,
    );
    let mut command = burn_command(&base_state, 1);
    command.purchased_zdex_atoms = 0;
    assert_burn_reject(
        &state_policy,
        &base_state,
        &context(&state_policy, 1),
        &command,
        ZDEXBurnRejectCodeV1::ZERO_PURCHASE,
    );

    let half = policy(1, 2);
    let one_atom = state(&half, 1, 0);
    assert_burn_reject(
        &half,
        &one_atom,
        &context(&half, 1),
        &burn_command(&one_atom, 1),
        ZDEXBurnRejectCodeV1::PRECISION_RESCALE_REQUIRED,
    );
    let half_state = state(&half, 10, 0);
    let mut floor_context = context(&half, 1);
    floor_context.source_reserve_floor_atoms = 10;
    assert_burn_reject(
        &half,
        &half_state,
        &floor_context,
        &burn_command(&half_state, 1),
        ZDEXBurnRejectCodeV1::SOURCE_RESERVE_FLOOR_REACHED,
    );
    let mut epoch_context = context(&half, 1);
    epoch_context.remaining_epoch_burn_cap_atoms = 0;
    assert_burn_reject(
        &half,
        &half_state,
        &epoch_context,
        &burn_command(&half_state, 1),
        ZDEXBurnRejectCodeV1::EPOCH_BURN_CAP_REACHED,
    );
    let mut route_context = context(&half, 1);
    route_context.route_safe_output_cap_atoms = 0;
    assert_burn_reject(
        &half,
        &half_state,
        &route_context,
        &burn_command(&half_state, 1),
        ZDEXBurnRejectCodeV1::ROUTE_OUTPUT_CAP_ZERO,
    );
    assert_burn_reject(
        &half,
        &half_state,
        &context(&half, 6),
        &burn_command(&half_state, 6),
        ZDEXBurnRejectCodeV1::PURCHASE_EXCEEDS_BURN_CAPACITY,
    );
}

#[test]
fn precision_rescale_matches_python_roots_and_preserves_normalized_values() {
    let policy = ZDEXHyperdeflationPolicyV1 {
        asset_id: root(1),
        retained_numerator: 1,
        retained_denominator: 2,
        maximum_decimals: 32,
        maximum_decimal_step: 8,
    };
    let mut state = state(&policy, 3, 2);
    state.precision_epoch = 7;
    let result = transition_zdex_precision_rescale_v1(
        &policy,
        &state,
        &ZDEXPrecisionRescaleCommandV1 {
            expected_pre_state_root: state.state_root().unwrap(),
            expected_precision_epoch: 7,
            additional_decimals: 8,
        },
    )
    .unwrap();
    let ZDEXPrecisionRescaleResultV1::Accepted(accepted) = result else {
        panic!("bounded rescale must accept")
    };
    assert_eq!(
        policy.policy_root().unwrap().as_str(),
        "0x9d8a4006811588648e07ad65b7ba890465781e311e4e005210f2e205971b8c56"
    );
    assert_eq!(
        state.state_root().unwrap().as_str(),
        "0xc64e6e924955b5a2e81e33bb66daf9c113d14ae34412916ebd1a5e908655135b"
    );
    assert_eq!(
        accepted.post_state().state_root().unwrap().as_str(),
        "0xb001fa4fc9f895e0e006f556770c45428d3f553a24fb6a55319d32ce06f80198"
    );
    assert_eq!(accepted.effect().scale_factor, 100_000_000);
    assert_eq!(accepted.effect().supply_before_atoms, 5);
    assert_eq!(accepted.effect().supply_after_atoms, 500_000_000);
    assert_eq!(accepted.effect().authorized_issue_atoms, 0);
    assert_eq!(accepted.effect().authorized_burn_atoms, 0);
}

#[test]
fn precision_boundaries_and_overflow_are_typed_noops() {
    let policy = ZDEXHyperdeflationPolicyV1 {
        maximum_decimals: 64,
        maximum_decimal_step: MAX_DECIMAL_SCALE_STEP_V1,
        ..policy(1, 2)
    };
    let unit_state = state(&policy, 1, 0);
    let accepted = transition_zdex_precision_rescale_v1(
        &policy,
        &unit_state,
        &ZDEXPrecisionRescaleCommandV1 {
            expected_pre_state_root: unit_state.state_root().unwrap(),
            expected_precision_epoch: 0,
            additional_decimals: 38,
        },
    )
    .unwrap();
    assert!(matches!(
        accepted,
        ZDEXPrecisionRescaleResultV1::Accepted(_)
    ));
    let rejected = transition_zdex_precision_rescale_v1(
        &policy,
        &unit_state,
        &ZDEXPrecisionRescaleCommandV1 {
            expected_pre_state_root: unit_state.state_root().unwrap(),
            expected_precision_epoch: 0,
            additional_decimals: 39,
        },
    )
    .unwrap();
    assert!(matches!(
        rejected,
        ZDEXPrecisionRescaleResultV1::Rejected(value)
            if value.code() == ZDEXPrecisionRejectCodeV1::DECIMAL_STEP_EXCEEDS_POLICY
                && value.pre_state() == value.post_state()
                && value.effects().is_empty()
    ));

    let largest_safe = u128::MAX / 10;
    for (atoms, should_accept) in [(largest_safe, true), (largest_safe + 1, false)] {
        let state = state(&policy, atoms, 0);
        let result = transition_zdex_precision_rescale_v1(
            &policy,
            &state,
            &ZDEXPrecisionRescaleCommandV1 {
                expected_pre_state_root: state.state_root().unwrap(),
                expected_precision_epoch: 0,
                additional_decimals: 1,
            },
        )
        .unwrap();
        assert_eq!(
            matches!(result, ZDEXPrecisionRescaleResultV1::Accepted(_)),
            should_accept
        );
    }
}

#[test]
fn every_precision_reject_code_has_exact_noop_evidence() {
    let policy = ZDEXHyperdeflationPolicyV1 {
        maximum_decimals: 16,
        maximum_decimal_step: 8,
        ..policy(1, 2)
    };
    let base_state = state(&policy, 10, 0);
    let base = ZDEXPrecisionRescaleCommandV1 {
        expected_pre_state_root: base_state.state_root().unwrap(),
        expected_precision_epoch: 0,
        additional_decimals: 1,
    };
    let caller_policy = ZDEXHyperdeflationPolicyV1 {
        retained_numerator: 2,
        retained_denominator: 3,
        ..policy.clone()
    };
    assert_precision_reject(
        &caller_policy,
        &base_state,
        &base,
        ZDEXPrecisionRejectCodeV1::POLICY_MISMATCH,
    );
    assert_precision_reject(
        &policy,
        &base_state,
        &ZDEXPrecisionRescaleCommandV1 {
            expected_pre_state_root: root(99),
            ..base.clone()
        },
        ZDEXPrecisionRejectCodeV1::STALE_STATE,
    );
    assert_precision_reject(
        &policy,
        &base_state,
        &ZDEXPrecisionRescaleCommandV1 {
            expected_precision_epoch: 1,
            ..base.clone()
        },
        ZDEXPrecisionRejectCodeV1::PRECISION_EPOCH_MISMATCH,
    );
    assert_precision_reject(
        &policy,
        &base_state,
        &ZDEXPrecisionRescaleCommandV1 {
            additional_decimals: 0,
            ..base.clone()
        },
        ZDEXPrecisionRejectCodeV1::ZERO_DECIMAL_STEP,
    );
    assert_precision_reject(
        &policy,
        &base_state,
        &ZDEXPrecisionRescaleCommandV1 {
            additional_decimals: 9,
            ..base.clone()
        },
        ZDEXPrecisionRejectCodeV1::DECIMAL_STEP_EXCEEDS_POLICY,
    );
    let maximum_state = ZDEXSupplyStateV1 {
        decimals: 16,
        ..base_state.clone()
    };
    assert_precision_reject(
        &policy,
        &maximum_state,
        &ZDEXPrecisionRescaleCommandV1 {
            expected_pre_state_root: maximum_state.state_root().unwrap(),
            ..base.clone()
        },
        ZDEXPrecisionRejectCodeV1::MAXIMUM_DECIMALS_EXCEEDED,
    );
    let exhausted_state = ZDEXSupplyStateV1 {
        precision_epoch: u64::MAX,
        ..base_state.clone()
    };
    assert_precision_reject(
        &policy,
        &exhausted_state,
        &ZDEXPrecisionRescaleCommandV1 {
            expected_pre_state_root: exhausted_state.state_root().unwrap(),
            expected_precision_epoch: u64::MAX,
            additional_decimals: 1,
        },
        ZDEXPrecisionRejectCodeV1::EPOCH_COUNTER_EXHAUSTED,
    );
    let overflow_state = state(&policy, u128::MAX, 0);
    assert_precision_reject(
        &policy,
        &overflow_state,
        &ZDEXPrecisionRescaleCommandV1 {
            expected_pre_state_root: overflow_state.state_root().unwrap(),
            expected_precision_epoch: 0,
            additional_decimals: 1,
        },
        ZDEXPrecisionRejectCodeV1::ATOM_OVERFLOW,
    );
}

#[test]
fn strict_decode_and_structural_validation_fail_closed() {
    let policy = policy(9, 10);
    assert!(serde_json::from_value::<ZDEXAmountBucketV1>(json!({
        "bucket_id": "",
        "amount_atoms": 0,
    }))
    .is_err());
    assert!(serde_json::from_value::<ZDEXHyperdeflationPolicyV1>(json!({
        "asset_id": root(1),
        "retained_numerator": 9,
        "retained_denominator": 10,
        "maximum_decimals": 64,
        "maximum_decimal_step": 8,
        "unexpected": true,
    }))
    .is_err());
    for hostile in [json!(true), json!("9")] {
        assert!(serde_json::from_value::<ZDEXHyperdeflationPolicyV1>(json!({
            "asset_id": root(1),
            "retained_numerator": hostile,
            "retained_denominator": 10,
            "maximum_decimals": 64,
            "maximum_decimal_step": 8,
        }))
        .is_err());
    }
    assert!(serde_json::from_value::<ZDEXHyperdeflationPolicyV1>(json!({
        "asset_id": root(1),
        "retained_numerator": 10,
        "retained_denominator": 10,
        "maximum_decimals": 64,
        "maximum_decimal_step": 8,
    }))
    .is_err());
    let mut invalid_context = serde_json::to_value(context(&policy, 1)).unwrap();
    invalid_context["purchased_zdex_atoms"] = json!(0);
    assert!(serde_json::from_value::<ZDEXBurnRouteContextV1>(invalid_context).is_err());
    let valid_state = state(&policy, 10, 0);
    let mut invalid_burn_command = serde_json::to_value(burn_command(&valid_state, 1)).unwrap();
    invalid_burn_command["source_bucket_id"] = json!("");
    assert!(serde_json::from_value::<ZDEXPurchaseAndBurnCommandV1>(invalid_burn_command).is_err());
    let invalid_precision_command = json!({
        "expected_pre_state_root": format!("0x{}", "0".repeat(64)),
        "expected_precision_epoch": 0,
        "additional_decimals": 1,
    });
    assert!(
        serde_json::from_value::<ZDEXPrecisionRescaleCommandV1>(invalid_precision_command).is_err()
    );
    let invalid = ZDEXSupplyStateV1 {
        asset_id: policy.asset_id.clone(),
        policy_root: policy.policy_root().unwrap(),
        decimals: 8,
        precision_epoch: 0,
        live_supply_atoms: 4,
        buckets: vec![ZDEXAmountBucketV1 {
            bucket_id: "route:buyburn:source".to_owned(),
            amount_atoms: 3,
        }],
        burn_budget_epoch: 0,
        remaining_epoch_burn_cap_atoms: 4,
    };
    assert!(invalid.validate().is_err());
    assert!(
        serde_json::from_value::<ZDEXSupplyStateV1>(serde_json::to_value(&invalid).unwrap())
            .is_err()
    );

    let maximum_buckets = ZDEXSupplyStateV1 {
        live_supply_atoms: MAX_ZDEX_PROJECTION_BUCKETS_V1 as u128,
        buckets: (0..MAX_ZDEX_PROJECTION_BUCKETS_V1)
            .map(|index| ZDEXAmountBucketV1 {
                bucket_id: format!("wallet:{index:04}"),
                amount_atoms: 1,
            })
            .collect(),
        remaining_epoch_burn_cap_atoms: MAX_ZDEX_PROJECTION_BUCKETS_V1 as u128,
        ..state(&policy, 1, 0)
    };
    maximum_buckets.validate().unwrap();
    serde_json::from_value::<ZDEXSupplyStateV1>(serde_json::to_value(&maximum_buckets).unwrap())
        .unwrap();

    let too_many_buckets = ZDEXSupplyStateV1 {
        live_supply_atoms: maximum_buckets.live_supply_atoms + 1,
        buckets: (0..=MAX_ZDEX_PROJECTION_BUCKETS_V1)
            .map(|index| ZDEXAmountBucketV1 {
                bucket_id: format!("wallet:{index:04}"),
                amount_atoms: 1,
            })
            .collect(),
        remaining_epoch_burn_cap_atoms: maximum_buckets.remaining_epoch_burn_cap_atoms + 1,
        ..maximum_buckets
    };
    assert!(too_many_buckets.validate().is_err());
    assert!(serde_json::from_value::<ZDEXSupplyStateV1>(
        serde_json::to_value(&too_many_buckets).unwrap()
    )
    .is_err());
}
