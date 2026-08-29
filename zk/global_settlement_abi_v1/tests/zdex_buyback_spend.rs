use zenodex_global_settlement_abi_v1::{
    candidate_zdex_fee_allocation_policy_v1, transition_zdex_buyback_spend_v1, RootV1,
    ZDEXBuybackSpendContextV1, ZDEXBuybackSpendPolicyV1, ZDEXBuybackSpendRejectCodeV1,
    ZDEXBuybackSpendResultV1, ZDEXBuybackSpendStateV1, ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1, ZDEXFeeAllocationPolicyV1, ZDEXFeeAllocationRejectCodeV1,
    ZDEXFeeDestinationAmountV1, ZDEXFeeStateV1, ZDEX_BUYBACK_SPEND_CONTEXT_SCHEMA_V1,
    ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1, ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1,
    ZDEX_FEE_DESTINATIONS_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "buyback spend test root", false).unwrap()
}

fn spend_policy(minimum: u128, cap: u128, interval: u64) -> ZDEXBuybackSpendPolicyV1 {
    ZDEXBuybackSpendPolicyV1 {
        schema: ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1.to_owned(),
        quote_asset_id: root(1),
        minimum_quote_spend_atoms: minimum,
        per_command_quote_cap_atoms: cap,
        minimum_interval_blocks: interval,
    }
}

fn cadence(policy: &ZDEXBuybackSpendPolicyV1, last_height: Option<u64>) -> ZDEXBuybackSpendStateV1 {
    ZDEXBuybackSpendStateV1 {
        schema: ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1.to_owned(),
        quote_asset_id: policy.quote_asset_id.clone(),
        policy_root: policy.policy_root().unwrap(),
        last_execution_height: last_height,
    }
}

fn fee_policy() -> ZDEXFeeAllocationPolicyV1 {
    candidate_zdex_fee_allocation_policy_v1()
}

fn fee_state(policy: &ZDEXFeeAllocationPolicyV1, reserve: u128, fee_atoms: u128) -> ZDEXFeeStateV1 {
    ZDEXFeeStateV1 {
        fee_asset_id: root(1),
        policy_root: policy.policy_root().unwrap(),
        fee_ingress_atoms: fee_atoms,
        unallocated_reserve_atoms: 0,
        destination_balances: ZDEX_FEE_DESTINATIONS_V1
            .iter()
            .copied()
            .enumerate()
            .map(|(index, destination)| ZDEXFeeDestinationAmountV1 {
                destination,
                allocation_atoms: if index == 0 { reserve } else { 0 },
            })
            .collect(),
        owned_and_custodied_atoms: 10_000,
        supply_atoms: 10_000,
    }
}

fn fee_context(
    policy: &ZDEXFeeAllocationPolicyV1,
    route: RootV1,
    occurrence: RootV1,
) -> ZDEXFeeAllocationContextV1 {
    ZDEXFeeAllocationContextV1 {
        chain_id: "zenodex-shadow".to_owned(),
        deployment_root: root(2),
        profile_root: root(5),
        writer_epoch: 11,
        allocation_route_release_id: route.clone(),
        authorized_buyback_route_release_id: route,
        tokenomics_module_release_id: root(6),
        command_occurrence_id: occurrence,
        policy_root: policy.policy_root().unwrap(),
    }
}

fn spend_context(
    fee_state: &ZDEXFeeStateV1,
    cadence: &ZDEXBuybackSpendStateV1,
    height: u64,
    safe_limit: u128,
) -> ZDEXBuybackSpendContextV1 {
    ZDEXBuybackSpendContextV1 {
        schema: ZDEX_BUYBACK_SPEND_CONTEXT_SCHEMA_V1.to_owned(),
        profile_root: root(5),
        route_release_id: root(3),
        command_occurrence_id: root(4),
        expected_fee_pre_state_root: fee_state.state_root().unwrap(),
        expected_cadence_pre_state_root: cadence.state_root().unwrap(),
        safety_limit_binding_root: root(7),
        quote_asset_id: root(1),
        current_height: height,
        route_safe_quote_limit_atoms: safe_limit,
    }
}

struct FixtureV1 {
    spend_policy: ZDEXBuybackSpendPolicyV1,
    cadence: ZDEXBuybackSpendStateV1,
    fee_policy: ZDEXFeeAllocationPolicyV1,
    fee_state: ZDEXFeeStateV1,
    fee_context: ZDEXFeeAllocationContextV1,
    fee_command: ZDEXFeeAllocationCommandV1,
    context: ZDEXBuybackSpendContextV1,
}

#[derive(Clone, Copy)]
struct FixtureParamsV1 {
    reserve: u128,
    fee_atoms: u128,
    cap: u128,
    safe_limit: u128,
    minimum: u128,
    interval: u64,
    last_height: Option<u64>,
    height: u64,
}

const DEFAULT_FIXTURE_PARAMS_V1: FixtureParamsV1 = FixtureParamsV1 {
    reserve: 80,
    fee_atoms: 125,
    cap: 100,
    safe_limit: 70,
    minimum: 10,
    interval: 5,
    last_height: None,
    height: 20,
};

fn fixture(params: FixtureParamsV1) -> FixtureV1 {
    let spend_policy = spend_policy(params.minimum, params.cap, params.interval);
    let cadence = cadence(&spend_policy, params.last_height);
    let fee_policy = fee_policy();
    let fee_state = fee_state(&fee_policy, params.reserve, params.fee_atoms);
    let fee_context = fee_context(&fee_policy, root(3), root(4));
    let context = spend_context(&fee_state, &cadence, params.height, params.safe_limit);
    FixtureV1 {
        spend_policy,
        cadence,
        fee_policy,
        fee_state,
        fee_context,
        fee_command: ZDEXFeeAllocationCommandV1 {
            fee_charged_atoms: params.fee_atoms,
        },
        context,
    }
}

fn run(fixture: &FixtureV1) -> ZDEXBuybackSpendResultV1 {
    transition_zdex_buyback_spend_v1(
        &fixture.spend_policy,
        &fixture.cadence,
        &fixture.fee_policy,
        &fixture.fee_state,
        &fixture.fee_context,
        &fixture.fee_command,
        &fixture.context,
    )
    .unwrap()
}

fn assert_reject(
    result: ZDEXBuybackSpendResultV1,
    fixture: &FixtureV1,
    code: ZDEXBuybackSpendRejectCodeV1,
) -> Option<ZDEXFeeAllocationRejectCodeV1> {
    let ZDEXBuybackSpendResultV1::Rejected(rejected) = result else {
        panic!("invalid buyback spend must reject")
    };
    assert_eq!(rejected.code(), code);
    assert_eq!(rejected.cadence_pre_state(), &fixture.cadence);
    assert_eq!(rejected.cadence_post_state(), &fixture.cadence);
    assert_eq!(rejected.fee_pre_state(), &fixture.fee_state);
    assert_eq!(rejected.fee_post_state(), &fixture.fee_state);
    assert!(rejected.effects().is_empty());
    rejected.fee_code()
}

#[test]
fn spend_is_minimum_of_canonical_reserve_allocation_cap_and_limit() {
    for (reserve, fee_atoms, cap, safe_limit, expected) in [
        (80, 125, 100, 70, 70),
        (30, 25, 100, 70, 35),
        (80, 125, 40, 70, 40),
    ] {
        let fixture = fixture(FixtureParamsV1 {
            reserve,
            fee_atoms,
            cap,
            safe_limit,
            ..DEFAULT_FIXTURE_PARAMS_V1
        });
        let result = run(&fixture);
        let ZDEXBuybackSpendResultV1::Accepted(accepted) = result else {
            panic!("governed buyback spend must accept")
        };
        assert_eq!(
            accepted.intent().buyback_allocation_atoms,
            fee_atoms * 2_000 / 10_000
        );
        assert_eq!(accepted.intent().quote_spend_atoms, expected);
        assert_eq!(
            accepted.fee_post_state().destination_balances[0].allocation_atoms + expected,
            reserve + accepted.intent().buyback_allocation_atoms
        );
        assert_eq!(
            accepted.cadence_post_state().last_execution_height,
            Some(20)
        );
    }
}

#[test]
fn same_occurrence_binding_substitutions_reject_without_effect() {
    for field in ["profile", "route", "occurrence"] {
        let mut fixture = fixture(DEFAULT_FIXTURE_PARAMS_V1);
        match field {
            "profile" => fixture.context.profile_root = root(99),
            "route" => fixture.context.route_release_id = root(99),
            "occurrence" => fixture.context.command_occurrence_id = root(99),
            _ => unreachable!("test field list is closed"),
        }
        assert_reject(
            run(&fixture),
            &fixture,
            ZDEXBuybackSpendRejectCodeV1::SAME_OCCURRENCE_MISMATCH,
        );
    }
}

#[test]
fn stale_fee_or_cadence_root_rejects_without_effect() {
    let mut stale_fee = fixture(DEFAULT_FIXTURE_PARAMS_V1);
    stale_fee.context.expected_fee_pre_state_root = root(99);
    assert_reject(
        run(&stale_fee),
        &stale_fee,
        ZDEXBuybackSpendRejectCodeV1::STALE_STATE,
    );

    let mut stale_cadence = fixture(DEFAULT_FIXTURE_PARAMS_V1);
    stale_cadence.context.expected_cadence_pre_state_root = root(99);
    assert_reject(
        run(&stale_cadence),
        &stale_cadence,
        ZDEXBuybackSpendRejectCodeV1::STALE_STATE,
    );
}

#[test]
fn cadence_accepts_boundary_and_rejects_predecessor_and_regression() {
    let predecessor = fixture(FixtureParamsV1 {
        last_height: Some(20),
        height: 24,
        ..DEFAULT_FIXTURE_PARAMS_V1
    });
    assert_reject(
        run(&predecessor),
        &predecessor,
        ZDEXBuybackSpendRejectCodeV1::COOLDOWN_NOT_ELAPSED,
    );

    let boundary = fixture(FixtureParamsV1 {
        last_height: Some(20),
        height: 25,
        ..DEFAULT_FIXTURE_PARAMS_V1
    });
    let result = run(&boundary);
    let ZDEXBuybackSpendResultV1::Accepted(accepted) = result else {
        panic!("exact cadence boundary must accept")
    };
    assert_eq!(
        accepted.cadence_post_state().last_execution_height,
        Some(25)
    );

    let regression = fixture(FixtureParamsV1 {
        last_height: Some(20),
        height: 19,
        ..DEFAULT_FIXTURE_PARAMS_V1
    });
    assert_reject(
        run(&regression),
        &regression,
        ZDEXBuybackSpendRejectCodeV1::HEIGHT_REGRESSION,
    );
}

#[test]
fn fee_allocation_is_recomputed_and_its_rejection_is_preserved() {
    let mut fixture = fixture(DEFAULT_FIXTURE_PARAMS_V1);
    fixture.fee_command.fee_charged_atoms = 126;
    let fee_code = assert_reject(
        run(&fixture),
        &fixture,
        ZDEXBuybackSpendRejectCodeV1::FEE_ALLOCATION_REJECTED,
    );
    assert_eq!(
        fee_code,
        Some(ZDEXFeeAllocationRejectCodeV1::INSUFFICIENT_FEE_INGRESS)
    );
}

#[test]
fn safe_limit_boundaries_reject_without_effect() {
    let zero = fixture(FixtureParamsV1 {
        safe_limit: 0,
        ..DEFAULT_FIXTURE_PARAMS_V1
    });
    assert_reject(
        run(&zero),
        &zero,
        ZDEXBuybackSpendRejectCodeV1::ROUTE_SAFE_LIMIT_ZERO,
    );

    let below_minimum = fixture(FixtureParamsV1 {
        safe_limit: 9,
        ..DEFAULT_FIXTURE_PARAMS_V1
    });
    assert_reject(
        run(&below_minimum),
        &below_minimum,
        ZDEXBuybackSpendRejectCodeV1::SPEND_BELOW_MINIMUM,
    );
}

#[test]
fn intent_binds_policy_and_both_authoritative_pre_states() {
    let fixture = fixture(DEFAULT_FIXTURE_PARAMS_V1);
    let result = run(&fixture);
    let ZDEXBuybackSpendResultV1::Accepted(accepted) = result else {
        panic!("fixture must accept")
    };

    assert_eq!(
        accepted.intent().spend_policy_root,
        accepted.spend_policy().policy_root().unwrap()
    );
    assert_eq!(
        accepted.intent().cadence_pre_state_root,
        accepted.cadence_pre_state().state_root().unwrap()
    );
    assert_eq!(
        accepted.intent().fee_pre_state_root,
        accepted.fee_allocation().pre_state.state_root().unwrap()
    );
    assert_eq!(
        accepted.intent().fee_allocated_state_root,
        accepted.fee_allocation().post_state.state_root().unwrap()
    );
    assert_eq!(
        accepted.intent().fee_allocation_occurrence_root,
        accepted
            .fee_allocation()
            .occurrence
            .occurrence_root()
            .unwrap()
    );
}

#[test]
fn small_boundary_grid_preserves_canonical_fee_reserve_equation() {
    for reserve in 0..3_u128 {
        for fee_atoms in [1_u128, 5, 20] {
            for cap in 1..4_u128 {
                for safe_limit in 1..4_u128 {
                    let fixture = fixture(FixtureParamsV1 {
                        reserve,
                        fee_atoms,
                        cap,
                        safe_limit,
                        minimum: 1,
                        interval: 1,
                        ..DEFAULT_FIXTURE_PARAMS_V1
                    });
                    let result = run(&fixture);
                    let allocation = fee_atoms * 2_000 / 10_000;
                    let available = reserve + allocation;
                    let expected = available.min(cap).min(safe_limit);
                    if expected == 0 {
                        assert_reject(
                            result,
                            &fixture,
                            ZDEXBuybackSpendRejectCodeV1::SPEND_BELOW_MINIMUM,
                        );
                    } else {
                        let ZDEXBuybackSpendResultV1::Accepted(accepted) = result else {
                            panic!("admitted finite-domain spend must accept")
                        };
                        assert_eq!(accepted.intent().quote_spend_atoms, expected);
                        assert_eq!(
                            accepted.fee_post_state().destination_balances[0].allocation_atoms
                                + expected,
                            available
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn policy_invalid_bounds_fail_closed() {
    assert!(spend_policy(0, 1, 1).validate().is_err());
    assert!(spend_policy(2, 1, 1).validate().is_err());
    assert!(spend_policy(1, i128::MAX.unsigned_abs() + 1, 1)
        .validate()
        .is_err());
    assert!(spend_policy(1, 1, 0).validate().is_err());
}

#[test]
fn canonical_roots_match_the_python_refinement_vector() {
    let fixture = fixture(DEFAULT_FIXTURE_PARAMS_V1);
    let result = run(&fixture);
    let ZDEXBuybackSpendResultV1::Accepted(accepted) = result else {
        panic!("Python refinement vector must accept")
    };

    assert_eq!(
        fixture.spend_policy.policy_root().unwrap().as_str(),
        "0x7dd117ac6614e82d74a65ff724616b1765256b100f832c6fa3df110c1cdb8eac"
    );
    assert_eq!(
        fixture.cadence.state_root().unwrap().as_str(),
        "0x111762570a0f3650ad40d560c530806d26214fd3cd9e9956b0cd0e45bcb97e93"
    );
    assert_eq!(
        fixture.fee_state.state_root().unwrap().as_str(),
        "0xcb89493719db4bef27ec4596fc9c77f3c8a734d881f881e1caef29e2d9794974"
    );
    assert_eq!(
        accepted.intent().intent_root().unwrap().as_str(),
        "0x1c50575386f844883f1256ed8bbda64524e2ada64bc0c4a9ad5372e4bbf1b6e0"
    );
    assert_eq!(
        accepted
            .fee_allocation()
            .occurrence
            .occurrence_root()
            .unwrap()
            .as_str(),
        "0x0ec3793f0c544e196fc913f998badbf47e9880e1feac871fb9520d978c3c6df3"
    );
    assert_eq!(
        accepted
            .fee_allocation()
            .post_state
            .state_root()
            .unwrap()
            .as_str(),
        "0x3bff1b6fd670e54ce506e853ce4cf59cfab56bf7cc07fc61450566cf9d5425fa"
    );
    assert_eq!(
        accepted.fee_post_state().state_root().unwrap().as_str(),
        "0x5185a99e77f8aced86876e91644252c7c3ea89b2c2053cbd6837471268f84353"
    );
    assert_eq!(
        accepted.cadence_post_state().state_root().unwrap().as_str(),
        "0xffb59d9af14c7f0e6963db519dbf1b763fc3eb303c7047dcd0a830881d5d986c"
    );
}
