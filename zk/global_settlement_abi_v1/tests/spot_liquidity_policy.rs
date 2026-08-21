use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    g1_testnet_spot_lp_policy_candidate_v1, lp_add_quote_v1, lp_create_quote_v1,
    lp_remove_quote_v1, spot_exact_in_quote_v1, spot_exact_out_quote_v1, G1SpotLpPolicyCandidateV1,
    G1SpotLpSelectionV1, PoolReserveIngressV1, RootV1, SpotLpRejectV1, SpotPoolMathStateV1,
    SpotPoolStatusV1, G1_SPOT_LP_MAX_POOL_ATOMS_V1, G1_SPOT_LP_SWAP_FEE_BPS_V1,
};

fn root(byte: u8) -> RootV1 {
    RootV1::parse(format!("0x{}", hex::encode([byte; 32])), "test root", false).unwrap()
}

fn candidate() -> G1SpotLpPolicyCandidateV1 {
    g1_testnet_spot_lp_policy_candidate_v1(root(7))
}

#[test]
fn exact_candidate_is_closed_unselected_and_canonically_rooted() {
    // Arrange
    let candidate = candidate();

    // Act
    candidate.validate().unwrap();
    let encoded = serde_json::to_value(&candidate).unwrap();
    let profile_root = candidate.profile_root().unwrap();

    // Assert
    assert_eq!(candidate.swap_fee_bps, G1_SPOT_LP_SWAP_FEE_BPS_V1);
    assert_eq!(candidate.protocol_fee_share_bps, 0);
    assert_eq!(
        candidate.reserve_ingress,
        PoolReserveIngressV1::POOL_KERNEL_ONLY
    );
    assert_eq!(
        candidate.selection,
        G1SpotLpSelectionV1::CANDIDATE_UNSELECTED_USER_CONFIRMATION_REQUIRED
    );
    assert_eq!(
        encoded["selection"],
        "CANDIDATE_UNSELECTED_USER_CONFIRMATION_REQUIRED"
    );
    assert!(!profile_root.is_zero());
}

#[test]
fn policy_mutations_reject_before_arithmetic() {
    // Arrange
    let baseline = candidate();
    let mut changed_fee = baseline.clone();
    changed_fee.swap_fee_bps += 1;
    let mut changed_protocol_share = baseline.clone();
    changed_protocol_share.protocol_fee_share_bps = 1;

    // Act / Assert
    assert!(changed_fee.validate().is_err());
    assert_eq!(
        spot_exact_in_quote_v1(&changed_fee, 10_000, 10_000, 1_000),
        Err(SpotLpRejectV1::INVALID_POLICY)
    );
    assert!(changed_protocol_share.validate().is_err());

    let wrong_predecessor = root(8);
    assert!(baseline
        .validate_for_asset_authority_root(&wrong_predecessor)
        .is_err());
}

#[test]
fn exact_in_fee_bva_uses_ceil_and_keeps_every_fee_atom_in_reserves() {
    // Arrange / Act
    let too_small = spot_exact_in_quote_v1(&candidate(), 10_000, 10_000, 1);
    let below_rounding_step = spot_exact_in_quote_v1(&candidate(), 10_000, 10_000, 333).unwrap();
    let above_rounding_step = spot_exact_in_quote_v1(&candidate(), 10_000, 10_000, 334).unwrap();
    let ordinary = spot_exact_in_quote_v1(&candidate(), 10_000, 20_000, 1_000).unwrap();

    // Assert
    assert_eq!(too_small, Err(SpotLpRejectV1::FEE_CONSUMES_INPUT));
    assert_eq!(below_rounding_step.fee_atoms, 1);
    assert_eq!(above_rounding_step.fee_atoms, 2);
    assert_eq!(ordinary.fee_atoms, 3);
    assert_eq!(ordinary.net_input_atoms, 997);
    assert_eq!(ordinary.output_atoms, (20_000 * 997) / 10_997);
    assert_eq!(ordinary.post_reserve_in_atoms, 11_000);
    assert_eq!(
        ordinary.post_reserve_out_atoms,
        20_000 - ordinary.output_atoms
    );
    assert!(ordinary.k_after >= ordinary.k_before);
}

#[test]
fn exact_out_quote_is_minimal_and_preserves_requested_output() {
    // Arrange / Act
    let quote = spot_exact_out_quote_v1(&candidate(), 10_000, 20_000, 1_000).unwrap();
    let replay =
        spot_exact_in_quote_v1(&candidate(), 10_000, 20_000, quote.required_input_atoms).unwrap();

    // Assert
    assert!(replay.output_atoms >= quote.requested_output_atoms);
    assert_eq!(
        replay.output_atoms - quote.requested_output_atoms,
        quote.pool_retained_output_atoms
    );
    assert_eq!(quote.post_reserve_out_atoms, 19_000);
    if quote.required_input_atoms > 1 {
        let prior =
            spot_exact_in_quote_v1(&candidate(), 10_000, 20_000, quote.required_input_atoms - 1);
        assert!(prior.is_err() || prior.unwrap().output_atoms < 1_000);
    }
}

#[test]
fn exact_out_derived_input_over_limit_rejects_before_widened_fee_arithmetic() {
    // Arrange / Act
    let result = spot_exact_out_quote_v1(
        &candidate(),
        G1_SPOT_LP_MAX_POOL_ATOMS_V1,
        G1_SPOT_LP_MAX_POOL_ATOMS_V1,
        G1_SPOT_LP_MAX_POOL_ATOMS_V1 - 1,
    );

    // Assert
    assert_eq!(result, Err(SpotLpRejectV1::LIMIT_EXCEEDED));
}

#[test]
fn lp_create_and_add_use_no_permanent_lock_and_refund_excess() {
    // Arrange / Act
    let created = lp_create_quote_v1(&candidate(), 10_000, 40_000).unwrap();
    let added = lp_add_quote_v1(
        &candidate(),
        &SpotPoolMathStateV1 {
            reserve0_atoms: 1_000,
            reserve1_atoms: 2_000,
            lp_supply_atoms: 1_000,
            status: SpotPoolStatusV1::ACTIVE,
        },
        400,
        900,
    )
    .unwrap();

    // Assert
    assert_eq!(created.lp_minted_atoms, 20_000);
    assert_eq!(created.post_pool.lp_supply_atoms, 20_000);
    assert_eq!(added.lp_minted_atoms, 400);
    assert_eq!(
        (added.amount0_used_atoms, added.amount1_used_atoms),
        (400, 800)
    );
    assert_eq!(
        (added.amount0_refund_atoms, added.amount1_refund_atoms),
        (0, 100)
    );
    assert_eq!(
        added.post_pool,
        SpotPoolMathStateV1 {
            reserve0_atoms: 1_400,
            reserve1_atoms: 2_800,
            lp_supply_atoms: 1_400,
            status: SpotPoolStatusV1::ACTIVE,
        }
    );
}

#[test]
fn partial_withdrawal_leaves_rounding_with_remaining_claimants() {
    // Arrange
    let pool = SpotPoolMathStateV1 {
        reserve0_atoms: 1_001,
        reserve1_atoms: 2_003,
        lp_supply_atoms: 1_000,
        status: SpotPoolStatusV1::ACTIVE,
    };

    // Act
    let withdrawal = lp_remove_quote_v1(&candidate(), &pool, 333).unwrap();

    // Assert
    assert_eq!(withdrawal.amount0_out_atoms, (333 * 1_001) / 1_000);
    assert_eq!(withdrawal.amount1_out_atoms, (333 * 2_003) / 1_000);
    assert_eq!(withdrawal.amount0_rounding_numerator, (333 * 1_001) % 1_000);
    assert_eq!(withdrawal.amount1_rounding_numerator, (333 * 2_003) % 1_000);
    assert_eq!(withdrawal.rounding_denominator, 1_000);
    assert!(!withdrawal.terminal_closed);
    assert_eq!(withdrawal.post_pool.lp_supply_atoms, 667);
}

#[test]
fn final_supply_burn_drains_every_reserve_atom_and_closes_pool() {
    // Arrange
    let pool = SpotPoolMathStateV1 {
        reserve0_atoms: 17,
        reserve1_atoms: 29,
        lp_supply_atoms: 3,
        status: SpotPoolStatusV1::ACTIVE,
    };

    // Act
    let withdrawal = lp_remove_quote_v1(&candidate(), &pool, 3).unwrap();

    // Assert
    assert_eq!(
        (withdrawal.amount0_out_atoms, withdrawal.amount1_out_atoms),
        (17, 29)
    );
    assert_eq!(withdrawal.amount0_rounding_numerator, 0);
    assert_eq!(withdrawal.amount1_rounding_numerator, 0);
    assert!(withdrawal.terminal_closed);
    assert_eq!(
        withdrawal.post_pool,
        SpotPoolMathStateV1 {
            reserve0_atoms: 0,
            reserve1_atoms: 0,
            lp_supply_atoms: 0,
            status: SpotPoolStatusV1::CLOSED,
        }
    );
    assert_eq!(
        lp_add_quote_v1(&candidate(), &withdrawal.post_pool, 1, 1),
        Err(SpotLpRejectV1::POOL_NOT_ACTIVE)
    );
}

#[test]
fn zero_overflow_and_inconsistent_state_boundaries_fail_closed() {
    // Arrange
    let policy = candidate();

    // Act / Assert
    assert_eq!(
        lp_create_quote_v1(&policy, 0, 1),
        Err(SpotLpRejectV1::ZERO_AMOUNT)
    );
    assert_eq!(
        spot_exact_in_quote_v1(&policy, G1_SPOT_LP_MAX_POOL_ATOMS_V1, 1, 1),
        Err(SpotLpRejectV1::LIMIT_EXCEEDED)
    );
    assert_eq!(
        lp_add_quote_v1(
            &policy,
            &SpotPoolMathStateV1 {
                reserve0_atoms: 1,
                reserve1_atoms: 1,
                lp_supply_atoms: 0,
                status: SpotPoolStatusV1::ACTIVE,
            },
            1,
            1,
        ),
        Err(SpotLpRejectV1::INCONSISTENT_POOL_STATE)
    );
}

#[test]
fn bounded_swap_arithmetic_laws_hold() {
    // Arrange
    let policy = candidate();

    // Act / Assert: exhaustive deterministic small-domain refutation screen.
    for reserve_in in 2u128..=24 {
        for reserve_out in 2u128..=24 {
            for gross_input in 2u128..=48 {
                if reserve_in + gross_input > G1_SPOT_LP_MAX_POOL_ATOMS_V1 {
                    continue;
                }
                if let Ok(quote) =
                    spot_exact_in_quote_v1(&policy, reserve_in, reserve_out, gross_input)
                {
                    let expected_fee = (gross_input * 30).div_ceil(10_000);
                    assert_eq!(quote.fee_atoms, expected_fee);
                    assert_eq!(quote.net_input_atoms + quote.fee_atoms, gross_input);
                    assert_eq!(quote.post_reserve_in_atoms, reserve_in + gross_input);
                    assert_eq!(
                        quote.post_reserve_out_atoms + quote.output_atoms,
                        reserve_out
                    );
                    assert!(quote.k_after >= quote.k_before);
                }
            }
            for requested_output in 1u128..reserve_out {
                if let Ok(quote) =
                    spot_exact_out_quote_v1(&policy, reserve_in, reserve_out, requested_output)
                {
                    let replay = spot_exact_in_quote_v1(
                        &policy,
                        reserve_in,
                        reserve_out,
                        quote.required_input_atoms,
                    )
                    .unwrap();
                    assert!(replay.output_atoms >= requested_output);
                    if quote.required_input_atoms > 1 {
                        let prior = spot_exact_in_quote_v1(
                            &policy,
                            reserve_in,
                            reserve_out,
                            quote.required_input_atoms - 1,
                        );
                        assert!(
                            prior.is_err()
                                || prior.as_ref().unwrap().output_atoms < requested_output
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn bounded_lp_withdrawal_laws_hold() {
    // Arrange
    let policy = candidate();

    // Act / Assert: exhaustive deterministic small-domain refutation screen.
    for reserve0 in 2u128..=16 {
        for reserve1 in 2u128..=16 {
            for supply in 2u128..=16 {
                let pool = SpotPoolMathStateV1 {
                    reserve0_atoms: reserve0,
                    reserve1_atoms: reserve1,
                    lp_supply_atoms: supply,
                    status: SpotPoolStatusV1::ACTIVE,
                };
                for burn in 1u128..=supply {
                    if let Ok(withdrawal) = lp_remove_quote_v1(&policy, &pool, burn) {
                        assert_eq!(
                            withdrawal.amount0_out_atoms + withdrawal.post_pool.reserve0_atoms,
                            reserve0
                        );
                        assert_eq!(
                            withdrawal.amount1_out_atoms + withdrawal.post_pool.reserve1_atoms,
                            reserve1
                        );
                        assert_eq!(burn + withdrawal.post_pool.lp_supply_atoms, supply);
                        assert_eq!(withdrawal.terminal_closed, burn == supply);
                    }
                }
            }
        }
    }
}

fn artifact_and_candidate() -> (Value, G1SpotLpPolicyCandidateV1) {
    let artifact: Value = serde_json::from_str(include_str!(
        "../../../docs/research/PRODUCTION_READINESS_G1_SPOT_LP_POLICY_V1.json"
    ))
    .unwrap();
    let asset_root = RootV1::parse(
        artifact["asset_authority_binding"]["candidate_profile_root"]
            .as_str()
            .unwrap(),
        "asset authority candidate profile root",
        false,
    )
    .unwrap();
    let candidate = g1_testnet_spot_lp_policy_candidate_v1(asset_root);
    (artifact, candidate)
}

#[test]
fn python_and_rust_candidate_roots_match() {
    // Arrange / Act
    let (artifact, candidate) = artifact_and_candidate();

    // Assert
    assert_eq!(
        candidate.profile_root().unwrap().as_str(),
        artifact["canonical_rust_binding"]["candidate_profile_root"]
            .as_str()
            .unwrap()
    );
}

#[test]
fn python_and_rust_exact_in_vectors_match() {
    // Arrange
    let (artifact, candidate) = artifact_and_candidate();

    // Act / Assert
    for vector in artifact["differential_vectors"]["exact_in"]
        .as_array()
        .unwrap()
    {
        let input = &vector["input"];
        let result = spot_exact_in_quote_v1(
            &candidate,
            u128::from(input["reserve_in_atoms"].as_u64().unwrap()),
            u128::from(input["reserve_out_atoms"].as_u64().unwrap()),
            u128::from(input["gross_input_atoms"].as_u64().unwrap()),
        )
        .unwrap();
        assert_eq!(serde_json::to_value(result).unwrap(), vector["expected"]);
    }
}

#[test]
fn python_and_rust_exact_out_vectors_match() {
    // Arrange
    let (artifact, candidate) = artifact_and_candidate();

    // Act / Assert
    for vector in artifact["differential_vectors"]["exact_out"]
        .as_array()
        .unwrap()
    {
        let input = &vector["input"];
        let result = spot_exact_out_quote_v1(
            &candidate,
            u128::from(input["reserve_in_atoms"].as_u64().unwrap()),
            u128::from(input["reserve_out_atoms"].as_u64().unwrap()),
            u128::from(input["requested_output_atoms"].as_u64().unwrap()),
        )
        .unwrap();
        assert_eq!(serde_json::to_value(result).unwrap(), vector["expected"]);
    }
}

#[test]
fn python_and_rust_lp_lifecycle_vectors_match() {
    // Arrange
    let (artifact, candidate) = artifact_and_candidate();

    // Act / Assert
    for vector in artifact["differential_vectors"]["lp_lifecycle"]
        .as_array()
        .unwrap()
    {
        let input = &vector["input"];
        let expected = &vector["expected"];
        match vector["operation"].as_str().unwrap() {
            "CREATE" => {
                let result = lp_create_quote_v1(
                    &candidate,
                    u128::from(input["amount0_atoms"].as_u64().unwrap()),
                    u128::from(input["amount1_atoms"].as_u64().unwrap()),
                )
                .unwrap();
                assert_eq!(serde_json::to_value(result).unwrap(), *expected);
            }
            "ADD" => {
                let pool: SpotPoolMathStateV1 =
                    serde_json::from_value(input["pool"].clone()).unwrap();
                let result = lp_add_quote_v1(
                    &candidate,
                    &pool,
                    u128::from(input["amount0_desired_atoms"].as_u64().unwrap()),
                    u128::from(input["amount1_desired_atoms"].as_u64().unwrap()),
                )
                .unwrap();
                assert_eq!(serde_json::to_value(result).unwrap(), *expected);
            }
            "REMOVE" => {
                let pool: SpotPoolMathStateV1 =
                    serde_json::from_value(input["pool"].clone()).unwrap();
                let result = lp_remove_quote_v1(
                    &candidate,
                    &pool,
                    u128::from(input["lp_burn_atoms"].as_u64().unwrap()),
                )
                .unwrap();
                assert_eq!(serde_json::to_value(result).unwrap(), *expected);
            }
            operation => panic!("unexpected vector operation: {operation}"),
        }
    }
}

#[test]
fn serde_rejects_unknown_candidate_fields() {
    // Arrange
    let mut encoded = serde_json::to_value(candidate()).unwrap();
    encoded["caller_selected_fee"] = Value::from(1);

    // Act
    let decoded = serde_json::from_value::<G1SpotLpPolicyCandidateV1>(encoded);

    // Assert
    assert!(decoded.is_err());
}
