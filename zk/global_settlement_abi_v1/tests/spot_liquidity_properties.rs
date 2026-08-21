use zenodex_global_settlement_abi_v1::{
    g1_testnet_spot_lp_policy_candidate_v1, lp_add_quote_v1, lp_remove_quote_v1,
    spot_exact_out_quote_v1, RootV1, SpotLpRejectV1, SpotPoolMathStateV1, SpotPoolStatusV1,
    G1_SPOT_LP_MAX_POOL_ATOMS_V1,
};

fn root(byte: u8) -> RootV1 {
    RootV1::parse(format!("0x{}", hex::encode([byte; 32])), "test root", false).unwrap()
}

fn independent_output_atoms(reserve_in: u128, reserve_out: u128, gross: u128) -> Option<u128> {
    let fee = (gross * 30).div_ceil(10_000);
    if fee >= gross {
        return None;
    }
    let net = gross - fee;
    let output = (reserve_out * net) / (reserve_in + net);
    (output > 0).then_some(output)
}

fn independent_minimum_gross(
    reserve_in: u128,
    reserve_out: u128,
    requested_output: u128,
) -> Option<(u128, u128)> {
    (1..=512).find_map(|gross| {
        let output = independent_output_atoms(reserve_in, reserve_out, gross)?;
        (output >= requested_output).then_some((gross, output))
    })
}

fn ceil_ratio(numerator: u128, denominator: u128) -> u128 {
    numerator.div_ceil(denominator)
}

#[test]
fn independent_bruteforce_oracle_confirms_exact_out_minimality_and_pool_retention() {
    // Arrange
    let policy = g1_testnet_spot_lp_policy_candidate_v1(root(7));

    // Act / Assert: independent finite search, without calling the exact-in kernel.
    for reserve_in in 2u128..=16 {
        for reserve_out in 2u128..=16 {
            for requested_output in 1u128..reserve_out {
                let (minimum_gross, independent_output) =
                    independent_minimum_gross(reserve_in, reserve_out, requested_output)
                        .expect("every bounded exact-out case has a brute-force witness");
                let quote =
                    spot_exact_out_quote_v1(&policy, reserve_in, reserve_out, requested_output)
                        .unwrap();

                assert_eq!(quote.required_input_atoms, minimum_gross);
                assert_eq!(quote.quoted_output_atoms, independent_output);
                assert_eq!(
                    quote.pool_retained_output_atoms,
                    independent_output - requested_output
                );
                assert_eq!(quote.post_reserve_out_atoms + requested_output, reserve_out);
            }
        }
    }
}

#[test]
fn independent_bruteforce_oracle_confirms_lp_add_maximality_and_non_dilution() {
    // Arrange
    let policy = g1_testnet_spot_lp_policy_candidate_v1(root(7));

    // Act / Assert: enumerate feasible mint counts independently from the kernel formula.
    for reserve0 in 1u128..=8 {
        for reserve1 in 1u128..=8 {
            for supply in 1u128..=8 {
                let pool = SpotPoolMathStateV1 {
                    reserve0_atoms: reserve0,
                    reserve1_atoms: reserve1,
                    lp_supply_atoms: supply,
                    status: SpotPoolStatusV1::ACTIVE,
                };
                for desired0 in 1u128..=12 {
                    for desired1 in 1u128..=12 {
                        let feasible = (1u128..=96)
                            .filter(|minted| {
                                ceil_ratio(minted * reserve0, supply) <= desired0
                                    && ceil_ratio(minted * reserve1, supply) <= desired1
                            })
                            .max();
                        let observed = lp_add_quote_v1(&policy, &pool, desired0, desired1);

                        let Some(maximal_mint) = feasible else {
                            assert_eq!(observed, Err(SpotLpRejectV1::ZERO_LP_MINT));
                            continue;
                        };
                        let quote = observed.unwrap();
                        assert_eq!(quote.lp_minted_atoms, maximal_mint);
                        assert_eq!(
                            quote.amount0_used_atoms,
                            ceil_ratio(maximal_mint * reserve0, supply)
                        );
                        assert_eq!(
                            quote.amount1_used_atoms,
                            ceil_ratio(maximal_mint * reserve1, supply)
                        );
                        assert_eq!(
                            quote.amount0_used_atoms + quote.amount0_refund_atoms,
                            desired0
                        );
                        assert_eq!(
                            quote.amount1_used_atoms + quote.amount1_refund_atoms,
                            desired1
                        );
                        assert!(
                            quote.post_pool.reserve0_atoms * supply
                                >= reserve0 * quote.post_pool.lp_supply_atoms
                        );
                        assert!(
                            quote.post_pool.reserve1_atoms * supply
                                >= reserve1 * quote.post_pool.lp_supply_atoms
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn malformed_pool_fields_have_stable_rejections() {
    // Arrange
    let policy = g1_testnet_spot_lp_policy_candidate_v1(root(7));
    let valid = SpotPoolMathStateV1 {
        reserve0_atoms: 10,
        reserve1_atoms: 20,
        lp_supply_atoms: 10,
        status: SpotPoolStatusV1::ACTIVE,
    };
    let inconsistent = [
        SpotPoolMathStateV1 {
            reserve0_atoms: 0,
            ..valid
        },
        SpotPoolMathStateV1 {
            reserve1_atoms: 0,
            ..valid
        },
        SpotPoolMathStateV1 {
            lp_supply_atoms: 0,
            ..valid
        },
    ];
    let over_limit = [
        SpotPoolMathStateV1 {
            reserve0_atoms: G1_SPOT_LP_MAX_POOL_ATOMS_V1 + 1,
            ..valid
        },
        SpotPoolMathStateV1 {
            reserve1_atoms: G1_SPOT_LP_MAX_POOL_ATOMS_V1 + 1,
            ..valid
        },
        SpotPoolMathStateV1 {
            lp_supply_atoms: G1_SPOT_LP_MAX_POOL_ATOMS_V1 + 1,
            ..valid
        },
    ];
    let closed_with_reserves = SpotPoolMathStateV1 {
        status: SpotPoolStatusV1::CLOSED,
        ..valid
    };

    // Act / Assert
    for pool in inconsistent {
        assert_eq!(
            lp_add_quote_v1(&policy, &pool, 1, 1),
            Err(SpotLpRejectV1::INCONSISTENT_POOL_STATE)
        );
    }
    for pool in over_limit {
        assert_eq!(
            lp_add_quote_v1(&policy, &pool, 1, 1),
            Err(SpotLpRejectV1::LIMIT_EXCEEDED)
        );
    }
    assert_eq!(
        lp_add_quote_v1(&policy, &closed_with_reserves, 1, 1),
        Err(SpotLpRejectV1::POOL_NOT_ACTIVE)
    );
}

#[test]
fn burn_boundaries_have_stable_rejections() {
    // Arrange
    let policy = g1_testnet_spot_lp_policy_candidate_v1(root(7));
    let valid = SpotPoolMathStateV1 {
        reserve0_atoms: 10,
        reserve1_atoms: 20,
        lp_supply_atoms: 10,
        status: SpotPoolStatusV1::ACTIVE,
    };

    // Act / Assert
    assert_eq!(
        lp_remove_quote_v1(&policy, &valid, 0),
        Err(SpotLpRejectV1::ZERO_AMOUNT)
    );
    assert_eq!(
        lp_remove_quote_v1(&policy, &valid, valid.lp_supply_atoms + 1),
        Err(SpotLpRejectV1::LP_BURN_EXCEEDS_SUPPLY)
    );
}
