use zenodex_global_settlement_abi_v1::{
    g1_testnet_spot_lp_policy_candidate_v1, lp_add_quote_v1, lp_create_quote_v1,
    lp_remove_quote_v1, spot_exact_in_quote_v1, RootV1, SpotPoolMathStateV1,
};

fn root(byte: u8) -> RootV1 {
    RootV1::parse(format!("0x{}", hex::encode([byte; 32])), "test root", false).unwrap()
}

#[test]
fn stateful_create_add_swap_remove_and_final_close_conserves_pool_atoms() {
    // Arrange
    let policy = g1_testnet_spot_lp_policy_candidate_v1(root(7));
    let created = lp_create_quote_v1(&policy, 10_000, 20_000).unwrap();
    let added = lp_add_quote_v1(&policy, &created.post_pool, 5_000, 10_000).unwrap();

    // Act
    let swap = spot_exact_in_quote_v1(
        &policy,
        added.post_pool.reserve0_atoms,
        added.post_pool.reserve1_atoms,
        1_000,
    )
    .unwrap();
    let after_swap = SpotPoolMathStateV1 {
        reserve0_atoms: swap.post_reserve_in_atoms,
        reserve1_atoms: swap.post_reserve_out_atoms,
        ..added.post_pool
    };
    let partial = lp_remove_quote_v1(&policy, &after_swap, 1).unwrap();
    let final_withdrawal = lp_remove_quote_v1(
        &policy,
        &partial.post_pool,
        partial.post_pool.lp_supply_atoms,
    )
    .unwrap();

    // Assert
    assert_eq!(
        swap.post_reserve_in_atoms,
        added.post_pool.reserve0_atoms + 1_000
    );
    assert_eq!(
        partial.amount0_out_atoms + partial.post_pool.reserve0_atoms,
        after_swap.reserve0_atoms
    );
    assert_eq!(
        partial.amount1_out_atoms + partial.post_pool.reserve1_atoms,
        after_swap.reserve1_atoms
    );
    assert!(final_withdrawal.terminal_closed);
    assert_eq!(final_withdrawal.post_pool.reserve0_atoms, 0);
    assert_eq!(final_withdrawal.post_pool.reserve1_atoms, 0);
}
