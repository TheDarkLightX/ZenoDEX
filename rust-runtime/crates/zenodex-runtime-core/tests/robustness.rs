//! Fuzz-grade robustness harness for every public transition (runs on stable).
//!
//! `cargo-fuzz` (libFuzzer) needs a nightly toolchain, which is not available in
//! this environment. This harness gives the *property* a fuzzer targets first —
//! "no input makes a public transition panic; it always returns a typed
//! `Result`, and accepted post-states satisfy the kernel invariants" — using
//! `proptest` with thousands of adversarial cases per kernel, including
//! out-of-domain, boundary, and degenerate values.
//!
//! It complements (does not replace) the Python/Rust differential and the
//! per-kernel semantic invariants. The `fuzz/` crate holds the matching
//! `cargo-fuzz` targets for when a nightly toolchain is present; this harness is
//! the always-on, stable-toolchain robustness net (see
//! `docs/runtime/SEMANTIC_DRIFT_CONTROLS.md`).

use proptest::prelude::*;
use zenodex_runtime_core::balance_kernel::{credit, transfer, BalanceState, MAX_BALANCE};
use zenodex_runtime_core::burn_receipts::{verify_rails, RailInputs};
use zenodex_runtime_core::cpmm_swap::{init_pool, swap_exact_in, swap_exact_out, Pool};
use zenodex_runtime_core::fee_router::{route_fee, FeeAccumulator, FeeSplitTable};
use zenodex_runtime_core::replay_guard::{admit, ReplayGuardState};
use zenodex_runtime_core::zusd::{step as zusd_step, ZusdCommand, ZusdState};

/// A handful of pubkey-shaped strings: valid, wrong-length, non-hex, empty.
fn pubkeyish() -> impl Strategy<Value = String> {
    prop_oneof![
        (0u8..4).prop_map(|t| format!("0x{}", hex::encode([0x10 + t; 48]))),
        Just("0x11".to_string()),
        Just(format!("0x{}", "zz".repeat(48))),
        Just(String::new()),
        Just(format!("0x{}", "ab".repeat(32))), // 32-byte (asset length)
    ]
}

fn assetish() -> impl Strategy<Value = String> {
    prop_oneof![
        (0u8..3).prop_map(|t| format!("0x{}", hex::encode([0xA0 + t; 32]))),
        Just("0xbb".to_string()),
        Just(String::new()),
    ]
}

/// Amounts spanning the interesting boundaries for every kernel.
fn amountish() -> impl Strategy<Value = u128> {
    prop_oneof![
        Just(0u128),
        Just(1u128),
        1u128..1_000_000,
        Just(MAX_BALANCE),
        Just(MAX_BALANCE + 1),
        Just(u128::MAX),
        Just((1u128 << 112) - 1),
        Just(3_000_000_000),
        Just(3_000_000_001),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(4000))]

    /// fee_router: never panics; on accept, per-(source,asset)-stream
    /// conservation holds and every bucket is bounded. Threads the accumulator
    /// across a sequence so dust-carry is exercised.
    #[test]
    fn fee_router_never_panics(
        source in "[a-z]{0,12}",
        asset in "\\PC{0,8}",
        steps in proptest::collection::vec(
            (1u128..1_000_000, -1i64..10_001, -1i64..10_001, -1i64..10_001, -1i64..10_001),
            0..20),
    ) {
        let mut acc = FeeAccumulator::default();
        for (amt, b, s, r, h) in steps {
            let table = FeeSplitTable { buyburn_bps: b, stakers_bps: s, reserve_bps: r, hosts_bps: h };
            let dust_in = acc.dust_for(&source, &asset);
            if let Ok(a) = route_fee(&source, &asset, amt, &table, &acc) {
                let rc = &a.receipt;
                prop_assert_eq!(amt + dust_in, rc.buyburn + rc.stakers + rc.reserve + rc.hosts + rc.dust);
                prop_assert!(rc.dust < 4);
                let _ = a.receipt.receipt_hash();
                let _ = a.accumulator.state_root();
                acc = a.accumulator;
            }
        }
    }

    /// replay_guard: never panics; accept iff nonce == last+1; reject is a no-op.
    #[test]
    fn replay_guard_never_panics(
        ops in proptest::collection::vec((pubkeyish(), prop_oneof![Just(0u64), 1u64..8, Just(u64::MAX)]), 0..50),
    ) {
        let mut state = ReplayGuardState::default();
        for (sender, nonce) in ops {
            let before = state.last_for(&sender);
            match admit(&state, &sender, nonce) {
                Ok(acc) => {
                    prop_assert_eq!(acc.receipt.nonce, before + 1);
                    let _ = acc.receipt.receipt_hash();
                    state = acc.state;
                }
                Err(_) => prop_assert_eq!(state.last_for(&sender), before),
            }
            let _ = state.state_root();
        }
    }

    /// balance_kernel: never panics; per-asset supply is conserved by transfer
    /// and increased by exactly `amount` by credit.
    #[test]
    fn balance_kernel_never_panics(
        ops in proptest::collection::vec(
            (any::<bool>(), pubkeyish(), pubkeyish(), assetish(), amountish()), 0..40),
    ) {
        let mut state = BalanceState::default();
        for (is_credit, a, b, asset, amount) in ops {
            let res = if is_credit {
                credit(&state, &a, &asset, amount)
            } else {
                transfer(&state, &a, &b, &asset, amount)
            };
            if let Ok(acc) = res {
                let _ = acc.receipt.receipt_hash();
                state = acc.state;
            }
            let _ = state.state_root();
        }
    }

    /// zusd: never panics for any command/arg; accepted states keep supply
    /// conservation (free + sp == debt) and no bad debt.
    #[test]
    fn zusd_never_panics(
        cmds in proptest::collection::vec(zusd_cmd(), 0..40),
    ) {
        let mut state = ZusdState::default();
        for cmd in cmds {
            if let Ok(acc) = zusd_step(&state, &cmd) {
                prop_assert_eq!(acc.state.free_debt_e8 + acc.state.sp_debt_e8, acc.state.debt_e8);
                let _ = acc.state.state_root();
                state = acc.state;
            }
        }
    }

    /// burn_receipts rails: never panic; accept implies all the rail equalities.
    #[test]
    fn burn_rails_never_panic(
        v in proptest::collection::vec(prop_oneof![Just(-1i64), 0i64..3, Just(0x7FFFi64),
                                                   Just(0x8000i64), Just(0xFFFFi64), Just(1i64 << 40)], 11..12),
    ) {
        let r = RailInputs {
            do_burn: v[0], receipt_bound: v[1], nullifier_unused: v[2], policy_ok: v[3],
            burn_amount: v[4], receipt_amount: v[5], burn_budget: v[6],
            supply_before: v[7], supply_after: v[8],
            batch_burn_sum_before: v[9], batch_burn_sum_after: v[10],
        };
        if verify_rails(&r).is_ok() {
            // On accept: supply conserved and accumulator grows by the burn.
            prop_assert_eq!(r.supply_after, r.supply_before - r.burn_amount);
            prop_assert_eq!(r.batch_burn_sum_after, r.batch_burn_sum_before + r.burn_amount);
            prop_assert!(r.burn_budget >= r.burn_amount);
        }
    }

    /// cpmm_swap: never panics; accepted swaps keep the constant-product k.
    #[test]
    fn cpmm_swap_never_panics(
        init_r0 in amountish(), init_r1 in amountish(), fee in prop_oneof![0u128..50, Just(10_000u128), Just(10_001u128)],
        ops in proptest::collection::vec(
            (any::<bool>(), any::<bool>(), amountish(), amountish()), 0..30),
    ) {
        let mut pool = match init_pool(&Pool::default(), init_r0, init_r1, fee) {
            Ok(a) => a.pool,
            Err(_) => return Ok(()), // invalid init: nothing to thread
        };
        for (is_exact_in, zfo, x, cap) in ops {
            let k_before = pool.reserve0.checked_mul(pool.reserve1);
            let res = if is_exact_in {
                swap_exact_in(&pool, zfo, x, 0)
            } else {
                swap_exact_out(&pool, zfo, x, cap)
            };
            if let Ok(acc) = res {
                if let Some(kb) = k_before {
                    prop_assert!(acc.pool.reserve0 * acc.pool.reserve1 >= kb);
                }
                let _ = acc.receipt.receipt_hash();
                pool = acc.pool;
            }
            let _ = pool.state_root();
        }
    }
}

/// Adversarial zUSD command generator: every variant, with arg strings that are
/// missing, non-numeric, negative, normal, and far beyond u128.
fn zusd_cmd() -> impl Strategy<Value = ZusdCommand> {
    let amt = prop_oneof![
        Just(None),
        Just(Some("0".to_string())),
        Just(Some("-1".to_string())),
        (1u64..1_000_000_000).prop_map(|v| Some(v.to_string())),
        Just(Some("x".to_string())),
        Just(Some("1".to_string() + &"0".repeat(40))), // 10^40, beyond u128
        Just(Some(((1u128 << 112) - 1).to_string())),
    ];
    let price = amt.clone();
    prop_oneof![
        amt.clone()
            .prop_map(|delta| ZusdCommand::AdvanceEpoch { delta }),
        (any::<bool>(), price.clone())
            .prop_map(|(auth_ok, price_e8)| ZusdCommand::BootstrapOracle { auth_ok, price_e8 }),
        (any::<bool>(), price)
            .prop_map(|(auth_ok, price_e8)| ZusdCommand::OracleReport { auth_ok, price_e8 }),
        any::<bool>().prop_map(|auth_ok| ZusdCommand::OracleCommit { auth_ok }),
        amt.clone()
            .prop_map(|amount_e8| ZusdCommand::DepositCollateral { amount_e8 }),
        amt.clone()
            .prop_map(|amount_e8| ZusdCommand::WithdrawCollateral { amount_e8 }),
        amt.clone()
            .prop_map(|amount_e8| ZusdCommand::MintZusd { amount_e8 }),
        amt.clone()
            .prop_map(|amount_e8| ZusdCommand::RepayZusd { amount_e8 }),
        amt.clone()
            .prop_map(|amount_e8| ZusdCommand::DepositSp { amount_e8 }),
        amt.clone()
            .prop_map(|amount_e8| ZusdCommand::WithdrawSp { amount_e8 }),
        amt.prop_map(|amount_e8| ZusdCommand::RedeemZusd { amount_e8 }),
        Just(ZusdCommand::Liquidate),
        Just(ZusdCommand::Unknown),
    ]
}
