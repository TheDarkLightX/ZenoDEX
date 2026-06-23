#![no_main]
//! libFuzzer target: CPMM settlement swaps must never panic; every accepted
//! swap preserves the constant-product invariant (k never decreases).

use libfuzzer_sys::fuzz_target;
use zenodex_runtime_core::cpmm_swap::{init_pool, swap_exact_in, swap_exact_out, Pool};

#[derive(arbitrary::Arbitrary, Debug)]
struct Input {
    r0: u128,
    r1: u128,
    fee_bps: u128,
    ops: Vec<(bool, bool, u128, u128)>,
}

fuzz_target!(|input: Input| {
    let mut pool = match init_pool(&Pool::default(), input.r0, input.r1, input.fee_bps) {
        Ok(a) => a.pool,
        Err(_) => return,
    };
    for (is_exact_in, zfo, x, cap) in input.ops.into_iter().take(64) {
        let k_before = pool.reserve0.checked_mul(pool.reserve1);
        let res = if is_exact_in {
            swap_exact_in(&pool, zfo, x, 0)
        } else {
            swap_exact_out(&pool, zfo, x, cap)
        };
        if let Ok(acc) = res {
            if let Some(kb) = k_before {
                assert!(acc.pool.reserve0 * acc.pool.reserve1 >= kb);
            }
            let _ = acc.receipt.receipt_hash();
            pool = acc.pool;
        }
        let _ = pool.state_root();
    }
});
