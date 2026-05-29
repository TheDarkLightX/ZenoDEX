#![no_main]
//! libFuzzer target: balance credit/transfer must never panic; accepted states
//! stay canonical (state_root must not panic).

use libfuzzer_sys::fuzz_target;
use zenodex_runtime_core::balance_kernel::{credit, transfer, BalanceState};

#[derive(arbitrary::Arbitrary, Debug)]
struct Op {
    is_credit: bool,
    a: String,
    b: String,
    asset: String,
    amount: u128,
}

fuzz_target!(|ops: Vec<Op>| {
    let mut state = BalanceState::default();
    for op in ops.into_iter().take(64) {
        let res = if op.is_credit {
            credit(&state, &op.a, &op.asset, op.amount)
        } else {
            transfer(&state, &op.a, &op.b, &op.asset, op.amount)
        };
        if let Ok(acc) = res {
            let _ = acc.receipt.receipt_hash();
            state = acc.state;
        }
        let _ = state.state_root();
    }
});
