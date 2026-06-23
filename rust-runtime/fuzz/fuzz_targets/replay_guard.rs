#![no_main]
//! libFuzzer target: replay_guard::admit must never panic; accept iff nonce ==
//! last+1; rejection never advances state.

use libfuzzer_sys::fuzz_target;
use zenodex_runtime_core::replay_guard::{admit, ReplayGuardState};

fuzz_target!(|ops: Vec<(String, u64)>| {
    let mut state = ReplayGuardState::default();
    for (sender, nonce) in ops.into_iter().take(128) {
        let before = state.last_for(&sender);
        match admit(&state, &sender, nonce) {
            Ok(acc) => {
                assert_eq!(acc.receipt.sequence, before + 1);
                let _ = acc.receipt.receipt_hash();
                state = acc.state;
            }
            Err(_) => assert_eq!(state.last_for(&sender), before),
        }
        let _ = state.state_root();
    }
});
