#![no_std]

extern crate alloc;

use risc0_zkvm::guest::env;
use tau_state_proof_risc0_shared::{
    txs_commitment_v1, DexStateV1, StateProofInputV1, StateProofJournalV1, JOURNAL_VERSION,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let input: StateProofInputV1 = env::read();

    let mut state = DexStateV1::from_snapshot(input.pre_state)
        .expect("invalid pre_state (snapshot decode/validation failed)");

    let computed_pre = state.canonical_app_hash_sha256();
    if input.pre_app_hash_present {
        assert_eq!(
            computed_pre, input.pre_app_hash,
            "pre_app_hash mismatch (pre_state hash does not match expected)"
        );
    }

    let txs_commitment = txs_commitment_v1(&input.txs);
    for tx in &input.txs {
        state
            .apply_tx(tx, input.block_timestamp)
            .expect("tx rejected by tauswap proof transition");
    }

    // Final native sync to match the app-bridge behavior.
    state.sync_native_balances_post(&input.chain_balances_post);

    let post = state.canonical_app_hash_sha256();
    assert_eq!(
        post, input.expected_post_app_hash,
        "post_app_hash mismatch (computed app hash does not match expected)"
    );

    let journal = StateProofJournalV1 {
        journal_version: JOURNAL_VERSION,
        state_hash: input.state_hash,
        txs_commitment,
        pre_app_hash_present: input.pre_app_hash_present,
        pre_app_hash: input.pre_app_hash,
        post_app_hash: post,
    };
    env::commit(&journal);
}
