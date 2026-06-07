//! Stage 2 I3a: the RISC0 guest EXECUTES the CLOB matching-law transition.
//!
//! Runs the REAL guest ELF via `default_executor` (fast -- runs the program, no
//! STARK) on a `ZenoProofInputV1::Clob` input, then asserts the committed journal
//! decodes and equals the host-side `execute_clob_transition_v1` output. This
//! proves the guest dispatch + execute + commit_journal path end-to-end through
//! the ACTUAL guest binary, cheaply enough for CI.
//!
//! A full STARK (`default_prover`) is the slow, opt-in path (a separate smoke).
//! This is the low-cost guard for `methods/guest/src/main.rs` dispatch.

use risc0_zkvm::{default_executor, ExecutorEnv};
use tau_state_proof_risc0_methods::{
    TAU_STATE_PROOF_RISC0_GUEST_ELF, TAU_STATE_PROOF_RISC0_GUEST_ID,
};
use tau_state_proof_risc0_shared::clob::{
    execute_clob_transition_v1, execute_clob_transition_v1_unchecked_with_journal, ClobBookV1,
    ClobOrderV1, ClobTransitionInputV1, ClobTransitionJournalV1,
};
use tau_state_proof_risc0_shared::ZenoProofInputV1;

fn asset(b: &str) -> String {
    "0x".to_string() + &b.repeat(32)
}
fn owner(b: &str) -> String {
    "0x".to_string() + &b.repeat(48)
}
fn oid(n: u64) -> String {
    format!("0x{:064x}", n)
}

fn sample_input() -> ClobTransitionInputV1 {
    // SELL 5 @ 1.0 resting; BUY 5 @ 1.0 taker -> a full crossing fill.
    ClobTransitionInputV1 {
        state_hash: [7u8; 32],
        chain_id: "devnet".to_string(),
        risc0_image_id: TAU_STATE_PROOF_RISC0_GUEST_ID,
        pre_book: ClobBookV1::new(
            asset("11"),
            asset("22"),
            vec![ClobOrderV1 {
                side_code: 1,
                price_q_per_base: 100_000_000,
                base_qty: 5,
                sequence: 1,
                order_id: oid(1),
                owner: owner("bb"),
            }],
        ),
        taker: ClobOrderV1 {
            side_code: 0,
            price_q_per_base: 100_000_000,
            base_qty: 5,
            sequence: 10,
            order_id: oid(99),
            owner: owner("aa"),
        },
        pre_app_hash_present: false,
        pre_app_hash: [0u8; 32],
        expected_post_app_hash: [0u8; 32],
    }
}

#[test]
fn clob_guest_executes_transition_and_commits_bound_journal() {
    let mut input = sample_input();
    // REVIEW(Codex 2026-06-07, grade B -> A-): the first I3a test imported
    // stale method symbol names and sent a zero expected_post_app_hash into the
    // checked guest path. That tested neither compilation nor the real proof
    // envelope. Prime the expected post root from the unchecked host reference,
    // then execute the same checked transition the guest runs.
    let (expected_journal, _post) =
        execute_clob_transition_v1_unchecked_with_journal(input.clone()).expect("host transition");
    input.expected_post_app_hash = expected_journal.post_book_root;

    // Host-side reference journal (the shared kernel I1/I2/I2b verified vs Python).
    let host_journal = execute_clob_transition_v1(input.clone()).expect("checked host transition");

    // Run the REAL guest ELF (execute, not prove) on the same input.
    let guest_input = ZenoProofInputV1::Clob(input);
    let input_bytes = postcard::to_allocvec(&guest_input).expect("encode input");
    let input_len: u32 = input_bytes.len().try_into().expect("input fits u32");
    let env = ExecutorEnv::builder()
        .write_slice(&[input_len])
        .write_slice(&input_bytes)
        .build()
        .expect("env");
    let session = default_executor()
        .execute(env, TAU_STATE_PROOF_RISC0_GUEST_ELF)
        .expect("guest executes the clob transition");
    let guest_journal: ClobTransitionJournalV1 =
        postcard::from_bytes(&session.journal.bytes).expect("decode guest journal");

    // The guest's committed journal must equal the host transition: it really ran
    // the bound matching-law logic and committed the same roots + fills.
    assert_eq!(guest_journal.pre_book_root, host_journal.pre_book_root);
    assert_eq!(guest_journal.post_book_root, host_journal.post_book_root);
    assert_eq!(guest_journal.event_log_root, host_journal.event_log_root);
    assert_eq!(
        guest_journal.matching_rule_hash,
        host_journal.matching_rule_hash
    );
    assert_eq!(guest_journal.fee_rule_hash, host_journal.fee_rule_hash);
    assert_eq!(guest_journal.fee_total, 0);
    assert_eq!(guest_journal.fills, host_journal.fills);
    assert_eq!(
        guest_journal.resting_taker_qty,
        host_journal.resting_taker_qty
    );
    assert_eq!(
        guest_journal.fills.len(),
        1,
        "the sample taker fully fills one maker"
    );

    // Envelope binding (I3b): the guest commits proof_type, chain, state-hash, and
    // the image id the client pins for verifier-identity -- so a verifier can
    // strictly reject cross-surface / wrong-chain / wrong-image receipts.
    assert_eq!(guest_journal.proof_type, host_journal.proof_type);
    assert_eq!(guest_journal.chain_id, "devnet");
    assert_eq!(guest_journal.state_hash, host_journal.state_hash);
    assert_eq!(
        guest_journal.risc0_image_id, TAU_STATE_PROOF_RISC0_GUEST_ID,
        "guest journal must carry the pinned image id"
    );
}
