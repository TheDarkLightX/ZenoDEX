mod support;

use std::time::Instant;

use risc0_zkvm::InnerReceipt;
use support::{guest_input, root};
use zenodex_economic_initial_state_risc0_host::{
    certify_economic_initial_state_receipt_v1, decode_canonical_economic_initial_state_receipt_v1,
    economic_initial_state_image_root_v1, encode_economic_initial_state_receipt_v1,
    prove_economic_initial_state_succinct_with_metrics_v1,
    verify_economic_initial_state_receipt_v1, EconomicInitialStateHostErrorV1,
};
use zenodex_economic_initial_state_risc0_methods::{
    ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ELF, ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ID,
};
use zenodex_economic_initial_state_risc0_shared::prepare_economic_initial_state_v1;
use zenodex_global_settlement_abi_v1::{hash_bytes_sha256_v1, MAX_CYCLE_BUDGET_V1};

#[test]
#[ignore = "generates and replays one real economic initial-state RISC0 Succinct receipt"]
fn real_economic_initial_state_proves_and_replays_the_exact_journal() {
    // Arrange
    assert!(!ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ELF.is_empty());
    assert_ne!(ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ID, [0; 8]);
    let image_root = economic_initial_state_image_root_v1().unwrap();
    let input = guest_input(image_root.clone());
    let prepared = prepare_economic_initial_state_v1(input.clone()).unwrap();
    let started = Instant::now();

    // Act
    let proof = prove_economic_initial_state_succinct_with_metrics_v1(&input).unwrap();
    let elapsed = started.elapsed();
    let receipt_bytes = encode_economic_initial_state_receipt_v1(proof.receipt()).unwrap();
    let replayed_receipt =
        decode_canonical_economic_initial_state_receipt_v1(&receipt_bytes).unwrap();
    verify_economic_initial_state_receipt_v1(&replayed_receipt, prepared.journal_bytes()).unwrap();
    let certified = certify_economic_initial_state_receipt_v1(
        &prepared,
        &replayed_receipt,
        MAX_CYCLE_BUDGET_V1,
    )
    .unwrap();

    // Assert
    assert!(matches!(&replayed_receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(replayed_receipt.journal.bytes, prepared.journal_bytes());
    assert_eq!(certified.receipt_bytes, receipt_bytes);
    assert_eq!(certified.certificate.root_image_id, image_root);
    assert!(proof.metrics().segments > 0);
    assert!(proof.metrics().total_cycles > 0);
    // SessionStats are diagnostic only; this catches an obviously oversized run.
    assert!(proof.metrics().total_cycles <= MAX_CYCLE_BUDGET_V1);

    let mut wrong_journal = prepared.journal_bytes().to_vec();
    wrong_journal[0] ^= 1;
    assert!(matches!(
        verify_economic_initial_state_receipt_v1(&replayed_receipt, &wrong_journal),
        Err(EconomicInitialStateHostErrorV1::ReceiptJournal)
    ));
    let mut wrong_image_receipt = replayed_receipt.clone();
    let mut wrong_image_statement = input.statement.clone();
    wrong_image_statement.root_image_id = root(98);
    wrong_image_receipt.journal.bytes = wrong_image_statement.canonical_bytes().unwrap();
    assert!(matches!(
        verify_economic_initial_state_receipt_v1(
            &wrong_image_receipt,
            &wrong_image_receipt.journal.bytes,
        ),
        Err(EconomicInitialStateHostErrorV1::MethodBinding)
    ));
    let mut corrupted_proof_receipt = replayed_receipt.clone();
    let InnerReceipt::Succinct(corrupted_proof) = &mut corrupted_proof_receipt.inner else {
        unreachable!("the accepted real receipt kind was already checked as Succinct")
    };
    assert!(!corrupted_proof.seal.is_empty());
    corrupted_proof.seal[0] ^= 1;
    assert!(matches!(
        verify_economic_initial_state_receipt_v1(
            &corrupted_proof_receipt,
            prepared.journal_bytes(),
        ),
        Err(EconomicInitialStateHostErrorV1::ReceiptVerification)
    ));
    let mut wrong_input = input;
    wrong_input.profile.root_image_id = root(99);
    assert!(matches!(
        prove_economic_initial_state_succinct_with_metrics_v1(&wrong_input),
        Err(EconomicInitialStateHostErrorV1::MethodBinding)
    ));

    let report = serde_json::json!({
        "schema": "zenodex/economic-initial-state-real-proof-report/v1",
        "status": "REAL_RECEIPT_REPLAY_TEST_ONLY",
        "production_authority": "NONE",
        "receipt_kind": "SUCCINCT",
        "guest_image_words": ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ID,
        "guest_image_root": image_root.as_str(),
        "embedded_method_sha256": hash_bytes_sha256_v1(
            ZENODEX_ECONOMIC_INITIAL_STATE_GUEST_ELF,
        ),
        "receipt_sha256": hash_bytes_sha256_v1(&receipt_bytes),
        "journal_bytes": prepared.journal_bytes().len(),
        "receipt_bytes": receipt_bytes.len(),
        "segments": proof.metrics().segments,
        "total_cycles": proof.metrics().total_cycles,
        "user_cycles": proof.metrics().user_cycles,
        "paging_cycles": proof.metrics().paging_cycles,
        "reserved_cycles": proof.metrics().reserved_cycles,
        "elapsed_milliseconds": elapsed.as_millis(),
        "receipt_verified": true,
        "canonical_receipt_replayed": true,
    });
    println!("{}", serde_json::to_string(&report).unwrap());
}
