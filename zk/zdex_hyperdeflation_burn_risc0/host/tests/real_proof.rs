mod support;

use std::time::Instant;

use risc0_zkvm::InnerReceipt;
use sha2::{Digest, Sha256};
use support::{guest_input, root};
use zenodex_global_settlement_abi_v1::ZDEXLaneSuccinctReceiptVerifierV1;
use zenodex_zdex_hyperdeflation_burn_risc0_host::{
    encode_zdex_hyperdeflation_burn_receipt_v1, prove_zdex_hyperdeflation_burn_succinct_v1,
    verify_zdex_hyperdeflation_burn_receipt_v1, zdex_hyperdeflation_burn_image_root_v1,
    PinnedZDEXHyperdeflationBurnReceiptVerifierV1, ZDEXHyperdeflationBurnHostErrorV1,
};
use zenodex_zdex_hyperdeflation_burn_risc0_methods::{
    ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ELF, ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ID,
};
use zenodex_zdex_hyperdeflation_burn_risc0_shared::prepare_zdex_hyperdeflation_burn_v1;

#[test]
#[ignore = "generates one real ZDEX hyperdeflation burn RISC0 Succinct receipt"]
fn real_zdex_hyperdeflation_burn_proves_the_exact_journal() {
    // Arrange
    assert!(!ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ELF.is_empty());
    assert_ne!(ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ID, [0; 8]);
    let input = guest_input(100);
    let prepared = prepare_zdex_hyperdeflation_burn_v1(input.clone()).unwrap();
    let started = Instant::now();

    // Act
    let receipt = prove_zdex_hyperdeflation_burn_succinct_v1(&input).unwrap();
    let elapsed = started.elapsed();
    let image_root = zdex_hyperdeflation_burn_image_root_v1().unwrap();
    let receipt_bytes = encode_zdex_hyperdeflation_burn_receipt_v1(&receipt).unwrap();

    // Assert
    assert!(matches!(&receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(receipt.journal.bytes, prepared.journal_bytes);
    PinnedZDEXHyperdeflationBurnReceiptVerifierV1
        .verify_succinct_receipt(&receipt_bytes, &image_root, &prepared.journal_bytes)
        .unwrap();
    let mut wrong_journal = prepared.journal_bytes.clone();
    wrong_journal[0] ^= 1;
    assert!(matches!(
        verify_zdex_hyperdeflation_burn_receipt_v1(&receipt, &wrong_journal),
        Err(ZDEXHyperdeflationBurnHostErrorV1::ReceiptJournal)
    ));
    assert!(PinnedZDEXHyperdeflationBurnReceiptVerifierV1
        .verify_succinct_receipt(&receipt_bytes, &root(99), &prepared.journal_bytes)
        .is_err());

    let embedded_method_sha256 =
        hex::encode(Sha256::digest(ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ELF));
    println!(
        "ZDEX hyperdeflation burn guest image words: {ZENODEX_ZDEX_HYPERDEFLATION_BURN_GUEST_ID:?}"
    );
    println!("ZDEX hyperdeflation burn guest image root: {image_root}");
    println!("ZDEX hyperdeflation burn embedded method sha256: {embedded_method_sha256}");
    println!("ZDEX hyperdeflation burn real proof elapsed: {elapsed:?}");
}
