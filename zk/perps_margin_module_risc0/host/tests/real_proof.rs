use std::time::Instant;

use risc0_zkvm::InnerReceipt;

#[path = "support/mod.rs"]
mod support;

use support::{module_input, root};
use zenodex_global_settlement_abi_v1::{AbiErrorV1, LaneModuleSuccinctReceiptVerifierV1};
use zenodex_perps_margin_module_risc0_host::{
    decode_canonical_perps_margin_module_receipt_v1, encode_perps_margin_module_receipt_v1,
    perps_margin_module_image_root_v1, prove_perps_margin_module_succinct_v1,
    verify_perps_margin_module_receipt_v1, PerpsMarginModuleHostErrorV1,
    PinnedPerpsMarginModuleReceiptVerifierV1,
};
use zenodex_perps_margin_module_risc0_methods::{
    ZENODEX_PERPS_MARGIN_MODULE_GUEST_ELF, ZENODEX_PERPS_MARGIN_MODULE_GUEST_ID,
};
use zenodex_perps_margin_module_risc0_shared::prepare_perps_margin_module_v1;

#[test]
#[ignore = "requires a real RISC0 method build and sustained succinct proving"]
fn real_perps_margin_module_receipt_verifies_exact_image_and_journal() {
    // Arrange.
    assert!(!ZENODEX_PERPS_MARGIN_MODULE_GUEST_ELF.is_empty());
    assert_ne!(ZENODEX_PERPS_MARGIN_MODULE_GUEST_ID, [0; 8]);
    let input = module_input(100);
    let prepared = prepare_perps_margin_module_v1(input.clone()).unwrap();

    // Act.
    let started = Instant::now();
    let receipt = prove_perps_margin_module_succinct_v1(&input).unwrap();

    // Assert.
    assert!(matches!(receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(receipt.journal.bytes, prepared.journal_bytes);
    verify_perps_margin_module_receipt_v1(&receipt, &prepared.journal_bytes).unwrap();
    let receipt_bytes = encode_perps_margin_module_receipt_v1(&receipt).unwrap();
    PinnedPerpsMarginModuleReceiptVerifierV1
        .verify_succinct_receipt(
            &receipt_bytes,
            &perps_margin_module_image_root_v1().unwrap(),
            &prepared.journal_bytes,
        )
        .unwrap();

    let mut wrong_journal = prepared.journal_bytes.clone();
    wrong_journal[0] ^= 1;
    assert!(matches!(
        verify_perps_margin_module_receipt_v1(&receipt, &wrong_journal),
        Err(PerpsMarginModuleHostErrorV1::ReceiptJournal)
    ));
    assert!(matches!(
        PinnedPerpsMarginModuleReceiptVerifierV1.verify_succinct_receipt(
            &receipt_bytes,
            &root(99),
            &prepared.journal_bytes,
        ),
        Err(AbiErrorV1::InvalidBinding("perps margin RISC0 image"))
    ));
    let pretty_receipt = serde_json::to_vec_pretty(&receipt).unwrap();
    assert!(matches!(
        decode_canonical_perps_margin_module_receipt_v1(&pretty_receipt),
        Err(PerpsMarginModuleHostErrorV1::ReceiptNonCanonical)
    ));
    println!(
        "perps margin module image={} elapsed={:?}",
        perps_margin_module_image_root_v1().unwrap(),
        started.elapsed()
    );
}
