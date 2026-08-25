use std::time::Instant;

use risc0_zkvm::InnerReceipt;

#[path = "support/mod.rs"]
mod support;

use support::module_input;
use zenodex_perps_margin_module_risc0_host::{
    perps_margin_module_image_root_v1, prove_perps_margin_module_succinct_v1,
    verify_perps_margin_module_receipt_v1,
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
    println!(
        "perps margin module image={} elapsed={:?}",
        perps_margin_module_image_root_v1().unwrap(),
        started.elapsed()
    );
}
