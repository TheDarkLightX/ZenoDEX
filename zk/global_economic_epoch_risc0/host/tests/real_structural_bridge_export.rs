// Reuse the retained structural fixture without changing its proof statement.
// This test-only leaf commits supplied bytes; it proves no economic transition.
include!("real_composition.rs");

use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::path::Path;

use risc0_zkvm::{compute_image_id, FakeReceipt, ReceiptClaim};
use zenodex_global_economic_epoch_risc0_methods::ZENODEX_ECONOMIC_EPOCH_GUEST_ELF;

fn export_bytes(directory: &Path, name: &str, bytes: &[u8]) {
    assert!(!bytes.is_empty() && bytes.len() <= 16 * 1024 * 1024);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(directory.join(name))
        .unwrap();
    file.write_all(bytes).unwrap();
    file.sync_all().unwrap();
}

#[test]
#[ignore = "exports three genuine structural receipts; remote qualification only"]
fn export_real_structural_epoch_bridge_receipts_v1() {
    assert_eq!(std::env::var("RISC0_DEV_MODE").as_deref(), Ok("0"));
    assert_eq!(std::env::var("RISC0_PROVER").as_deref(), Ok("local"));
    assert!(std::env::var_os("RISC0_SKIP_BUILD").is_none());
    let directory = std::env::var_os("ZENODEX_STRUCTURAL_RECEIPT_OUTPUT").unwrap();
    let directory = Path::new(&directory);
    assert!(directory.is_absolute());
    std::fs::create_dir(directory).unwrap();

    let input = real_proof_input();
    let child = prove_structural_test_leaf(&input);
    let epoch = prove_economic_epoch_succinct_v1(&input, vec![child.clone()]).unwrap();
    epoch.verify(ZENODEX_ECONOMIC_EPOCH_GUEST_ID).unwrap();
    assert_eq!(epoch.journal.bytes, input.certificate_journal_bytes);

    // An independently valid proof of the SAME journal under the wrong image
    // must reach cryptographic image rejection, not merely journal rejection.
    let mut foreign_input = input.clone();
    foreign_input.route_receipts[0].journal_bytes = epoch.journal.bytes.clone();
    let foreign = prove_structural_test_leaf(&foreign_input);
    assert_eq!(foreign.journal.bytes, epoch.journal.bytes);
    assert!(foreign.verify(ZENODEX_ECONOMIC_EPOCH_GUEST_ID).is_err());

    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        ZENODEX_ECONOMIC_EPOCH_GUEST_ID,
        epoch.journal.bytes.clone(),
    ))
    .try_into()
    .unwrap();
    let mut corrupt = epoch.clone();
    let InnerReceipt::Succinct(ref mut succinct) = corrupt.inner else {
        panic!("real epoch must be succinct");
    };
    succinct.seal[0] ^= 1;
    assert!(corrupt.verify(ZENODEX_ECONOMIC_EPOCH_GUEST_ID).is_err());

    for (name, receipt) in [
        ("child.receipt", &child),
        ("epoch.receipt", &epoch),
        ("foreign_same_journal.receipt", &foreign),
        ("fake.receipt", &fake),
        ("corrupt_seal.receipt", &corrupt),
    ] {
        export_bytes(directory, name, &postcard::to_allocvec(receipt).unwrap());
    }
    for (name, elf, image) in [
        (
            "epoch.elf",
            ZENODEX_ECONOMIC_EPOCH_GUEST_ELF,
            ZENODEX_ECONOMIC_EPOCH_GUEST_ID,
        ),
        (
            "structural_leaf.elf",
            ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF,
            ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID,
        ),
    ] {
        assert_eq!(compute_image_id(elf).unwrap().as_words(), image);
        export_bytes(directory, name, elf);
    }
    export_bytes(directory, "epoch.journal", &epoch.journal.bytes);
    export_bytes(
        directory,
        "epoch.input.postcard",
        &postcard::to_allocvec(&input).unwrap(),
    );
    let metadata = serde_json::json!({
        "schema": "zenodex-structural-receipt-export-v1",
        "scope": "structural_recursive_receipt_and_verifier_bridge_only",
        "asset_transfer_semantics_proved": false,
        "publication_authority": false,
        "epoch_image_id": image_id_root_v1(ZENODEX_ECONOMIC_EPOCH_GUEST_ID).unwrap(),
        "foreign_image_id": image_id_root_v1(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID).unwrap(),
        "epoch_elf_sha256": sha256_root_v1(ZENODEX_ECONOMIC_EPOCH_GUEST_ELF),
        "foreign_elf_sha256": sha256_root_v1(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF),
        "epoch_journal_sha256": sha256_root_v1(&epoch.journal.bytes),
        "real_succinct_receipts": 3,
    });
    export_bytes(
        directory,
        "proof_metadata.json",
        &serde_json::to_vec_pretty(&metadata).unwrap(),
    );
}

#[test]
#[ignore = "exports a genuine foreign-image receipt for one bounded journal"]
fn export_real_foreign_journal_bridge_receipt_v1() {
    assert_eq!(std::env::var("RISC0_DEV_MODE").as_deref(), Ok("0"));
    assert_eq!(std::env::var("RISC0_PROVER").as_deref(), Ok("local"));
    assert!(std::env::var_os("RISC0_SKIP_BUILD").is_none());
    let journal_path = std::env::var_os("ZENODEX_FOREIGN_JOURNAL_PATH").unwrap();
    let mut journal = Vec::new();
    std::fs::File::open(journal_path)
        .unwrap()
        .take(1_048_577)
        .read_to_end(&mut journal)
        .unwrap();
    assert!(!journal.is_empty() && journal.len() <= 1_048_576);
    let directory = std::env::var_os("ZENODEX_FOREIGN_RECEIPT_OUTPUT").unwrap();
    let directory = Path::new(&directory);
    assert!(directory.is_absolute());
    std::fs::create_dir(directory).unwrap();

    // This quarantined leaf proves only that the supplied bytes were committed.
    // It supplies a real foreign-image negative, never an economic positive.
    let mut input = real_proof_input();
    input.route_receipts[0].journal_bytes = journal.clone();
    let foreign = prove_structural_test_leaf(&input);
    foreign
        .verify(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID)
        .unwrap();
    assert!(matches!(&foreign.inner, InnerReceipt::Succinct(_)));
    assert_eq!(foreign.journal.bytes, journal);
    assert_eq!(
        compute_image_id(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF)
            .unwrap()
            .as_words(),
        ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID
    );
    export_bytes(directory, "foreign.journal", &journal);
    export_bytes(
        directory,
        "foreign.receipt.json",
        &serde_json::to_vec(&foreign).unwrap(),
    );
    export_bytes(
        directory,
        "foreign.receipt.postcard",
        &postcard::to_allocvec(&foreign).unwrap(),
    );
    export_bytes(
        directory,
        "foreign.elf",
        ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ELF,
    );
    let metadata = serde_json::json!({
        "schema": "zenodex-foreign-journal-receipt-export-v1",
        "scope": "quarantined_structural_leaf_commits_supplied_journal_only",
        "foreign_image_id": image_id_root_v1(ZENODEX_ROUTE_STRUCTURAL_TEST_LEAF_ID).unwrap(),
        "journal_sha256": sha256_root_v1(&journal),
        "economic_semantics_proved": false,
        "publication_authority": false,
    });
    export_bytes(
        directory,
        "proof_metadata.json",
        &serde_json::to_vec_pretty(&metadata).unwrap(),
    );
}
