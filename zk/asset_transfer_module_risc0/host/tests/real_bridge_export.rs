// Retain the existing accepted-transfer fixture and its native receipt codec.
include!("real_proof.rs");

use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;

use risc0_zkvm::{compute_image_id, FakeReceipt, Receipt, ReceiptClaim};
use zenodex_asset_transfer_module_risc0_shared::canonical_asset_transfer_guest_input_bytes_v1;

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
#[ignore = "exports a genuine economic module receipt; authorized remote job only"]
fn export_real_asset_transfer_bridge_receipt_v1() {
    assert_eq!(std::env::var("RISC0_DEV_MODE").as_deref(), Ok("0"));
    assert_eq!(std::env::var("RISC0_PROVER").as_deref(), Ok("local"));
    assert!(std::env::var_os("RISC0_SKIP_BUILD").is_none());
    let directory = std::env::var_os("ZENODEX_ASSET_MODULE_RECEIPT_OUTPUT").unwrap();
    let directory = Path::new(&directory);
    assert!(directory.is_absolute());
    std::fs::create_dir(directory).unwrap();

    let input = module_input();
    let prepared = prepare_asset_transfer_module_v1(input.clone()).unwrap();
    let receipt = prove_asset_transfer_module_succinct_v1(&input).unwrap();
    assert!(matches!(&receipt.inner, InnerReceipt::Succinct(_)));
    receipt
        .verify(ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID)
        .unwrap();
    assert_eq!(receipt.journal.bytes, prepared.journal_bytes);
    assert_eq!(
        compute_image_id(ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF)
            .unwrap()
            .as_words(),
        ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID
    );
    let encoded = encode_asset_transfer_module_receipt_v1(&receipt).unwrap();
    let image = asset_transfer_module_image_root_v1().unwrap();
    PinnedAssetTransferModuleReceiptVerifierV1
        .verify_succinct_receipt(&encoded, &image, &prepared.journal_bytes)
        .unwrap();

    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID,
        receipt.journal.bytes.clone(),
    ))
    .try_into()
    .unwrap();
    let mut corrupt = receipt.clone();
    let InnerReceipt::Succinct(ref mut succinct) = corrupt.inner else {
        panic!("succinct required");
    };
    succinct.seal[0] ^= 1;
    assert!(corrupt
        .verify(ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID)
        .is_err());
    export_bytes(directory, "module.receipt.json", &encoded);
    export_bytes(
        directory,
        "fake.receipt.json",
        &encode_asset_transfer_module_receipt_v1(&fake).unwrap(),
    );
    export_bytes(
        directory,
        "corrupt_seal.receipt.json",
        &encode_asset_transfer_module_receipt_v1(&corrupt).unwrap(),
    );
    export_bytes(directory, "module.journal", &prepared.journal_bytes);
    export_bytes(
        directory,
        "module.elf",
        ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF,
    );
    export_bytes(
        directory,
        "module.input.json",
        &canonical_asset_transfer_guest_input_bytes_v1(&input).unwrap(),
    );
    export_bytes(
        directory,
        "module.accepted.json",
        &zenodex_global_settlement_abi_v1::canonical_bytes_v1(&prepared.accepted).unwrap(),
    );
    let metadata = serde_json::json!({
        "schema": "zenodex-asset-transfer-module-receipt-export-v1",
        "scope": "accepted_transfer_computation_given_fixture_context_and_prestate",
        "receipt_codec": "native_serde_json",
        "module_image_id": image,
        "module_image_words": ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID,
        "module_elf_sha256": hex::encode(Sha256::digest(ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF)),
        "input_authenticity_qualified": false,
        "publication_authority": false,
        "whole_value_movement_safe": false,
    });
    export_bytes(
        directory,
        "proof_metadata.json",
        &serde_json::to_vec_pretty(&metadata).unwrap(),
    );
}
