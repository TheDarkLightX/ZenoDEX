// Reuse the retained governed fixture and retain both genuine receipts.
include!("real_composition.rs");

use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;

use risc0_zkvm::{compute_image_id, FakeReceipt, ReceiptClaim};
use zenodex_asset_lane_coordinator_risc0_shared::canonical_asset_lane_coordinator_guest_input_bytes_v1;
use zenodex_asset_transfer_module_risc0_methods::ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF;

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
#[ignore = "exports genuine module and coordinator receipts; remote job only"]
fn export_real_asset_lane_bridge_receipts_v1() {
    assert_eq!(std::env::var("RISC0_DEV_MODE").as_deref(), Ok("0"));
    assert_eq!(std::env::var("RISC0_PROVER").as_deref(), Ok("local"));
    assert!(std::env::var_os("RISC0_SKIP_BUILD").is_none());
    let directory = std::env::var_os("ZENODEX_ASSET_LANE_RECEIPT_OUTPUT").unwrap();
    let directory = Path::new(&directory);
    assert!(directory.is_absolute());
    std::fs::create_dir(directory).unwrap();

    let (fixture, prepared, lane_image_root) = arrange_release_aware_lane_v1();
    let binding = bind_release_route_v1(&fixture, &prepared);
    let module =
        prove_asset_transfer_module_succinct_v1(&fixture.guest_input.module_input).unwrap();
    let structural = verify_module_and_compose_v1(&fixture, &prepared, &binding, &module);
    let lane =
        prove_asset_lane_coordinator_succinct_v1(&fixture.guest_input, module.clone()).unwrap();
    let lane_bytes = encode_asset_lane_coordinator_receipt_v1(&lane).unwrap();
    let verified = verify_lane_v1(&fixture, &prepared, &structural, &lane_bytes);
    assert_eq!(verified.expected_image_id(), &lane_image_root);
    assert_eq!(lane.journal.bytes, prepared.lane_journal_bytes);
    assert_eq!(module.journal.bytes, prepared.module_journal_bytes);
    module
        .verify(ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID)
        .unwrap();
    lane.verify(ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID)
        .unwrap();
    assert_eq!(
        compute_image_id(ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF)
            .unwrap()
            .as_words(),
        ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID
    );

    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID,
        lane.journal.bytes.clone(),
    ))
    .try_into()
    .unwrap();
    let mut corrupt = lane.clone();
    let InnerReceipt::Succinct(ref mut succinct) = corrupt.inner else {
        panic!("succinct required");
    };
    succinct.seal[0] ^= 1;
    assert!(corrupt
        .verify(ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID)
        .is_err());
    for (name, bytes) in [
        (
            "module.receipt.json",
            encode_asset_transfer_module_receipt_v1(&module).unwrap(),
        ),
        ("lane.receipt.json", lane_bytes),
        (
            "fake.receipt.json",
            encode_asset_lane_coordinator_receipt_v1(&fake).unwrap(),
        ),
        (
            "corrupt_seal.receipt.json",
            encode_asset_lane_coordinator_receipt_v1(&corrupt).unwrap(),
        ),
        (
            "lane.input.json",
            canonical_asset_lane_coordinator_guest_input_bytes_v1(&fixture.guest_input).unwrap(),
        ),
        (
            "module.accepted.json",
            zenodex_global_settlement_abi_v1::canonical_bytes_v1(&prepared.module_accepted)
                .unwrap(),
        ),
        (
            "lane.accepted.json",
            zenodex_global_settlement_abi_v1::canonical_bytes_v1(&prepared.lane_accepted).unwrap(),
        ),
    ] {
        export_bytes(directory, name, &bytes);
    }
    export_bytes(directory, "module.journal", &prepared.module_journal_bytes);
    export_bytes(directory, "lane.journal", &prepared.lane_journal_bytes);
    export_bytes(
        directory,
        "module.elf",
        ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF,
    );
    export_bytes(
        directory,
        "lane.elf",
        ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF,
    );
    let fixture_context = serde_json::json!({
        "profile": fixture.profile, "lanes": fixture.lanes,
        "coordinators": fixture.coordinators, "routes": fixture.routes,
        "policy_registry": fixture.policy_registry,
        "asset_policy_registry": fixture.asset_policy_registry,
        "occurrence": fixture.occurrence,
        "authenticated_command_binding_root": fixture.authenticated_command.binding_root().unwrap(),
        "authentication_message_digest": fixture.authenticated_command.authentication_message_digest(),
    });
    export_bytes(
        directory,
        "fixture_context.json",
        &serde_json::to_vec(&fixture_context).unwrap(),
    );
    let metadata = serde_json::json!({
        "schema": "zenodex-asset-lane-coordinator-receipt-export-v1",
        "scope": "module_receipt_composition_given_governed_fixture",
        "receipt_codec": "native_serde_json",
        "module_image_words": ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID,
        "lane_image_words": ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ID,
        "lane_image_id": lane_image_root,
        "lane_elf_sha256": hex::encode(Sha256::digest(ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF)),
        "store_current_authority_qualified": false,
        "signature_authentication_qualified": false,
        "publication_authority": false,
        "whole_value_movement_safe": false,
    });
    export_bytes(
        directory,
        "proof_metadata.json",
        &serde_json::to_vec_pretty(&metadata).unwrap(),
    );
}
