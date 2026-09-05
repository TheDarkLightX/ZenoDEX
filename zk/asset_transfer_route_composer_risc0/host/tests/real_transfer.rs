//! Isolated real module -> coordinator -> full-state route proof exporter.
//! Fixture profile labels and command bytes do not supply signer or writer authority.

#[path = "../../test_support/mod.rs"]
mod support;

use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
use zenodex_asset_lane_coordinator_risc0_host::{
    asset_lane_coordinator_image_root_v1, asset_transfer_module_image_root_v1,
    prove_asset_lane_coordinator_succinct_v1,
};
use zenodex_asset_lane_coordinator_risc0_methods::ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF;
use zenodex_asset_transfer_module_risc0_host::prove_asset_transfer_module_succinct_v1;
use zenodex_asset_transfer_module_risc0_methods::ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF;
use zenodex_asset_transfer_route_composer_risc0_host::*;
use zenodex_asset_transfer_route_composer_risc0_methods::{
    ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ELF, ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ID,
};
use zenodex_asset_transfer_route_composer_risc0_shared::*;
use zenodex_global_settlement_abi_v1::RootV1;

fn input() -> AssetTransferRouteGuestInputV1 {
    if let Some(path) = std::env::var_os("ZENODEX_ASSET_ROUTE_INPUT") {
        let bytes = std::fs::read(path).unwrap();
        return prepare_asset_transfer_route_from_bytes_v1(&bytes)
            .unwrap()
            .input()
            .clone();
    }
    let root_image = std::env::var("ZENODEX_ASSET_ROUTE_ROOT_IMAGE")
        .ok()
        .map(|value| RootV1::parse(value, "isolated root image", false).unwrap());
    let height = std::env::var("ZENODEX_ASSET_ROUTE_PRE_HEIGHT")
        .ok()
        .map(|value| value.parse::<u64>().unwrap())
        .unwrap_or(0);
    support::input_at(
        asset_transfer_module_image_root_v1().unwrap(),
        asset_lane_coordinator_image_root_v1().unwrap(),
        asset_transfer_route_image_root_v1().unwrap(),
        root_image,
        height,
    )
}

#[test]
#[ignore = "export exact measured-image fixture and pure preflight before final proving"]
fn export_measured_route_input_and_journals() {
    let input = input();
    let prepared = prepare_asset_transfer_route_v1(input.clone()).unwrap();
    let directory =
        std::path::PathBuf::from(std::env::var_os("ZENODEX_ASSET_ROUTE_EVIDENCE_DIR").unwrap());
    std::fs::create_dir_all(&directory).unwrap();
    for (name, bytes) in [
        (
            "route.input.json",
            canonical_asset_transfer_route_input_bytes_v1(&input).unwrap(),
        ),
        ("lane.journal", prepared.lane_journal_bytes().to_vec()),
        ("route.journal", prepared.route_journal_bytes().to_vec()),
    ] {
        std::fs::write(directory.join(name), bytes).unwrap();
    }
}

#[test]
#[ignore = "three genuine Succinct receipts; exact input/output files on authorized isolated prover"]
fn real_asset_transfer_module_coordinator_route_with_exact_export() {
    let input = input();
    let prepared = prepare_asset_transfer_route_v1(input.clone()).unwrap();
    let module = prove_asset_transfer_module_succinct_v1(&input.lane_input.module_input).unwrap();
    let coordinator =
        prove_asset_lane_coordinator_succinct_v1(&input.lane_input, module.clone()).unwrap();
    assert_eq!(coordinator.journal.bytes, prepared.lane_journal_bytes());
    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        prepared.coordinator_image(),
        coordinator.journal.bytes.clone(),
    ))
    .try_into()
    .unwrap();
    assert!(matches!(
        build_asset_transfer_route_executor_env_v1(&input, fake),
        Err(AssetTransferRouteHostErrorV1::ReceiptKind)
    ));
    let mut altered = coordinator.clone();
    altered.journal.bytes.push(0);
    assert!(matches!(
        build_asset_transfer_route_executor_env_v1(&input, altered),
        Err(AssetTransferRouteHostErrorV1::ReceiptJournal)
    ));
    let receipt = prove_asset_transfer_route_succinct_v1(&input, coordinator.clone()).unwrap();
    verify_asset_transfer_route_receipt_v1(&receipt, &prepared).unwrap();
    let mut wrong_context = input.clone();
    wrong_context.post_state.history_root = support::root(990);
    assert!(prepare_asset_transfer_route_v1(wrong_context).is_err());
    if let Some(directory) = std::env::var_os("ZENODEX_ASSET_ROUTE_EVIDENCE_DIR") {
        let directory = std::path::PathBuf::from(directory);
        std::fs::create_dir_all(&directory).unwrap();
        for (name, value) in [
            ("module", &module),
            ("coordinator", &coordinator),
            ("route", &receipt),
        ] {
            std::fs::write(
                directory.join(format!("{name}.receipt.json")),
                serde_json::to_vec(value).unwrap(),
            )
            .unwrap();
            std::fs::write(
                directory.join(format!("{name}.journal")),
                &value.journal.bytes,
            )
            .unwrap();
        }
        for (name, elf) in [
            ("module", ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF),
            ("coordinator", ZENODEX_ASSET_LANE_COORDINATOR_GUEST_ELF),
            ("route", ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ELF),
        ] {
            std::fs::write(directory.join(format!("{name}.elf")), elf).unwrap();
        }
        std::fs::write(
            directory.join("route.input.json"),
            canonical_asset_transfer_route_input_bytes_v1(&input).unwrap(),
        )
        .unwrap();
        std::fs::write(directory.join("subject.json"), serde_json::to_vec_pretty(&serde_json::json!({
            "route_image_words": ZENODEX_ASSET_TRANSFER_ROUTE_GUEST_ID,
            "projection_root": prepared.projection_root(), "refinement_root": prepared.refinement_root(),
            "pre_state_root": input.pre_state.state_root().unwrap(), "post_state_root": input.post_state.state_root().unwrap(),
            "signature_authority_verified": false, "initial_allocation_certified": false,
            "publication_qualified": false, "production_authority": false,
        })).unwrap()).unwrap();
    }
}
