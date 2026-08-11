use std::time::Instant;

use risc0_zkvm::InnerReceipt;
use sha2::{Digest, Sha256};
use zenodex_asset_transfer_module_risc0_host::{
    asset_transfer_module_image_root_v1, encode_asset_transfer_module_receipt_v1,
    prove_asset_transfer_module_succinct_v1, verify_asset_transfer_module_receipt_v1,
    AssetTransferModuleHostErrorV1, PinnedAssetTransferModuleReceiptVerifierV1,
};
use zenodex_asset_transfer_module_risc0_methods::{
    ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF, ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID,
};
use zenodex_asset_transfer_module_risc0_shared::prepare_asset_transfer_module_v1;
use zenodex_global_settlement_abi_v1::{
    AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1, AssetTransferLaneModuleInputV1,
    AssetTransferPolicyV1, AssetTransferStateV1, EconomicAmountV1,
    LaneModuleSuccinctReceiptVerifierV1, RootV1, ASSET_TRANSFER_COMMAND_KIND_V1,
    ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "real asset transfer proof root",
        false,
    )
    .unwrap()
}

fn module_input() -> AssetTransferLaneModuleInputV1 {
    AssetTransferLaneModuleInputV1 {
        schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: AssetTransferContextV1 {
            chain_id: "zeno-real-asset-transfer-proof".to_owned(),
            deployment_root: root(1),
            profile_root: root(2),
            writer_epoch: 7,
            module_release_id: root(3),
            command_occurrence_id: root(4),
            subject_id: "alice".to_owned(),
            grant_root: root(5),
        },
        pre_state: AssetTransferStateV1 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: root(3),
            policies: vec![AssetTransferPolicyV1 {
                asset: "USD".to_owned(),
                fee_owner: "treasury".to_owned(),
                transfer_fee_atoms: 2,
                enabled: true,
            }],
            balances: vec![
                EconomicAmountV1 {
                    owner: "alice".to_owned(),
                    asset: "USD".to_owned(),
                    custody_domain: "accounts".to_owned(),
                    amount_atoms: 100,
                },
                EconomicAmountV1 {
                    owner: "bob".to_owned(),
                    asset: "USD".to_owned(),
                    custody_domain: "accounts".to_owned(),
                    amount_atoms: 10,
                },
                EconomicAmountV1 {
                    owner: "treasury".to_owned(),
                    asset: "USD".to_owned(),
                    custody_domain: "accounts".to_owned(),
                    amount_atoms: 5,
                },
            ],
            supplies: vec![AssetSupplyV1 {
                asset: "USD".to_owned(),
                amount_atoms: 115,
            }],
        },
        command: AssetTransferCommandV1 {
            command_kind: ASSET_TRANSFER_COMMAND_KIND_V1.to_owned(),
            asset: "USD".to_owned(),
            sender: "alice".to_owned(),
            recipient: "bob".to_owned(),
            amount_atoms: 30,
            max_fee_atoms: 2,
        },
        asset_policy_registry_root: root(11),
        fee_policy_registry_root: root(12),
        custody: vec![],
    }
}

#[test]
#[ignore = "generates one real ASSET_TRANSFER RISC0 Succinct receipt"]
fn real_asset_transfer_transition_proves_the_exact_module_journal() {
    // Arrange
    assert!(!ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF.is_empty());
    assert_ne!(ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID, [0; 8]);
    let input = module_input();
    let prepared = prepare_asset_transfer_module_v1(input.clone()).unwrap();
    let started = Instant::now();

    // Act
    let receipt = prove_asset_transfer_module_succinct_v1(&input).unwrap();
    let elapsed = started.elapsed();
    let image_root = asset_transfer_module_image_root_v1().unwrap();
    let receipt_bytes = encode_asset_transfer_module_receipt_v1(&receipt).unwrap();

    // Assert
    assert!(matches!(&receipt.inner, InnerReceipt::Succinct(_)));
    assert_eq!(receipt.journal.bytes, prepared.journal_bytes);
    PinnedAssetTransferModuleReceiptVerifierV1
        .verify_succinct_receipt(&receipt_bytes, &image_root, &prepared.journal_bytes)
        .unwrap();
    let mut wrong_journal = prepared.journal_bytes.clone();
    wrong_journal[0] ^= 1;
    assert!(matches!(
        verify_asset_transfer_module_receipt_v1(&receipt, &wrong_journal),
        Err(AssetTransferModuleHostErrorV1::ReceiptJournal)
    ));
    assert!(PinnedAssetTransferModuleReceiptVerifierV1
        .verify_succinct_receipt(&receipt_bytes, &root(99), &prepared.journal_bytes)
        .is_err());

    let embedded_method_sha256 =
        hex::encode(Sha256::digest(ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ELF));
    println!("asset transfer guest image words: {ZENODEX_ASSET_TRANSFER_MODULE_GUEST_ID:?}");
    println!("asset transfer guest image root: {image_root}");
    println!("asset transfer embedded method sha256: {embedded_method_sha256}");
    println!("asset transfer real proof elapsed: {elapsed:?}");
}
