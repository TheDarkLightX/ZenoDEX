use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
use zenodex_asset_lane_coordinator_risc0_host::{
    build_asset_lane_coordinator_executor_env_v1, prove_asset_lane_coordinator_succinct_v1,
    require_asset_lane_coordinator_receipt_bytes_len_v1, AssetLaneCoordinatorHostErrorV1,
    PinnedAssetLaneCoordinatorReceiptVerifierV1, MAX_ASSET_LANE_COORDINATOR_RECEIPT_BYTES_V1,
};
use zenodex_asset_lane_coordinator_risc0_shared::{
    prepare_asset_lane_coordinator_v1, AssetLaneCoordinatorGuestInputV1,
    ASSET_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1, ASSET_TRANSFER_MODULE_IMAGE_ID_V1,
};
use zenodex_global_settlement_abi_v1::{
    AbiErrorV1, AssetLaneCoordinatorContextV1, AssetLaneModuleCompatibilityV1, AssetSupplyV1,
    AssetTransferCommandV1, AssetTransferContextV1, AssetTransferLaneModuleInputV1,
    AssetTransferPolicyV1, AssetTransferStateV1, EconomicAmountV1,
    LaneCompositionSuccinctReceiptVerifierV1, RootV1, ASSET_LANE_COORDINATOR_SCHEMA_V1,
    ASSET_TRANSFER_COMMAND_KIND_V1, ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "asset lane host test root",
        false,
    )
    .unwrap()
}

fn guest_input() -> AssetLaneCoordinatorGuestInputV1 {
    let module_input = AssetTransferLaneModuleInputV1 {
        schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: AssetTransferContextV1 {
            chain_id: "zeno-asset-lane-host-test".to_owned(),
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
    };
    let coordinator_context = AssetLaneCoordinatorContextV1 {
        schema: ASSET_LANE_COORDINATOR_SCHEMA_V1.to_owned(),
        chain_id: "zeno-asset-lane-host-test".to_owned(),
        deployment_root: root(1),
        profile_root: root(2),
        writer_epoch: 7,
        coordinator_release_id: root(10),
        command_occurrence_id: root(4),
        asset_policy_registry_root: root(11),
        fee_policy_registry_root: root(12),
        compatible_modules: vec![AssetLaneModuleCompatibilityV1 {
            module_release_id: root(3),
            module_schema: ASSET_TRANSFER_MODULE_SCHEMA_V1.to_owned(),
        }],
    };
    AssetLaneCoordinatorGuestInputV1 {
        schema: ASSET_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1.to_owned(),
        module_input,
        coordinator_context,
    }
}

#[test]
fn placeholder_lane_method_and_fake_module_receipt_reject_before_authority() {
    // Arrange
    let input = guest_input();
    let prepared = prepare_asset_lane_coordinator_v1(input.clone()).unwrap();
    let fake: Receipt = FakeReceipt::new(ReceiptClaim::ok(
        ASSET_TRANSFER_MODULE_IMAGE_ID_V1,
        prepared.module_journal_bytes,
    ))
    .try_into()
    .unwrap();

    // Act / Assert
    assert!(matches!(
        build_asset_lane_coordinator_executor_env_v1(&input, fake.clone()),
        Err(AssetLaneCoordinatorHostErrorV1::ModuleReceiptKind)
    ));
    assert!(matches!(
        prove_asset_lane_coordinator_succinct_v1(&input, fake),
        Err(AssetLaneCoordinatorHostErrorV1::PlaceholderMethod)
    ));
}

#[test]
fn receipt_byte_ceiling_rejects_zero_and_maximum_plus_one_before_decoding() {
    // Arrange / Act / Assert: BVA around the resource-admission ceiling.
    assert!(matches!(
        require_asset_lane_coordinator_receipt_bytes_len_v1(0),
        Err(AssetLaneCoordinatorHostErrorV1::ReceiptSize)
    ));
    assert!(require_asset_lane_coordinator_receipt_bytes_len_v1(
        MAX_ASSET_LANE_COORDINATOR_RECEIPT_BYTES_V1
    )
    .is_ok());
    assert!(matches!(
        require_asset_lane_coordinator_receipt_bytes_len_v1(
            MAX_ASSET_LANE_COORDINATOR_RECEIPT_BYTES_V1 + 1
        ),
        Err(AssetLaneCoordinatorHostErrorV1::ReceiptSize)
    ));

    let verifier = PinnedAssetLaneCoordinatorReceiptVerifierV1;
    assert!(matches!(
        verifier.verify_succinct_receipt(&[], &root(91), &[]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
    let oversized = vec![0_u8; MAX_ASSET_LANE_COORDINATOR_RECEIPT_BYTES_V1 + 1];
    assert!(matches!(
        verifier.verify_succinct_receipt(&oversized, &root(91), &[]),
        Err(AbiErrorV1::InvalidBounds(_))
    ));
}
