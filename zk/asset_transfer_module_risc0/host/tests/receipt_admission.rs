use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
use zenodex_asset_transfer_module_risc0_host::{
    build_asset_transfer_module_executor_env_v1, prove_asset_transfer_module_succinct_v1,
    verify_asset_transfer_module_receipt_v1, AssetTransferModuleHostErrorV1,
};
use zenodex_asset_transfer_module_risc0_shared::AssetTransferGuestErrorV1;
use zenodex_global_settlement_abi_v1::{
    AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1, AssetTransferLaneModuleInputV1,
    AssetTransferPolicyV1, AssetTransferRejectCodeV1, AssetTransferStateV1, EconomicAmountV1,
    RootV1, ASSET_TRANSFER_COMMAND_KIND_V1, ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "asset transfer host test root",
        false,
    )
    .unwrap()
}

fn module_input(amount_atoms: u128) -> AssetTransferLaneModuleInputV1 {
    AssetTransferLaneModuleInputV1 {
        schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: AssetTransferContextV1 {
            chain_id: "zeno-asset-host-test".to_owned(),
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
            amount_atoms,
            max_fee_atoms: 2,
        },
        asset_policy_registry_root: root(11),
        fee_policy_registry_root: root(12),
        custody: vec![],
    }
}

#[test]
fn host_preflight_uses_the_same_transition_and_rejects_economic_denial() {
    // Arrange / Act
    let (_, accepted) = build_asset_transfer_module_executor_env_v1(&module_input(30)).unwrap();
    let rejected = build_asset_transfer_module_executor_env_v1(&module_input(0));

    // Assert
    assert_eq!(
        accepted.accepted.post_state.balance_atoms("alice", "USD"),
        68
    );
    assert!(matches!(
        rejected,
        Err(AssetTransferModuleHostErrorV1::Guest(
            AssetTransferGuestErrorV1::Rejected(AssetTransferRejectCodeV1::ZERO_AMOUNT)
        ))
    ));
}

#[test]
fn placeholder_method_and_fake_receipt_fail_before_authority() {
    // Arrange
    let (_, prepared) = build_asset_transfer_module_executor_env_v1(&module_input(30)).unwrap();
    let fake: Receipt =
        FakeReceipt::new(ReceiptClaim::ok([1_u32; 8], prepared.journal_bytes.clone()))
            .try_into()
            .unwrap();

    // Act / Assert
    assert!(matches!(
        prove_asset_transfer_module_succinct_v1(&module_input(30)),
        Err(AssetTransferModuleHostErrorV1::PlaceholderMethod)
    ));
    assert!(matches!(
        verify_asset_transfer_module_receipt_v1(&fake, &prepared.journal_bytes),
        Err(AssetTransferModuleHostErrorV1::ReceiptKind)
    ));
}
