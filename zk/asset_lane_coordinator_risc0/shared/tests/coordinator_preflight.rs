use zenodex_asset_lane_coordinator_risc0_shared::{
    canonical_asset_lane_coordinator_guest_input_bytes_v1,
    prepare_asset_lane_coordinator_from_canonical_bytes_v1, prepare_asset_lane_coordinator_v1,
    AssetLaneCoordinatorGuestErrorV1, AssetLaneCoordinatorGuestInputV1,
    ASSET_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1, ASSET_TRANSFER_MODULE_IMAGE_ID_V1,
};
use zenodex_global_settlement_abi_v1::{
    AssetLaneCoordinatorContextV1, AssetLaneCoordinatorRejectCodeV1,
    AssetLaneModuleCompatibilityV1, AssetSupplyV1, AssetTransferCommandV1, AssetTransferContextV1,
    AssetTransferLaneModuleInputV1, AssetTransferPolicyV1, AssetTransferRejectCodeV1,
    AssetTransferStateV1, EconomicAmountV1, RootV1, ASSET_LANE_COORDINATOR_SCHEMA_V1,
    ASSET_TRANSFER_COMMAND_KIND_V1, ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1,
    ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "asset lane coordinator test root",
        false,
    )
    .unwrap()
}

fn module_input(amount_atoms: u128) -> AssetTransferLaneModuleInputV1 {
    AssetTransferLaneModuleInputV1 {
        schema: ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: AssetTransferContextV1 {
            chain_id: "zeno-asset-test".to_owned(),
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

fn coordinator_context() -> AssetLaneCoordinatorContextV1 {
    AssetLaneCoordinatorContextV1 {
        schema: ASSET_LANE_COORDINATOR_SCHEMA_V1.to_owned(),
        chain_id: "zeno-asset-test".to_owned(),
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
    }
}

fn guest_input(amount_atoms: u128) -> AssetLaneCoordinatorGuestInputV1 {
    AssetLaneCoordinatorGuestInputV1 {
        schema: ASSET_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1.to_owned(),
        module_input: module_input(amount_atoms),
        coordinator_context: coordinator_context(),
    }
}

#[test]
fn exact_module_transition_composes_into_the_known_lane_journal() {
    // Arrange
    let input = guest_input(30);
    let input_bytes = canonical_asset_lane_coordinator_guest_input_bytes_v1(&input).unwrap();

    // Act
    let prepared = prepare_asset_lane_coordinator_from_canonical_bytes_v1(&input_bytes).unwrap();

    // Assert
    assert_eq!(prepared.input, input);
    assert_eq!(
        prepared
            .module_accepted
            .post_state
            .balance_atoms("alice", "USD"),
        68
    );
    assert_eq!(
        prepared
            .lane_accepted
            .post_state
            .supply_atoms("USD")
            .unwrap(),
        115
    );
    assert_eq!(
        prepared
            .module_accepted
            .module_journal
            .journal_root()
            .unwrap()
            .to_string(),
        "0x709acd06e9bf22c0f4791b9eb7d8c48a01cc07bc8b66ea8df52dd964a72c2af8"
    );
    assert_eq!(
        prepared
            .lane_accepted
            .lane_journal
            .journal_root()
            .unwrap()
            .to_string(),
        "0xc89ddaaad74124731a00a5530d481c8360ba85613d3e4f887774754f2967da95"
    );
    assert_eq!(
        prepared
            .lane_accepted
            .lane_journal
            .ordered_module_journal_roots,
        vec![prepared
            .module_accepted
            .module_journal
            .journal_root()
            .unwrap()]
    );
}

#[test]
fn module_and_coordinator_rejections_emit_no_lane_journal() {
    // Arrange / Act
    let module_rejected = prepare_asset_lane_coordinator_v1(guest_input(0));
    let mut wrong_chain = guest_input(30);
    wrong_chain.coordinator_context.chain_id = "foreign-chain".to_owned();
    let coordinator_rejected = prepare_asset_lane_coordinator_v1(wrong_chain);

    // Assert
    assert!(matches!(
        module_rejected,
        Err(AssetLaneCoordinatorGuestErrorV1::ModuleRejected(
            AssetTransferRejectCodeV1::ZERO_AMOUNT
        ))
    ));
    assert!(matches!(
        coordinator_rejected,
        Err(AssetLaneCoordinatorGuestErrorV1::CoordinatorRejected(
            AssetLaneCoordinatorRejectCodeV1::CHAIN_MISMATCH
        ))
    ));
}

#[test]
fn amount_boundaries_survive_module_to_lane_composition() {
    // Arrange / Act / Assert: exact BVA with a fixed two-atom transfer fee.
    for amount in [1, 98] {
        let prepared = prepare_asset_lane_coordinator_v1(guest_input(amount)).unwrap();
        assert_eq!(
            prepared
                .module_accepted
                .post_state
                .balance_atoms("alice", "USD"),
            98 - amount
        );
    }
    assert!(matches!(
        prepare_asset_lane_coordinator_v1(guest_input(99)),
        Err(AssetLaneCoordinatorGuestErrorV1::ModuleRejected(
            AssetTransferRejectCodeV1::INSUFFICIENT_BALANCE
        ))
    ));
    assert!(matches!(
        prepare_asset_lane_coordinator_v1(guest_input(u128::MAX)),
        Err(AssetLaneCoordinatorGuestErrorV1::ModuleRejected(
            AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW
        ))
    ));
}

#[test]
fn malformed_and_noncanonical_inputs_fail_before_assumption_verification() {
    // Arrange
    let canonical =
        canonical_asset_lane_coordinator_guest_input_bytes_v1(&guest_input(30)).unwrap();
    let mut trailing = canonical.clone();
    trailing.push(b'\n');
    let mut unknown: serde_json::Value = serde_json::from_slice(&canonical).unwrap();
    unknown
        .as_object_mut()
        .unwrap()
        .insert("unexpected".to_owned(), serde_json::Value::Bool(true));
    let unknown = serde_json::to_vec(&unknown).unwrap();
    let oversized = vec![0_u8; 1_048_577];

    // Act / Assert
    assert!(matches!(
        prepare_asset_lane_coordinator_from_canonical_bytes_v1(&[]),
        Err(AssetLaneCoordinatorGuestErrorV1::EmptyInput)
    ));
    assert!(matches!(
        prepare_asset_lane_coordinator_from_canonical_bytes_v1(&oversized),
        Err(AssetLaneCoordinatorGuestErrorV1::InputTooLarge)
    ));
    assert!(matches!(
        prepare_asset_lane_coordinator_from_canonical_bytes_v1(&unknown),
        Err(AssetLaneCoordinatorGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_asset_lane_coordinator_from_canonical_bytes_v1(&trailing),
        Err(AssetLaneCoordinatorGuestErrorV1::NonCanonicalInput)
    ));
    assert_ne!(ASSET_TRANSFER_MODULE_IMAGE_ID_V1, [0; 8]);
}
