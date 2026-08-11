use zenodex_asset_transfer_module_risc0_shared::{
    canonical_asset_transfer_guest_input_bytes_v1,
    prepare_asset_transfer_module_from_canonical_bytes_v1, prepare_asset_transfer_module_v1,
    AssetTransferGuestErrorV1,
};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, transition_asset_transfer_lane_module_v1, AssetSupplyV1,
    AssetTransferCommandV1, AssetTransferContextV1, AssetTransferLaneModuleInputV1,
    AssetTransferLaneModuleResultV1, AssetTransferPolicyV1, AssetTransferRejectCodeV1,
    AssetTransferStateV1, EconomicAmountV1, RootV1, ASSET_TRANSFER_COMMAND_KIND_V1,
    ASSET_TRANSFER_LANE_MODULE_INPUT_SCHEMA_V1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "asset transfer guest test root",
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

#[test]
fn exact_core_acceptance_commits_the_known_module_journal() {
    // Arrange
    let input = module_input(30);
    let input_bytes = canonical_asset_transfer_guest_input_bytes_v1(&input).unwrap();

    // Act
    let prepared = prepare_asset_transfer_module_from_canonical_bytes_v1(&input_bytes).unwrap();

    // Assert
    assert_eq!(prepared.input, input);
    assert_eq!(
        prepared.accepted.post_state.balance_atoms("alice", "USD"),
        68
    );
    assert_eq!(prepared.accepted.post_state.balance_atoms("bob", "USD"), 40);
    assert_eq!(
        prepared
            .accepted
            .post_state
            .balance_atoms("treasury", "USD"),
        7
    );
    assert_eq!(
        prepared
            .accepted
            .module_journal
            .journal_root()
            .unwrap()
            .to_string(),
        "0x709acd06e9bf22c0f4791b9eb7d8c48a01cc07bc8b66ea8df52dd964a72c2af8"
    );
    assert_eq!(
        prepared.journal_bytes,
        canonical_bytes_v1(&prepared.accepted.module_journal).unwrap()
    );
}

#[test]
fn one_atom_and_exact_balance_neighbor_accept_while_next_atom_rejects() {
    // Arrange / Act / Assert: amount BVA with a fixed two-atom fee.
    for amount in [1, 98] {
        let prepared = prepare_asset_transfer_module_v1(module_input(amount)).unwrap();
        assert_eq!(
            prepared.accepted.post_state.balance_atoms("alice", "USD"),
            98 - amount
        );
    }
    assert!(matches!(
        prepare_asset_transfer_module_v1(module_input(99)),
        Err(AssetTransferGuestErrorV1::Rejected(
            AssetTransferRejectCodeV1::INSUFFICIENT_BALANCE
        ))
    ));
    assert!(matches!(
        prepare_asset_transfer_module_v1(module_input(u128::MAX)),
        Err(AssetTransferGuestErrorV1::Rejected(
            AssetTransferRejectCodeV1::EFFECT_DELTA_OVERFLOW
        ))
    ));
}

#[test]
fn typed_rejection_is_an_exact_noop_and_produces_no_guest_journal() {
    // Arrange
    let input = module_input(0);

    // Act
    let direct = transition_asset_transfer_lane_module_v1(&input).unwrap();
    let guest = prepare_asset_transfer_module_v1(input);

    // Assert
    let AssetTransferLaneModuleResultV1::Rejected(rejected) = direct else {
        panic!("zero transfer must reject")
    };
    assert_eq!(rejected.code, AssetTransferRejectCodeV1::ZERO_AMOUNT);
    assert_eq!(rejected.pre_state_root, rejected.post_state_root);
    assert!(rejected.effects.is_empty());
    assert!(matches!(
        guest,
        Err(AssetTransferGuestErrorV1::Rejected(
            AssetTransferRejectCodeV1::ZERO_AMOUNT
        ))
    ));
}

#[test]
fn empty_oversized_unknown_and_noncanonical_inputs_fail_closed() {
    // Arrange
    let canonical = canonical_asset_transfer_guest_input_bytes_v1(&module_input(30)).unwrap();
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
        prepare_asset_transfer_module_from_canonical_bytes_v1(&[]),
        Err(AssetTransferGuestErrorV1::EmptyInput)
    ));
    assert!(matches!(
        prepare_asset_transfer_module_from_canonical_bytes_v1(&oversized),
        Err(AssetTransferGuestErrorV1::InputTooLarge)
    ));
    assert!(matches!(
        prepare_asset_transfer_module_from_canonical_bytes_v1(&unknown),
        Err(AssetTransferGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_asset_transfer_module_from_canonical_bytes_v1(&trailing),
        Err(AssetTransferGuestErrorV1::NonCanonicalInput)
    ));
}
