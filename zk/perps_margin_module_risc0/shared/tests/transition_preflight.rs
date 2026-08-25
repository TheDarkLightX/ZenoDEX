use zenodex_global_settlement_abi_v1::{
    PerpsMarginCommandV1, PerpsMarginContextV1, PerpsMarginLaneModuleInputV1,
    PerpsMarginMarketStatusV1, PerpsMarginResultV1, PerpsMarginStateV1, RootV1,
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1,
    PERPS_MARGIN_MODULE_SCHEMA_V1, ZERO_ROOT_V1,
};
use zenodex_perps_margin_module_risc0_shared::prepare_perps_margin_module_v1;
use zenodex_perps_margin_module_risc0_shared::{
    canonical_perps_margin_module_guest_input_bytes_v1,
    prepare_perps_margin_module_from_canonical_bytes_v1, PerpsMarginModuleGuestErrorV1,
    MAX_PERPS_MARGIN_MODULE_GUEST_INPUT_BYTES_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "perps module guest test root",
        false,
    )
    .unwrap()
}

fn zero_root() -> RootV1 {
    RootV1::parse(ZERO_ROOT_V1, "perps module guest zero root", true).unwrap()
}

fn module_input(amount_atoms: u128) -> PerpsMarginLaneModuleInputV1 {
    PerpsMarginLaneModuleInputV1 {
        schema: PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: PerpsMarginContextV1 {
            chain_id: "zeno-perps-module-risc0-test".to_owned(),
            deployment_root: root(1),
            profile_root: root(2),
            writer_epoch: 7,
            module_release_id: root(3),
            command_occurrence_id: root(4),
            subject_id: "alice".to_owned(),
            grant_root: root(5),
            oracle_authority_root: zero_root(),
            oracle_occurrence_root: zero_root(),
            oracle_price_e8: 0,
        },
        pre_state: PerpsMarginStateV1 {
            schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
            module_release_id: root(3),
            market_id: "BTC-ZUSD-PERP".to_owned(),
            collateral_asset: "zUSD".to_owned(),
            index_price_e8: 6_500_000_000_000,
            maintenance_margin_bps: 500,
            depeg_buffer_bps: 100,
            max_position_abs: 10,
            market_status: PerpsMarginMarketStatusV1::ACTIVE,
            accounts: vec![],
        },
        command: PerpsMarginCommandV1 {
            command_kind: PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1.to_owned(),
            account_id: "alice-margin".to_owned(),
            market_id: "BTC-ZUSD-PERP".to_owned(),
            owner: "alice".to_owned(),
            asset: "zUSD".to_owned(),
            amount_atoms,
            nonce: 1,
        },
    }
}

#[test]
fn exact_deposit_transition_produces_one_canonical_module_journal() {
    // Arrange.
    let input = module_input(100);

    // Act.
    let prepared = prepare_perps_margin_module_v1(input).unwrap();

    // Assert.
    assert!(matches!(
        prepared.accepted,
        zenodex_global_settlement_abi_v1::PerpsMarginAcceptedV1 { .. }
    ));
    assert!(!prepared.journal_bytes.is_empty());
    assert!(matches!(
        zenodex_global_settlement_abi_v1::transition_perps_margin_lane_module_v1(&prepared.input)
            .unwrap(),
        PerpsMarginResultV1::Accepted(_)
    ));
    assert_eq!(
        prepared
            .accepted
            .module_journal
            .journal_root()
            .unwrap()
            .as_str(),
        "0x00b00d3a379b56a8e04066f9b4b5c79c91f2bce0177b701d3b8b568d0947f879"
    );
}

#[test]
fn economic_rejections_emit_no_prepared_journal() {
    // Arrange and act.
    let rejected = prepare_perps_margin_module_v1(module_input(0));

    // Assert.
    assert!(matches!(
        rejected,
        Err(PerpsMarginModuleGuestErrorV1::Rejected(
            zenodex_global_settlement_abi_v1::PerpsMarginRejectCodeV1::ZERO_AMOUNT
        ))
    ));
}

#[test]
fn amount_bva_accepts_one_and_i128_max_then_rejects_i128_max_plus_one() {
    // Arrange, act, and assert.
    for amount_atoms in [1, i128::MAX as u128] {
        assert!(prepare_perps_margin_module_v1(module_input(amount_atoms)).is_ok());
    }
    assert!(matches!(
        prepare_perps_margin_module_v1(module_input(i128::MAX as u128 + 1)),
        Err(PerpsMarginModuleGuestErrorV1::Rejected(
            zenodex_global_settlement_abi_v1::PerpsMarginRejectCodeV1::EFFECT_DELTA_OVERFLOW
        ))
    ));
}

#[test]
fn malformed_noncanonical_and_oversized_inputs_reject_before_transition() {
    // Arrange.
    let canonical = canonical_perps_margin_module_guest_input_bytes_v1(&module_input(100)).unwrap();
    let mut trailing = canonical.clone();
    trailing.push(b'\n');
    let mut unknown: serde_json::Value = serde_json::from_slice(&canonical).unwrap();
    unknown
        .as_object_mut()
        .unwrap()
        .insert("unexpected".to_owned(), serde_json::Value::Bool(true));
    let unknown = serde_json::to_vec(&unknown).unwrap();
    let oversized = vec![0_u8; MAX_PERPS_MARGIN_MODULE_GUEST_INPUT_BYTES_V1 + 1];

    // Act and assert.
    assert!(matches!(
        prepare_perps_margin_module_from_canonical_bytes_v1(&[]),
        Err(PerpsMarginModuleGuestErrorV1::EmptyInput)
    ));
    assert!(matches!(
        prepare_perps_margin_module_from_canonical_bytes_v1(&oversized),
        Err(PerpsMarginModuleGuestErrorV1::InputTooLarge)
    ));
    assert!(matches!(
        prepare_perps_margin_module_from_canonical_bytes_v1(&unknown),
        Err(PerpsMarginModuleGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_perps_margin_module_from_canonical_bytes_v1(&trailing),
        Err(PerpsMarginModuleGuestErrorV1::NonCanonicalInput)
    ));
}
