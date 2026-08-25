use zenodex_global_settlement_abi_v1::{
    transition_perps_margin_lane_module_v1, AssetSupplyV1, EconomicAmountV1, PerpsMarginCommandV1,
    PerpsMarginContextV1, PerpsMarginLaneCoordinatorContextV1,
    PerpsMarginLaneCoordinatorRejectCodeV1, PerpsMarginLaneModuleInputV1,
    PerpsMarginLaneProjectionV1, PerpsMarginMarketStatusV1, PerpsMarginModuleCompatibilityV1,
    PerpsMarginRejectCodeV1, PerpsMarginResultV1, PerpsMarginStateV1, RootV1,
    ACCOUNT_CUSTODY_DOMAIN_V1, PERPS_MARGIN_CUSTODY_DOMAIN_V1,
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, PERPS_MARGIN_LANE_COORDINATOR_SCHEMA_V1,
    PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1, PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1,
    PERPS_MARGIN_MODULE_SCHEMA_V1, ZERO_ROOT_V1,
};
use zenodex_perps_margin_lane_coordinator_risc0_shared::{
    canonical_perps_margin_lane_coordinator_guest_input_bytes_v1,
    prepare_perps_margin_lane_coordinator_from_canonical_bytes_v1,
    prepare_perps_margin_lane_coordinator_v1, PerpsMarginLaneCoordinatorGuestErrorV1,
    PerpsMarginLaneCoordinatorGuestInputV1, MAX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1,
    PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "perps coordinator guest test root",
        false,
    )
    .unwrap()
}

fn module_input(amount_atoms: u128) -> PerpsMarginLaneModuleInputV1 {
    let zero = RootV1::parse(ZERO_ROOT_V1, "perps coordinator zero root", true).unwrap();
    PerpsMarginLaneModuleInputV1 {
        schema: PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: PerpsMarginContextV1 {
            chain_id: "zeno-perps-coordinator-risc0-test".to_owned(),
            deployment_root: root(1),
            profile_root: root(2),
            writer_epoch: 7,
            module_release_id: root(3),
            command_occurrence_id: root(4),
            subject_id: "alice".to_owned(),
            grant_root: root(5),
            oracle_authority_root: zero.clone(),
            oracle_occurrence_root: zero,
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

fn guest_input(amount_atoms: u128) -> PerpsMarginLaneCoordinatorGuestInputV1 {
    let module_input = module_input(amount_atoms);
    let accepted = match transition_perps_margin_lane_module_v1(&module_input).unwrap() {
        PerpsMarginResultV1::Accepted(value) => *value,
        PerpsMarginResultV1::Rejected(value) => {
            panic!("unexpected fixture reject: {:?}", value.code)
        }
    };
    let pre_state = PerpsMarginLaneProjectionV1 {
        schema: PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1.to_owned(),
        lane_state: module_input.pre_state.clone(),
        balances: vec![EconomicAmountV1 {
            owner: "alice".to_owned(),
            asset: "zUSD".to_owned(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
            amount_atoms: 1_000,
        }],
        accounting_locations: vec![],
        liabilities: vec![],
        supplies: vec![AssetSupplyV1 {
            asset: "zUSD".to_owned(),
            amount_atoms: 1_000,
        }],
        terminal_obligations: vec![],
    };
    let post_state = PerpsMarginLaneProjectionV1 {
        schema: PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1.to_owned(),
        lane_state: accepted.post_state.clone(),
        balances: vec![EconomicAmountV1 {
            owner: "alice".to_owned(),
            asset: "zUSD".to_owned(),
            custody_domain: ACCOUNT_CUSTODY_DOMAIN_V1.to_owned(),
            amount_atoms: 1_000 - amount_atoms,
        }],
        accounting_locations: vec![EconomicAmountV1 {
            owner: "alice-margin".to_owned(),
            asset: "zUSD".to_owned(),
            custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
            amount_atoms,
        }],
        liabilities: vec![EconomicAmountV1 {
            owner: "alice".to_owned(),
            asset: "zUSD".to_owned(),
            custody_domain: PERPS_MARGIN_CUSTODY_DOMAIN_V1.to_owned(),
            amount_atoms,
        }],
        supplies: vec![AssetSupplyV1 {
            asset: "zUSD".to_owned(),
            amount_atoms: 1_000,
        }],
        terminal_obligations: accepted.post_state.terminal_obligations().unwrap(),
    };
    PerpsMarginLaneCoordinatorGuestInputV1 {
        schema: PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1.to_owned(),
        module_input,
        coordinator_context: PerpsMarginLaneCoordinatorContextV1 {
            schema: PERPS_MARGIN_LANE_COORDINATOR_SCHEMA_V1.to_owned(),
            chain_id: "zeno-perps-coordinator-risc0-test".to_owned(),
            deployment_root: root(1),
            profile_root: root(2),
            writer_epoch: 7,
            coordinator_release_id: root(10),
            command_occurrence_id: root(4),
            compatible_modules: vec![PerpsMarginModuleCompatibilityV1 {
                module_release_id: root(3),
                module_schema: PERPS_MARGIN_MODULE_SCHEMA_V1.to_owned(),
            }],
        },
        pre_state,
        post_state,
    }
}

#[test]
fn exact_module_transition_composes_into_one_lane_journal() {
    let prepared = prepare_perps_margin_lane_coordinator_v1(guest_input(100)).unwrap();
    assert_eq!(
        prepared.lane_accepted.post_state.balances[0].amount_atoms,
        900
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
fn canonical_guest_byte_path_matches_typed_coordinator_transition() {
    // Arrange.
    let input = guest_input(100);
    let canonical = canonical_perps_margin_lane_coordinator_guest_input_bytes_v1(&input).unwrap();

    // Act.
    let byte_prepared =
        prepare_perps_margin_lane_coordinator_from_canonical_bytes_v1(&canonical).unwrap();
    let typed_prepared = prepare_perps_margin_lane_coordinator_v1(input.clone()).unwrap();

    // Assert.
    assert_eq!(byte_prepared.input, input);
    assert_eq!(
        byte_prepared.module_accepted,
        typed_prepared.module_accepted
    );
    assert_eq!(byte_prepared.lane_accepted, typed_prepared.lane_accepted);
    assert_eq!(
        byte_prepared.module_journal_bytes,
        typed_prepared.module_journal_bytes
    );
    assert_eq!(
        byte_prepared.lane_journal_bytes,
        typed_prepared.lane_journal_bytes
    );
}

#[test]
fn malformed_noncanonical_and_oversized_coordinator_inputs_fail_closed() {
    // Arrange.
    let canonical =
        canonical_perps_margin_lane_coordinator_guest_input_bytes_v1(&guest_input(100)).unwrap();
    let mut trailing = canonical.clone();
    trailing.push(b'\n');
    let mut unknown: serde_json::Value = serde_json::from_slice(&canonical).unwrap();
    unknown
        .as_object_mut()
        .unwrap()
        .insert("unexpected".to_owned(), serde_json::Value::Bool(true));
    let unknown = serde_json::to_vec(&unknown).unwrap();
    let oversized = vec![0_u8; MAX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1 + 1];

    // Act and assert.
    assert!(matches!(
        prepare_perps_margin_lane_coordinator_from_canonical_bytes_v1(&[]),
        Err(PerpsMarginLaneCoordinatorGuestErrorV1::EmptyInput)
    ));
    assert!(matches!(
        prepare_perps_margin_lane_coordinator_from_canonical_bytes_v1(&oversized),
        Err(PerpsMarginLaneCoordinatorGuestErrorV1::InputTooLarge)
    ));
    assert!(matches!(
        prepare_perps_margin_lane_coordinator_from_canonical_bytes_v1(&unknown),
        Err(PerpsMarginLaneCoordinatorGuestErrorV1::Decode)
    ));
    assert!(matches!(
        prepare_perps_margin_lane_coordinator_from_canonical_bytes_v1(&trailing),
        Err(PerpsMarginLaneCoordinatorGuestErrorV1::NonCanonicalInput)
    ));
}

#[test]
fn module_and_lane_rejections_remain_typed_at_the_guest_boundary() {
    // Arrange: one child-level denial and one valid projection drift that the
    // lane coordinator must reject after the child transition accepts.
    let mut zero_amount = guest_input(100);
    zero_amount.module_input.command.amount_atoms = 0;

    let mut drifted = guest_input(100);
    drifted.post_state.balances[0].amount_atoms -= 1;
    drifted
        .post_state
        .accounting_locations
        .push(EconomicAmountV1 {
            owner: "treasury".to_owned(),
            asset: "zUSD".to_owned(),
            custody_domain: "treasury".to_owned(),
            amount_atoms: 1,
        });
    drifted.post_state.validate().unwrap();

    // Act and assert.
    assert!(matches!(
        prepare_perps_margin_lane_coordinator_v1(zero_amount),
        Err(PerpsMarginLaneCoordinatorGuestErrorV1::ModuleRejected(
            PerpsMarginRejectCodeV1::ZERO_AMOUNT
        ))
    ));
    assert!(matches!(
        prepare_perps_margin_lane_coordinator_v1(drifted),
        Err(PerpsMarginLaneCoordinatorGuestErrorV1::CoordinatorRejected(
            PerpsMarginLaneCoordinatorRejectCodeV1::STATE_EFFECT_MISMATCH
        ))
    ));
}
