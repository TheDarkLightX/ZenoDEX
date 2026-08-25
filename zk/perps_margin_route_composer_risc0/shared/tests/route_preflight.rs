use zenodex_global_settlement_abi_v1::{
    transition_perps_margin_lane_module_v1, AssetSupplyV1, EconomicAmountV1, PerpsMarginCommandV1,
    PerpsMarginContextV1, PerpsMarginLaneCoordinatorContextV1, PerpsMarginLaneModuleInputV1,
    PerpsMarginLaneProjectionV1, PerpsMarginMarketStatusV1, PerpsMarginModuleCompatibilityV1,
    PerpsMarginResultV1, PerpsMarginStateV1, RootV1, ACCOUNT_CUSTODY_DOMAIN_V1,
    PERPS_MARGIN_CUSTODY_DOMAIN_V1, PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
    PERPS_MARGIN_LANE_COORDINATOR_SCHEMA_V1, PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1,
    PERPS_MARGIN_LANE_PROJECTION_SCHEMA_V1, PERPS_MARGIN_MODULE_SCHEMA_V1, ZERO_ROOT_V1,
};
use zenodex_perps_margin_lane_coordinator_risc0_shared::{
    PerpsMarginLaneCoordinatorGuestInputV1, PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1,
};
use zenodex_perps_margin_route_composer_risc0_shared::{
    canonical_perps_margin_route_composer_guest_input_bytes_v1,
    prepare_perps_margin_route_composer_from_canonical_bytes_v1,
    prepare_perps_margin_route_composer_v1, PerpsMarginRouteComposerGuestErrorV1,
    PerpsMarginRouteComposerGuestInputV1, MAX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_BYTES_V1,
    PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "route preflight test root",
        false,
    )
    .unwrap()
}

fn lane_input(amount_atoms: u128) -> PerpsMarginLaneCoordinatorGuestInputV1 {
    let zero = RootV1::parse(ZERO_ROOT_V1, "route preflight zero root", true).unwrap();
    let module_input = PerpsMarginLaneModuleInputV1 {
        schema: PERPS_MARGIN_LANE_MODULE_INPUT_SCHEMA_V1.to_owned(),
        context: PerpsMarginContextV1 {
            chain_id: "zeno-perps-route-test".to_owned(),
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
    };
    let accepted = match transition_perps_margin_lane_module_v1(&module_input).unwrap() {
        PerpsMarginResultV1::Accepted(value) => *value,
        PerpsMarginResultV1::Rejected(value) => panic!("fixture rejected: {:?}", value.code),
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
            chain_id: "zeno-perps-route-test".to_owned(),
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

fn input(amount_atoms: u128) -> PerpsMarginRouteComposerGuestInputV1 {
    PerpsMarginRouteComposerGuestInputV1 {
        schema: PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_SCHEMA_V1.to_owned(),
        lane_input: lane_input(amount_atoms),
        route_release_id: root(20),
        declared_pre_state_root: root(21),
        declared_post_state_root: root(22),
    }
}

#[test]
fn route_is_constructed_from_the_exact_lane_journal_and_declared_global_roots() {
    // Arrange
    let input = input(100);

    // Act
    let prepared = prepare_perps_margin_route_composer_v1(input.clone()).unwrap();

    // Assert
    assert_eq!(
        prepared.route_journal.route_release_id,
        input.route_release_id
    );
    assert_eq!(
        prepared.route_journal.command_occurrence_id,
        input.lane_input.coordinator_context.command_occurrence_id
    );
    assert_eq!(
        prepared.route_journal.ordered_lane_journal_roots,
        vec![prepared
            .lane
            .lane_accepted
            .lane_journal
            .journal_root()
            .unwrap()]
    );
    assert_eq!(
        prepared.route_journal.effect_plan_root,
        prepared
            .lane
            .lane_accepted
            .effects
            .effect_plan_root()
            .unwrap()
    );
    assert_eq!(
        prepared.route_journal.pre_state_root,
        input.declared_pre_state_root
    );
    assert_eq!(
        prepared.route_journal.post_state_root,
        input.declared_post_state_root
    );
}

#[test]
fn canonical_round_trip_rejects_trailing_bytes_and_oversized_inputs() {
    // Arrange
    let exact = input(100);
    let bytes = canonical_perps_margin_route_composer_guest_input_bytes_v1(&exact).unwrap();
    let mut trailing = bytes.clone();
    trailing.push(b'\n');
    let oversized = vec![b'x'; MAX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_BYTES_V1 + 1];

    // Act / Assert
    assert_eq!(
        prepare_perps_margin_route_composer_from_canonical_bytes_v1(&bytes)
            .unwrap()
            .input,
        exact
    );
    assert_eq!(
        prepare_perps_margin_route_composer_from_canonical_bytes_v1(&trailing),
        Err(PerpsMarginRouteComposerGuestErrorV1::NonCanonicalInput)
    );
    assert_eq!(
        prepare_perps_margin_route_composer_from_canonical_bytes_v1(&oversized),
        Err(PerpsMarginRouteComposerGuestErrorV1::InputTooLarge)
    );
}

#[test]
fn route_release_and_global_root_substitutions_change_the_route_commitment() {
    // Arrange
    let exact = input(100);
    let exact_root = prepare_perps_margin_route_composer_v1(exact.clone())
        .unwrap()
        .route_journal
        .journal_root()
        .unwrap();
    let mut substitutions = Vec::new();
    let mut route = exact.clone();
    route.route_release_id = root(30);
    substitutions.push(route);
    let mut pre = exact.clone();
    pre.declared_pre_state_root = root(31);
    substitutions.push(pre);
    let mut post = exact;
    post.declared_post_state_root = root(32);
    substitutions.push(post);

    // Act / Assert
    for mutant in substitutions {
        let mutant_root = prepare_perps_margin_route_composer_v1(mutant)
            .unwrap()
            .route_journal
            .journal_root()
            .unwrap();
        assert_ne!(mutant_root, exact_root);
    }
}

#[test]
fn schema_and_zero_required_roots_fail_closed() {
    // Arrange
    let exact = input(100);
    let mut wrong_schema = exact.clone();
    wrong_schema.schema = "zenodex/perps-margin-route-composer-guest-input/v2".to_owned();
    let zero = RootV1::parse(ZERO_ROOT_V1, "route preflight zero", true).unwrap();
    let mut zero_route = exact;
    zero_route.route_release_id = zero;

    // Act / Assert
    assert_eq!(
        prepare_perps_margin_route_composer_v1(wrong_schema),
        Err(PerpsMarginRouteComposerGuestErrorV1::Schema)
    );
    assert_eq!(
        prepare_perps_margin_route_composer_v1(zero_route),
        Err(PerpsMarginRouteComposerGuestErrorV1::Abi)
    );
}
