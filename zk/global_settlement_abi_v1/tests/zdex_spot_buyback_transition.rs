//! Rust refinement evidence for the bounded SHADOW Spot buyback core.
//!
//! The literal roots below are independently pinned by
//! `tests/core/test_zdex_spot_buyback_transition_v1.py`.  This test proves only
//! that the two local runtimes agree on this bounded transition surface. It
//! grants no route, receipt, settlement, or publication authority.

use zenodex_global_settlement_abi_v1::{
    transition_zdex_spot_buyback_v1, ReleaseStatusV1, RootV1, ZDEXBuybackExecutionPolicyV1,
    ZDEXBuybackOraclePriceOccurrenceV1, ZDEXBuybackPriceSafetyPolicyV1,
    ZDEXSpotBuybackAuthorityContextV1, ZDEXSpotBuybackAuthorityInputV1, ZDEXSpotBuybackInputV1,
    ZDEXSpotBuybackRejectCodeV1, ZDEXSpotBuybackReleaseV1, ZDEXSpotBuybackResultV1,
    ZDEXSpotCurveKindV1, ZDEXSpotLaneStateV1, ZDEXSpotOracleOccurrenceV1, ZDEXSpotOracleRegistryV1,
    ZDEXSpotOracleStatusV1, ZDEXSpotPoolCreationReleaseV1, ZDEXSpotPoolDefinitionV1,
    ZDEXSpotPoolStatusV1, ZDEXSpotPoolV1, ZDEXSpotPriceEnvelopeV1, ZDEXSpotPrivatePortsV1,
    ZDEXSpotProfileAuthorizationV1, ZDEXSpotQuoteInputPortV1,
    ZDEX_BUYBACK_EXECUTION_POLICY_SCHEMA_V1, ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1,
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1, ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("fixed test root")
}

fn authority_mut(candidate: &mut ZDEXSpotBuybackInputV1) -> &mut ZDEXSpotBuybackAuthorityContextV1 {
    match &mut candidate.authority {
        ZDEXSpotBuybackAuthorityInputV1::CONTEXT(authority) => authority,
        ZDEXSpotBuybackAuthorityInputV1::MALFORMED => panic!("test candidate lost authority"),
    }
}

fn rebind_profile(candidate: &mut ZDEXSpotBuybackInputV1) {
    let authority = authority_mut(candidate);
    authority.profile_authorization.release_root = authority.release.release_root().expect("root");
    authority.profile_authorization.execution_policy_root =
        authority.execution_policy.policy_root().expect("root");
    authority.profile_authorization.price_policy_root =
        authority.price_policy.policy_root().expect("root");
    authority.profile_authorization_root = authority
        .profile_authorization
        .authorization_root()
        .expect("root");
}

fn rebind_state(candidate: &mut ZDEXSpotBuybackInputV1, state: ZDEXSpotLaneStateV1) {
    let state_root = state.state_root().expect("state root");
    candidate.pre_state = state;
    candidate.quote_port.spot_pre_state_root = state_root.clone();
    candidate.price_envelope.spot_pre_state_root = state_root.clone();
    authority_mut(candidate).spot_pre_state_root = state_root;
}

fn rebind_governed_pool(
    candidate: &mut ZDEXSpotBuybackInputV1,
    definition: ZDEXSpotPoolDefinitionV1,
) {
    let pool_id = definition.pool_id().expect("pool id");
    let definition_root = definition.definition_root().expect("definition root");
    {
        let authority = authority_mut(candidate);
        authority.expected_pool_definition = definition;
        authority.execution_policy.pool_id = pool_id.clone();
        authority.execution_policy.pool_definition_root = definition_root;
    }
    candidate.price_envelope.selected_pool_id = pool_id;
    rebind_profile(candidate);
}

fn rebind_oracle(candidate: &mut ZDEXSpotBuybackInputV1, oracle: ZDEXSpotOracleOccurrenceV1) {
    let occurrence_id = oracle.occurrence_id().expect("oracle occurrence root");
    {
        let authority = authority_mut(candidate);
        authority.oracle_registry = ZDEXSpotOracleRegistryV1 {
            occurrences: vec![oracle.clone()],
        };
        authority.oracle_occurrence = oracle.clone();
    }
    candidate.price_envelope.oracle_occurrence_id = occurrence_id;
    candidate.price_envelope.oracle_finality_root = oracle.finality_root;
    candidate.price_envelope.oracle_observed_height = oracle.price.observed_height;
    candidate.price_envelope.oracle_quote_numerator_atoms = oracle.price.quote_numerator_atoms;
    candidate.price_envelope.oracle_zdex_denominator_atoms = oracle.price.zdex_denominator_atoms;
}

fn candidate() -> ZDEXSpotBuybackInputV1 {
    let release = ZDEXSpotBuybackReleaseV1 {
        spot_module_release_id: root(1_001),
        tokenomics_module_release_id: root(1_002),
        route_release_id: root(2_001),
        cpmm_curve_release_id: root(8_000),
        protocol_fee_share_bps: 0,
        reserve_cap_atoms: 3_000_000_000,
        swap_cap_atoms: 3_000_000_000,
        pool_count_cap: 64,
        pool_creation_releases: vec![ZDEXSpotPoolCreationReleaseV1 {
            module_release_id: root(1_001),
            status: ReleaseStatusV1::ACTIVE_NEW,
        }],
        registered_sibling_curve_releases: vec![],
    };
    let definition = ZDEXSpotPoolDefinitionV1 {
        asset0: root(1),
        asset1: root(2),
        fee_bps: 0,
        curve_kind: ZDEXSpotCurveKindV1::CPMM_V8_EXACT_IN,
        curve_release_id: release.cpmm_curve_release_id.clone(),
        curve_params_root: RootV1::parse(ZERO_ROOT_V1, "zero root", true).expect("zero root"),
    };
    let pool = ZDEXSpotPoolV1 {
        pool_id: definition.pool_id().expect("pool id"),
        definition: definition.clone(),
        reserve0_atoms: 1_000,
        reserve1_atoms: 1_000,
        lp_supply_atoms: 1_000,
        status: ZDEXSpotPoolStatusV1::ACTIVE,
        creation_release_id: release.spot_module_release_id.clone(),
        created_height: 1,
    };
    let state = ZDEXSpotLaneStateV1 {
        pools: vec![pool],
        lp_ownership_root: root(11),
        route_batch_root: root(12),
        fee_residue_root: root(13),
        pool_terminal_obligations_root: root(14),
    };
    let execution_policy = ZDEXBuybackExecutionPolicyV1 {
        schema: ZDEX_BUYBACK_EXECUTION_POLICY_SCHEMA_V1.to_owned(),
        pool_id: definition.pool_id().expect("pool id"),
        pool_definition_root: definition.definition_root().expect("definition root"),
        quote_asset_id: definition.asset0.clone(),
        zdex_asset_id: definition.asset1.clone(),
    };
    let price_policy = ZDEXBuybackPriceSafetyPolicyV1 {
        schema: ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1.to_owned(),
        oracle_id: "zdex-buyback-oracle".to_owned(),
        maximum_oracle_age_blocks: 3,
        minimum_quote_reserve_atoms: 500,
        minimum_zdex_reserve_atoms: 500,
        maximum_pool_oracle_deviation_bps: 2_000,
        maximum_execution_impact_bps: 2_000,
        maximum_oracle_execution_deviation_bps: 1_000,
        maximum_quote_reserve_spend_bps: 2_000,
    };
    let profile = ZDEXSpotProfileAuthorizationV1 {
        profile_root: root(3_000),
        chain_id: "zenodex-test-chain".to_owned(),
        deployment_root: root(3_001),
        route_release_id: release.route_release_id.clone(),
        spot_module_release_id: release.spot_module_release_id.clone(),
        tokenomics_module_release_id: release.tokenomics_module_release_id.clone(),
        oracle_id: price_policy.oracle_id.clone(),
        release_root: release.release_root().expect("release root"),
        execution_policy_root: execution_policy.policy_root().expect("policy root"),
        price_policy_root: price_policy.policy_root().expect("policy root"),
    };
    let profile_authorization_root = profile.authorization_root().expect("profile root");
    let price = ZDEXBuybackOraclePriceOccurrenceV1 {
        schema: ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1.to_owned(),
        oracle_id: price_policy.oracle_id.clone(),
        quote_asset_id: execution_policy.quote_asset_id.clone(),
        zdex_asset_id: execution_policy.zdex_asset_id.clone(),
        quote_numerator_atoms: 125,
        zdex_denominator_atoms: 111,
        observed_height: 76,
    };
    let oracle = ZDEXSpotOracleOccurrenceV1 {
        price,
        finality_root: root(96),
        status: ZDEXSpotOracleStatusV1::FINAL,
    };
    let state_root = state.state_root().expect("state root");
    let authority = ZDEXSpotBuybackAuthorityContextV1 {
        chain_id: profile.chain_id.clone(),
        deployment_root: profile.deployment_root.clone(),
        profile_root: profile.profile_root.clone(),
        profile_authorization_root,
        route_release_id: release.route_release_id.clone(),
        command_occurrence_id: root(92),
        global_pre_state_root: root(5_000),
        spot_pre_state_root: state_root.clone(),
        writer_epoch: 0,
        current_height: 77,
        spot_module_release_id: release.spot_module_release_id.clone(),
        tokenomics_module_release_id: release.tokenomics_module_release_id.clone(),
        release: release.clone(),
        execution_policy: execution_policy.clone(),
        expected_pool_definition: definition,
        price_policy,
        profile_authorization: profile,
        oracle_registry: ZDEXSpotOracleRegistryV1 {
            occurrences: vec![oracle.clone()],
        },
        oracle_occurrence: oracle.clone(),
    };
    ZDEXSpotBuybackInputV1 {
        authority: ZDEXSpotBuybackAuthorityInputV1::CONTEXT(Box::new(authority.clone())),
        pre_state: state,
        quote_port: ZDEXSpotQuoteInputPortV1 {
            profile_root: authority.profile_root.clone(),
            route_release_id: authority.route_release_id.clone(),
            command_occurrence_id: authority.command_occurrence_id.clone(),
            global_pre_state_root: authority.global_pre_state_root.clone(),
            spot_pre_state_root: state_root.clone(),
            source_module_release_id: authority.tokenomics_module_release_id.clone(),
            destination_module_release_id: authority.spot_module_release_id.clone(),
            source_pre_state_root: root(201),
            source_post_state_root: root(202),
            source_effect_plan_root: root(203),
            source_journal_root: root(204),
            source_receipt_binding_root: root(205),
            amount_atoms: 125,
        },
        price_envelope: ZDEXSpotPriceEnvelopeV1 {
            profile_root: authority.profile_root.clone(),
            route_release_id: authority.route_release_id.clone(),
            command_occurrence_id: authority.command_occurrence_id.clone(),
            global_pre_state_root: authority.global_pre_state_root.clone(),
            spot_pre_state_root: state_root,
            selected_pool_id: authority.execution_policy.pool_id.clone(),
            oracle_occurrence_id: oracle.occurrence_id().expect("oracle root"),
            oracle_finality_root: oracle.finality_root,
            quote_amount_atoms: 125,
            current_height: authority.current_height,
            oracle_observed_height: oracle.price.observed_height,
            oracle_quote_numerator_atoms: oracle.price.quote_numerator_atoms,
            oracle_zdex_denominator_atoms: oracle.price.zdex_denominator_atoms,
            claimed_route_safe_quote_limit_atoms: 200,
            minimum_output_atoms: 101,
        },
    }
}

fn reject_code(candidate: &ZDEXSpotBuybackInputV1) -> ZDEXSpotBuybackRejectCodeV1 {
    match transition_zdex_spot_buyback_v1(candidate).expect("typed transition") {
        ZDEXSpotBuybackResultV1::Rejected(rejected) => {
            rejected.validate().expect("reject invariant");
            assert_eq!(rejected.pre_state(), &candidate.pre_state);
            assert_eq!(rejected.post_state(), &candidate.pre_state);
            assert!(rejected.effects().is_empty());
            rejected.code()
        }
        ZDEXSpotBuybackResultV1::Accepted(_) => panic!("expected exact no-op rejection"),
    }
}

#[test]
fn roots_match_python_shadow_core_golden_vectors() {
    // Arrange.
    let candidate = candidate();

    // Act.
    let result = transition_zdex_spot_buyback_v1(&candidate).expect("transition");

    // Assert: pre-root plus the five accepted roots pinned by Python.
    assert_eq!(
        candidate.pre_state.state_root().expect("root").to_string(),
        "0x49ac89c397d72b40aafb12b556cd1cb3e7e32bf4c0189eb0c16afc5cd12517cb"
    );
    let ZDEXSpotBuybackResultV1::Accepted(accepted) = result else {
        panic!("baseline must accept");
    };
    accepted.validate().expect("accepted cross-bindings");
    assert_eq!(
        accepted.journal().context_root.to_string(),
        "0x82f0b0cbe3908be00803b7d77495f2d35f92106380d9076b23b65b39c67437a6"
    );
    assert_eq!(
        accepted
            .post_state()
            .state_root()
            .expect("root")
            .to_string(),
        "0xb42313a61d18805ae7745a54b5d1bdf1e58479ebeda34861942aa022bc9a1b0f"
    );
    assert_eq!(
        accepted
            .effects()
            .effect_plan_root()
            .expect("root")
            .to_string(),
        "0xafcb6b6f8bd26a69fe8d637717450f37cc4d0f1ed380f64c19910dd01886d71a"
    );
    assert_eq!(
        accepted.ports().ports_root().expect("root").to_string(),
        "0x8c6e07a5e3614178d98535d27cb170ae306fb4c241727594dea15459cc523994"
    );
    assert_eq!(
        accepted
            .terminal_obligation()
            .obligation_id()
            .expect("root")
            .to_string(),
        "0xd41633a3185a5cb3528915a2146cf8ac97485b6d804c289b108f451e80300054"
    );
    assert_eq!(
        accepted.journal().journal_root().expect("root").to_string(),
        "0x003711f76c6ae397542cb000cae6445994654275d50d53f930c781c9d9970ae3"
    );
}

#[test]
fn private_port_root_rejects_a_duplicated_role() {
    // Arrange.
    let ZDEXSpotBuybackResultV1::Accepted(accepted) =
        transition_zdex_spot_buyback_v1(&candidate()).expect("transition")
    else {
        panic!("baseline must accept");
    };
    let duplicated = ZDEXSpotPrivatePortsV1 {
        quote_input: accepted.ports().quote_input.clone(),
        purchased_output: accepted.ports().quote_input.clone(),
    };

    // Act / Assert.
    assert!(duplicated.ports_root().is_err());
}

#[test]
fn rounding_one_atom_sibling_and_conservation_hold() {
    // Arrange: the selected pool is governed; its sibling only tests preservation.
    let mut candidate = candidate();
    let release = authority_mut(&mut candidate).release.clone();
    let sibling_definition = ZDEXSpotPoolDefinitionV1 {
        asset0: root(3),
        asset1: root(4),
        fee_bps: 0,
        curve_kind: ZDEXSpotCurveKindV1::CPMM_V8_EXACT_IN,
        curve_release_id: release.cpmm_curve_release_id,
        curve_params_root: RootV1::parse(ZERO_ROOT_V1, "zero root", true).expect("root"),
    };
    let sibling = ZDEXSpotPoolV1 {
        pool_id: sibling_definition.pool_id().expect("pool id"),
        definition: sibling_definition,
        reserve0_atoms: 500,
        reserve1_atoms: 500,
        lp_supply_atoms: 500,
        status: ZDEXSpotPoolStatusV1::ACTIVE,
        creation_release_id: release.spot_module_release_id,
        created_height: 1,
    };
    let mut state = candidate.pre_state.clone();
    state.pools[0].definition.fee_bps = 1;
    state.pools[0].pool_id = state.pools[0].definition.pool_id().expect("pool id");
    state.pools.push(sibling.clone());
    state
        .pools
        .sort_by(|left, right| left.pool_id.cmp(&right.pool_id));
    let selected = state
        .pools
        .iter()
        .find(|pool| pool.definition.fee_bps == 1)
        .expect("selected pool")
        .definition
        .clone();
    rebind_governed_pool(&mut candidate, selected.clone());
    rebind_state(&mut candidate, state);

    // Act.
    let result = transition_zdex_spot_buyback_v1(&candidate).expect("transition");

    // Assert: ceil(125 / 10_000) = 1, output is 110 and sibling is unchanged.
    let ZDEXSpotBuybackResultV1::Accepted(accepted) = result else {
        panic!("rounded transition must accept");
    };
    assert_eq!(accepted.journal().fee_atoms, 1);
    assert_eq!(accepted.journal().net_input_atoms, 124);
    assert_eq!(accepted.journal().purchased_zdex_atoms, 110);
    assert!(accepted.post_state().pools.contains(&sibling));
    let pre_selected = candidate
        .pre_state
        .pools
        .iter()
        .find(|pool| pool.pool_id == selected.pool_id().expect("pool id"))
        .expect("selected pool");
    let post_selected = accepted
        .post_state()
        .pools
        .iter()
        .find(|pool| pool.pool_id == pre_selected.pool_id)
        .expect("selected pool");
    assert_eq!(
        post_selected.reserve0_atoms - pre_selected.reserve0_atoms,
        125
    );
    assert_eq!(
        pre_selected.reserve1_atoms - post_selected.reserve1_atoms,
        110
    );
    assert!(
        post_selected.reserve0_atoms * post_selected.reserve1_atoms
            >= pre_selected.reserve0_atoms * pre_selected.reserve1_atoms
    );
}

#[test]
fn one_atom_boundary_is_live_under_wide_shadow_envelope() {
    // Arrange.
    let mut candidate = candidate();
    let mut state = candidate.pre_state.clone();
    state.pools[0].reserve0_atoms = 501;
    state.pools[0].reserve1_atoms = 1_000;
    rebind_state(&mut candidate, state);
    candidate.quote_port.amount_atoms = 1;
    candidate.price_envelope.quote_amount_atoms = 1;
    candidate.price_envelope.minimum_output_atoms = 1;
    candidate
        .price_envelope
        .claimed_route_safe_quote_limit_atoms = 100;
    {
        let authority = authority_mut(&mut candidate);
        authority.price_policy.minimum_quote_reserve_atoms = 1;
        authority.price_policy.minimum_zdex_reserve_atoms = 1;
        authority.price_policy.maximum_pool_oracle_deviation_bps = 9_999;
        authority.price_policy.maximum_execution_impact_bps = 9_999;
        authority
            .price_policy
            .maximum_oracle_execution_deviation_bps = 9_999;
    }
    let mut price = authority_mut(&mut candidate)
        .oracle_occurrence
        .price
        .clone();
    price.quote_numerator_atoms = 1;
    price.zdex_denominator_atoms = 1;
    rebind_oracle(
        &mut candidate,
        ZDEXSpotOracleOccurrenceV1 {
            price,
            finality_root: root(96),
            status: ZDEXSpotOracleStatusV1::FINAL,
        },
    );
    rebind_profile(&mut candidate);

    // Act / Assert.
    let ZDEXSpotBuybackResultV1::Accepted(accepted) =
        transition_zdex_spot_buyback_v1(&candidate).expect("transition")
    else {
        panic!("one atom must remain live");
    };
    assert_eq!(accepted.journal().quote_input_atoms, 1);
    assert_eq!(accepted.journal().purchased_zdex_atoms, 1);
}

#[test]
fn reversed_asset_order_is_a_policy_mismatch_before_lane_validation() {
    // Arrange: make every earlier profile and Oracle binding coherent while
    // retaining the original lane state. A missing ordering guard would
    // therefore reach the later malformed-lane classification.
    let mut candidate = candidate();
    let (quote_asset, zdex_asset, mut definition, mut oracle) = {
        let authority = authority_mut(&mut candidate);
        (
            authority.execution_policy.quote_asset_id.clone(),
            authority.execution_policy.zdex_asset_id.clone(),
            authority.expected_pool_definition.clone(),
            authority.oracle_occurrence.clone(),
        )
    };
    definition.asset0 = zdex_asset.clone();
    definition.asset1 = quote_asset.clone();
    rebind_governed_pool(&mut candidate, definition);
    {
        let authority = authority_mut(&mut candidate);
        authority.execution_policy.quote_asset_id = zdex_asset.clone();
        authority.execution_policy.zdex_asset_id = quote_asset.clone();
    }
    oracle.price.quote_asset_id = zdex_asset;
    oracle.price.zdex_asset_id = quote_asset;
    rebind_oracle(&mut candidate, oracle);
    rebind_profile(&mut candidate);

    // Act / Assert.
    assert_eq!(
        reject_code(&candidate),
        ZDEXSpotBuybackRejectCodeV1::POLICY_MISMATCH
    );
}

#[test]
fn reject_precedence_and_mutation_killers_are_exact_noops() {
    // Arrange / Act / Assert: each mutation kills a named guard.
    let mut malformed = candidate();
    malformed.authority = ZDEXSpotBuybackAuthorityInputV1::MALFORMED;
    assert_eq!(
        reject_code(&malformed),
        ZDEXSpotBuybackRejectCodeV1::AUTHORITY_MALFORMED
    );

    let mut release = candidate();
    authority_mut(&mut release).release.swap_cap_atoms = 2;
    assert_eq!(
        reject_code(&release),
        ZDEXSpotBuybackRejectCodeV1::RELEASE_MISMATCH
    );

    let mut profile = candidate();
    authority_mut(&mut profile).profile_authorization_root = root(9_001);
    assert_eq!(
        reject_code(&profile),
        ZDEXSpotBuybackRejectCodeV1::PROFILE_MISMATCH
    );

    let mut state = candidate();
    authority_mut(&mut state).spot_pre_state_root = root(9_002);
    assert_eq!(
        reject_code(&state),
        ZDEXSpotBuybackRejectCodeV1::STATE_COMMITMENT_MISMATCH
    );

    let mut quote = candidate();
    quote.quote_port.source_post_state_root = quote.quote_port.source_pre_state_root.clone();
    assert_eq!(
        reject_code(&quote),
        ZDEXSpotBuybackRejectCodeV1::QUOTE_PORT_MISMATCH
    );

    let mut oracle = candidate();
    let bad_oracle = ZDEXSpotOracleOccurrenceV1 {
        price: authority_mut(&mut oracle).oracle_occurrence.price.clone(),
        finality_root: root(96),
        status: ZDEXSpotOracleStatusV1::DISPUTED,
    };
    rebind_oracle(&mut oracle, bad_oracle);
    assert_eq!(
        reject_code(&oracle),
        ZDEXSpotBuybackRejectCodeV1::ORACLE_MISMATCH
    );

    let mut price_subject = candidate();
    price_subject.price_envelope.quote_amount_atoms = 124;
    assert_eq!(
        reject_code(&price_subject),
        ZDEXSpotBuybackRejectCodeV1::PRICE_SUBJECT_MISMATCH
    );

    let mut policy = candidate();
    authority_mut(&mut policy)
        .expected_pool_definition
        .curve_params_root = root(1);
    assert_eq!(
        reject_code(&policy),
        ZDEXSpotBuybackRejectCodeV1::POLICY_MISMATCH
    );

    let mut malformed_lane = candidate();
    let duplicate = malformed_lane.pre_state.pools[0].clone();
    let mut duplicate_state = malformed_lane.pre_state.clone();
    duplicate_state.pools.push(duplicate);
    rebind_state(&mut malformed_lane, duplicate_state);
    assert_eq!(
        reject_code(&malformed_lane),
        ZDEXSpotBuybackRejectCodeV1::LANE_MALFORMED
    );

    let mut inactive = candidate();
    let mut inactive_state = inactive.pre_state.clone();
    inactive_state.pools[0].status = ZDEXSpotPoolStatusV1::FROZEN;
    rebind_state(&mut inactive, inactive_state);
    assert_eq!(
        reject_code(&inactive),
        ZDEXSpotBuybackRejectCodeV1::POOL_INACTIVE
    );

    let mut amount = candidate();
    amount.quote_port.amount_atoms = 3_000_000_001;
    amount.price_envelope.quote_amount_atoms = 3_000_000_001;
    assert_eq!(
        reject_code(&amount),
        ZDEXSpotBuybackRejectCodeV1::AMOUNT_OUT_OF_RANGE
    );

    let mut fee = candidate();
    let mut fee_state = fee.pre_state.clone();
    fee_state.pools[0].definition.fee_bps = 10_000;
    fee_state.pools[0].pool_id = fee_state.pools[0].definition.pool_id().expect("pool id");
    rebind_governed_pool(&mut fee, fee_state.pools[0].definition.clone());
    rebind_state(&mut fee, fee_state);
    assert_eq!(
        reject_code(&fee),
        ZDEXSpotBuybackRejectCodeV1::FEE_CONSUMES_INPUT
    );

    let mut minimum = candidate();
    minimum.price_envelope.minimum_output_atoms = 112;
    assert_eq!(
        reject_code(&minimum),
        ZDEXSpotBuybackRejectCodeV1::MINIMUM_OUTPUT_MISMATCH
    );

    let mut stale = candidate();
    let mut stale_price = authority_mut(&mut stale).oracle_occurrence.price.clone();
    stale_price.observed_height = 73;
    rebind_oracle(
        &mut stale,
        ZDEXSpotOracleOccurrenceV1 {
            price: stale_price,
            finality_root: root(96),
            status: ZDEXSpotOracleStatusV1::FINAL,
        },
    );
    assert_eq!(
        reject_code(&stale),
        ZDEXSpotBuybackRejectCodeV1::PRICE_UNSAFE
    );

    let mut precedence = candidate();
    authority_mut(&mut precedence).release.swap_cap_atoms = 2;
    authority_mut(&mut precedence).profile_authorization_root = root(9_001);
    assert_eq!(
        reject_code(&precedence),
        ZDEXSpotBuybackRejectCodeV1::RELEASE_MISMATCH
    );
}

#[test]
fn pool_oracle_overflow_precedes_price_policy_and_preserves_state() {
    // Arrange: these terms overflow only in the mirrored arithmetic-admission
    // layer. The price verifier must never classify this as PRICE_UNSAFE.
    let mut candidate = candidate();
    {
        let authority = authority_mut(&mut candidate);
        authority.price_policy.maximum_pool_oracle_deviation_bps = 9_999;
        authority
            .price_policy
            .maximum_oracle_execution_deviation_bps = 0;
    }
    let mut price = authority_mut(&mut candidate)
        .oracle_occurrence
        .price
        .clone();
    price.quote_numerator_atoms = u128::MAX / 2_000_000;
    rebind_oracle(
        &mut candidate,
        ZDEXSpotOracleOccurrenceV1 {
            price,
            finality_root: root(96),
            status: ZDEXSpotOracleStatusV1::FINAL,
        },
    );
    rebind_profile(&mut candidate);

    // Act / Assert.
    assert_eq!(
        reject_code(&candidate),
        ZDEXSpotBuybackRejectCodeV1::ARITHMETIC_OUT_OF_RANGE
    );
}
