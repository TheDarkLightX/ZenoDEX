//! Source-pinned Rust parity vectors for the frozen Python Spot V2 schema.
//!
//! These vectors establish local deterministic agreement only.  They do not
//! authenticate a route receipt, publish roots, or apply an economic plan.

use zenodex_global_settlement_abi_v1::zdex_atomic_buyback_quote_port_v2::{
    ZDEXAtomicBuybackQuotePortV2, ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2,
};
use zenodex_global_settlement_abi_v1::{
    effect_plan_from_spot_accepted_v2, terminal_from_spot_accepted_v2,
    transition_zdex_spot_buyback_v1, transition_zdex_spot_buyback_v2, AbiErrorV1, ReleaseStatusV1,
    RootV1, ZDEXBuybackExecutionPolicyV1, ZDEXBuybackOraclePriceOccurrenceV1,
    ZDEXBuybackPriceSafetyPolicyV1, ZDEXSpotBuybackAuthorityContextV1,
    ZDEXSpotBuybackAuthorityContextV2, ZDEXSpotBuybackAuthorityInputV1,
    ZDEXSpotBuybackAuthorityInputV2, ZDEXSpotBuybackInputV1, ZDEXSpotBuybackInputV2,
    ZDEXSpotBuybackRejectCodeV1, ZDEXSpotBuybackRejectCodeV2, ZDEXSpotBuybackReleaseV1,
    ZDEXSpotBuybackResultV1, ZDEXSpotBuybackResultV2, ZDEXSpotCurveKindV1, ZDEXSpotLaneStateV1,
    ZDEXSpotOracleOccurrenceV1, ZDEXSpotOracleRegistryV1, ZDEXSpotOracleStatusV1,
    ZDEXSpotPoolCreationReleaseV1, ZDEXSpotPoolDefinitionV1, ZDEXSpotPoolStatusV1, ZDEXSpotPoolV1,
    ZDEXSpotPriceEnvelopeV1, ZDEXSpotPriceEnvelopeV2, ZDEXSpotProfileAuthorizationV1,
    ZDEXSpotQuoteInputPortV1, ZDEX_BUYBACK_EXECUTION_POLICY_SCHEMA_V1,
    ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1, ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1,
    ZDEX_SPOT_BUYBACK_CONTEXT_SCHEMA_V2, ZDEX_SPOT_BUYBACK_COORDINATES_SCHEMA_V2,
    ZDEX_SPOT_FLOW_SCHEMA_V2, ZDEX_SPOT_PRICE_ENVELOPE_SCHEMA_V2,
    ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V2, ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V2,
    ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V2, ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("fixed test root")
}

fn candidate() -> ZDEXSpotBuybackInputV2 {
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
    let policy = ZDEXBuybackExecutionPolicyV1 {
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
        execution_policy_root: policy.policy_root().expect("policy root"),
        price_policy_root: price_policy.policy_root().expect("policy root"),
    };
    let oracle = ZDEXSpotOracleOccurrenceV1 {
        price: ZDEXBuybackOraclePriceOccurrenceV1 {
            schema: ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1.to_owned(),
            oracle_id: price_policy.oracle_id.clone(),
            quote_asset_id: policy.quote_asset_id.clone(),
            zdex_asset_id: policy.zdex_asset_id.clone(),
            quote_numerator_atoms: 125,
            zdex_denominator_atoms: 111,
            observed_height: 76,
        },
        finality_root: root(96),
        status: ZDEXSpotOracleStatusV1::FINAL,
    };
    let authority = ZDEXSpotBuybackAuthorityContextV1 {
        chain_id: profile.chain_id.clone(),
        deployment_root: profile.deployment_root.clone(),
        profile_root: profile.profile_root.clone(),
        profile_authorization_root: profile.authorization_root().expect("profile root"),
        route_release_id: release.route_release_id.clone(),
        command_occurrence_id: root(92),
        global_pre_state_root: root(5_000),
        spot_pre_state_root: state.state_root().expect("state root"),
        writer_epoch: 0,
        current_height: 77,
        spot_module_release_id: release.spot_module_release_id.clone(),
        tokenomics_module_release_id: release.tokenomics_module_release_id.clone(),
        release,
        execution_policy: policy.clone(),
        expected_pool_definition: definition,
        price_policy,
        profile_authorization: profile,
        oracle_registry: ZDEXSpotOracleRegistryV1 {
            occurrences: vec![oracle.clone()],
        },
        oracle_occurrence: oracle.clone(),
    };
    let quote_port = ZDEXAtomicBuybackQuotePortV2 {
        schema: ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2.to_owned(),
        profile_root: authority.profile_root.clone(),
        route_release_id: authority.route_release_id.clone(),
        command_occurrence_id: authority.command_occurrence_id.clone(),
        global_pre_state_root: authority.global_pre_state_root.clone(),
        producer_module_release_id: authority.tokenomics_module_release_id.clone(),
        consumer_module_release_id: authority.spot_module_release_id.clone(),
        producer_quote_pre_state_root: root(7_001),
        producer_quote_post_state_root: root(7_002),
        producer_quote_effect_plan_root: root(7_003),
        selected_pool_id: policy.pool_id.clone(),
        quote_asset_id: policy.quote_asset_id.clone(),
        amount_atoms: 125,
    };
    let coordinates = zenodex_global_settlement_abi_v1::ZDEXSpotBuybackCoordinatesV2 {
        profile_root: authority.profile_root.clone(),
        route_release_id: authority.route_release_id.clone(),
        command_occurrence_id: authority.command_occurrence_id.clone(),
        global_pre_state_root: authority.global_pre_state_root.clone(),
        spot_pre_state_root: state.state_root().expect("state root"),
        producer_quote_pre_state_root: quote_port.producer_quote_pre_state_root.clone(),
        producer_quote_post_state_root: quote_port.producer_quote_post_state_root.clone(),
        producer_quote_effect_plan_root: quote_port.producer_quote_effect_plan_root.clone(),
        quote_port_root: quote_port.port_root().expect("port root"),
    };
    let envelope = ZDEXSpotPriceEnvelopeV2 {
        coordinates,
        selected_pool_id: policy.pool_id,
        oracle_occurrence_id: oracle.occurrence_id().expect("oracle root"),
        oracle_finality_root: oracle.finality_root,
        quote_amount_atoms: 125,
        current_height: authority.current_height,
        oracle_observed_height: oracle.price.observed_height,
        oracle_quote_numerator_atoms: oracle.price.quote_numerator_atoms,
        oracle_zdex_denominator_atoms: oracle.price.zdex_denominator_atoms,
        claimed_route_safe_quote_limit_atoms: 200,
        minimum_output_atoms: 101,
    };
    ZDEXSpotBuybackInputV2 {
        authority: ZDEXSpotBuybackAuthorityInputV2::CONTEXT(Box::new(
            ZDEXSpotBuybackAuthorityContextV2 {
                stable_authority: authority,
            },
        )),
        pre_state: state,
        quote_port,
        price_envelope: envelope,
    }
}

#[test]
fn frozen_v2_eleven_roots_match_the_python_spot_v2_contract() {
    let candidate = candidate();
    let ZDEXSpotBuybackResultV2::Accepted(accepted) =
        transition_zdex_spot_buyback_v2(&candidate).expect("typed transition")
    else {
        panic!("frozen V2 vector must accept");
    };
    accepted.validate().expect("accepted rederivation");
    let context = accepted.context().expect("context");
    let ports = accepted.ports().expect("ports");
    let journal = accepted.journal().expect("journal");
    let terminal = accepted.terminal_obligation().expect("terminal");
    assert_eq!(
        candidate.quote_port.port_root().expect("root").to_string(),
        "0xc55c0910c090ab45476f6cc773cfcebe7322842f21e083141d3ee94ef1df6c39"
    );
    assert_eq!(
        candidate.pre_state.state_root().expect("root").to_string(),
        "0x49ac89c397d72b40aafb12b556cd1cb3e7e32bf4c0189eb0c16afc5cd12517cb"
    );
    assert_eq!(
        context
            .coordinates
            .coordinates_root()
            .expect("root")
            .to_string(),
        "0x56ca299b1cc74138aac79cd4c07d0280c0d761e2e047ade2cbafe1dca05cdfd9"
    );
    assert_eq!(
        context.context_root().expect("root").to_string(),
        "0xc389a03563bb31372d241b284373fa1592795a3642c77d0dc33ff4a668f88441"
    );
    assert_eq!(
        accepted
            .post_state()
            .expect("post state")
            .state_root()
            .expect("root")
            .to_string(),
        "0xb42313a61d18805ae7745a54b5d1bdf1e58479ebeda34861942aa022bc9a1b0f"
    );
    assert_eq!(
        accepted
            .effects()
            .expect("effects")
            .effect_plan_root()
            .expect("root")
            .to_string(),
        "0xafcb6b6f8bd26a69fe8d637717450f37cc4d0f1ed380f64c19910dd01886d71a"
    );
    assert_eq!(
        ports.quote_input.flow_id().expect("root").to_string(),
        "0x99a972ab1479ca9e180939cfed54e192816eeee7302d308cc05aa56c1a0ef53e"
    );
    assert_eq!(
        ports.purchased_output.flow_id().expect("root").to_string(),
        "0xca98a627e4652ad1d0d40c0ade19b5c4e346d4dee2a310e256f76de548145152"
    );
    assert_eq!(
        ports.ports_root().expect("root").to_string(),
        "0x4c57a5a9049ec31bfa5bad0893f33bdd30b8401eadd4e701956dd899581b64ed"
    );
    assert_eq!(
        terminal.obligation_id().expect("root").to_string(),
        "0xacdc6ff9fb66b718507ce62c5bc23dc0773101e44a6ae2e75117699d3c0b09e4"
    );
    assert_eq!(
        journal.journal_root().expect("root").to_string(),
        "0x2f06748d44e4eeb7d60d0c267b8f256d22b31b529dd7f135d7d9625ae8852a4e"
    );
}

#[test]
fn stale_or_missing_authority_is_an_exact_typed_noop() {
    let mut candidate = candidate();
    candidate.authority = ZDEXSpotBuybackAuthorityInputV2::MALFORMED;
    let ZDEXSpotBuybackResultV2::Rejected(rejected) =
        transition_zdex_spot_buyback_v2(&candidate).expect("typed transition")
    else {
        panic!("malformed authority must reject");
    };
    assert_eq!(
        rejected.code(),
        ZDEXSpotBuybackRejectCodeV2::AUTHORITY_MALFORMED
    );
    rejected.validate().expect("exact no-op");
    assert_eq!(rejected.pre_state(), &candidate.pre_state);
    assert_eq!(rejected.post_state(), &candidate.pre_state);
    assert!(rejected.effects().is_empty());
    assert!(rejected.context().is_none());
    assert!(rejected.ports().is_none());
    assert!(rejected.journal().is_none());
    assert!(rejected.terminal_obligation().is_none());
}

#[test]
fn malformed_authoritative_pre_state_fails_admission_before_typed_rejection() {
    let mut malformed = candidate();
    malformed.pre_state.pools[0].pool_id = root(91_001);
    assert_eq!(
        transition_zdex_spot_buyback_v2(&malformed),
        Err(AbiErrorV1::InvalidBinding("Spot V2 state pool identity"))
    );
}

#[test]
fn host_terminal_and_effect_extraction_revalidate_the_accepted_wrapper() {
    let candidate = candidate();
    let ZDEXSpotBuybackResultV2::Accepted(accepted) =
        transition_zdex_spot_buyback_v2(&candidate).expect("typed transition")
    else {
        panic!("vector must accept");
    };
    let terminal = terminal_from_spot_accepted_v2(&accepted).expect("validated extraction");
    let effects = effect_plan_from_spot_accepted_v2(&accepted).expect("validated extraction");
    assert_eq!(terminal.purchased_atoms, 111);
    assert!(!effects.is_empty());
}

#[test]
fn m09_state_commitment_precedes_coherent_quote_and_price_defects() {
    let mut candidate = candidate();
    candidate.quote_port.selected_pool_id = root(90_001);
    candidate.price_envelope.coordinates.quote_port_root = root(90_002);
    let ZDEXSpotBuybackAuthorityInputV2::CONTEXT(authority) = &mut candidate.authority else {
        panic!("fixture authority");
    };
    authority.stable_authority.spot_pre_state_root = root(90_003);
    let ZDEXSpotBuybackResultV2::Rejected(rejected) =
        transition_zdex_spot_buyback_v2(&candidate).expect("typed transition")
    else {
        panic!("triple defect must reject");
    };
    assert_eq!(
        rejected.code(),
        ZDEXSpotBuybackRejectCodeV2::STATE_COMMITMENT_MISMATCH
    );
    rejected.validate().expect("exact no-op");
}

#[test]
fn m11_frozen_v2_schema_literals_are_exact() {
    assert_eq!(
        ZDEX_SPOT_BUYBACK_COORDINATES_SCHEMA_V2,
        "zenodex/zdex-spot-buyback-coordinates/v2"
    );
    assert_eq!(
        ZDEX_SPOT_BUYBACK_CONTEXT_SCHEMA_V2,
        "zenodex/zdex-spot-buyback-transition-context/v2"
    );
    assert_eq!(
        ZDEX_SPOT_PRICE_ENVELOPE_SCHEMA_V2,
        "zenodex/zdex-spot-price-envelope/v2"
    );
    assert_eq!(
        ZDEX_SPOT_FLOW_SCHEMA_V2,
        "zenodex/zdex-spot-buyback-flow/v2"
    );
    assert_eq!(
        ZDEX_SPOT_PRIVATE_PORTS_SCHEMA_V2,
        "zenodex/zdex-spot-private-ports/v2"
    );
    assert_eq!(
        ZDEX_SPOT_TERMINAL_OBLIGATION_SCHEMA_V2,
        "zenodex/zdex-spot-terminal-obligation/v2"
    );
    assert_eq!(
        ZDEX_SPOT_TRANSITION_JOURNAL_SCHEMA_V2,
        "zenodex/zdex-spot-buyback-transition-journal/v2"
    );
}

fn stable_v1_view(candidate: &ZDEXSpotBuybackInputV2) -> ZDEXSpotBuybackInputV1 {
    let ZDEXSpotBuybackAuthorityInputV2::CONTEXT(authority) = &candidate.authority else {
        panic!("fixture authority");
    };
    let stable = &authority.stable_authority;
    let port_root = candidate.quote_port.port_root().expect("port root");
    ZDEXSpotBuybackInputV1 {
        authority: ZDEXSpotBuybackAuthorityInputV1::CONTEXT(Box::new(stable.clone())),
        pre_state: candidate.pre_state.clone(),
        quote_port: ZDEXSpotQuoteInputPortV1 {
            profile_root: candidate.quote_port.profile_root.clone(),
            route_release_id: candidate.quote_port.route_release_id.clone(),
            command_occurrence_id: candidate.quote_port.command_occurrence_id.clone(),
            global_pre_state_root: candidate.quote_port.global_pre_state_root.clone(),
            spot_pre_state_root: candidate.pre_state.state_root().expect("state root"),
            source_module_release_id: candidate.quote_port.producer_module_release_id.clone(),
            destination_module_release_id: candidate.quote_port.consumer_module_release_id.clone(),
            source_pre_state_root: candidate.quote_port.producer_quote_pre_state_root.clone(),
            source_post_state_root: candidate.quote_port.producer_quote_post_state_root.clone(),
            source_effect_plan_root: candidate.quote_port.producer_quote_effect_plan_root.clone(),
            source_journal_root: port_root.clone(),
            source_receipt_binding_root: port_root,
            amount_atoms: candidate.quote_port.amount_atoms,
        },
        price_envelope: ZDEXSpotPriceEnvelopeV1 {
            profile_root: stable.profile_root.clone(),
            route_release_id: stable.route_release_id.clone(),
            command_occurrence_id: stable.command_occurrence_id.clone(),
            global_pre_state_root: stable.global_pre_state_root.clone(),
            spot_pre_state_root: candidate.pre_state.state_root().expect("state root"),
            selected_pool_id: candidate.price_envelope.selected_pool_id.clone(),
            oracle_occurrence_id: candidate.price_envelope.oracle_occurrence_id.clone(),
            oracle_finality_root: candidate.price_envelope.oracle_finality_root.clone(),
            quote_amount_atoms: candidate.price_envelope.quote_amount_atoms,
            current_height: candidate.price_envelope.current_height,
            oracle_observed_height: candidate.price_envelope.oracle_observed_height,
            oracle_quote_numerator_atoms: candidate.price_envelope.oracle_quote_numerator_atoms,
            oracle_zdex_denominator_atoms: candidate.price_envelope.oracle_zdex_denominator_atoms,
            claimed_route_safe_quote_limit_atoms: candidate
                .price_envelope
                .claimed_route_safe_quote_limit_atoms,
            minimum_output_atoms: candidate.price_envelope.minimum_output_atoms,
        },
    }
}

fn rebind_quote_amount(candidate: &mut ZDEXSpotBuybackInputV2) {
    candidate.price_envelope.quote_amount_atoms = candidate.quote_port.amount_atoms;
    candidate.price_envelope.coordinates.quote_port_root =
        candidate.quote_port.port_root().expect("quote root");
}

fn assert_v1_v2_replay_rejection(
    candidate: &ZDEXSpotBuybackInputV2,
    expected_v1: ZDEXSpotBuybackRejectCodeV1,
    expected_v2: ZDEXSpotBuybackRejectCodeV2,
) {
    let ZDEXSpotBuybackResultV1::Rejected(v1) =
        transition_zdex_spot_buyback_v1(&stable_v1_view(candidate)).expect("V1 transition")
    else {
        panic!("V1 replay must reject");
    };
    let ZDEXSpotBuybackResultV2::Rejected(v2) =
        transition_zdex_spot_buyback_v2(candidate).expect("V2 transition")
    else {
        panic!("V2 replay must reject");
    };
    assert_eq!(v1.code(), expected_v1);
    assert_eq!(v2.code(), expected_v2);
    v2.validate().expect("V2 exact no-op");
}

#[test]
fn m14_v1_cpmm_effects_bounds_and_price_policy_replay_through_v2() {
    let candidate = candidate();
    let ZDEXSpotBuybackResultV1::Accepted(v1) =
        transition_zdex_spot_buyback_v1(&stable_v1_view(&candidate)).expect("V1 transition")
    else {
        panic!("V1 corpus vector must accept");
    };
    let ZDEXSpotBuybackResultV2::Accepted(v2) =
        transition_zdex_spot_buyback_v2(&candidate).expect("V2 transition")
    else {
        panic!("V2 corpus vector must accept");
    };
    assert_eq!(
        v1.post_state().state_root().expect("V1 post root"),
        v2.post_state()
            .expect("V2 post state")
            .state_root()
            .expect("V2 post root")
    );
    assert_eq!(
        v1.effects().effect_plan_root().expect("V1 effects"),
        v2.effects()
            .expect("V2 effects")
            .effect_plan_root()
            .expect("V2 effects")
    );
    assert_eq!(
        v1.journal().purchased_zdex_atoms,
        v2.journal().expect("V2 journal").purchased_zdex_atoms
    );

    let mut over_swap_cap = candidate.clone();
    over_swap_cap.quote_port.amount_atoms = 3_000_000_001;
    rebind_quote_amount(&mut over_swap_cap);
    assert_v1_v2_replay_rejection(
        &over_swap_cap,
        ZDEXSpotBuybackRejectCodeV1::AMOUNT_OUT_OF_RANGE,
        ZDEXSpotBuybackRejectCodeV2::AMOUNT_OUT_OF_RANGE,
    );

    let mut minimum_output = candidate.clone();
    minimum_output.price_envelope.minimum_output_atoms = 112;
    assert_v1_v2_replay_rejection(
        &minimum_output,
        ZDEXSpotBuybackRejectCodeV1::MINIMUM_OUTPUT_MISMATCH,
        ZDEXSpotBuybackRejectCodeV2::MINIMUM_OUTPUT_MISMATCH,
    );

    let mut unsafe_price = candidate;
    unsafe_price
        .price_envelope
        .claimed_route_safe_quote_limit_atoms = 100;
    assert_v1_v2_replay_rejection(
        &unsafe_price,
        ZDEXSpotBuybackRejectCodeV1::PRICE_UNSAFE,
        ZDEXSpotBuybackRejectCodeV2::PRICE_UNSAFE,
    );
}
