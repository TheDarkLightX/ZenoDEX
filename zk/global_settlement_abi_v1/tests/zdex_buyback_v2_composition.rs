//! End-to-end SHADOW composition evidence for Phase A -> Spot V2 -> Phase B.

use serde::Serialize;

use zenodex_global_settlement_abi_v1::zdex_atomic_buyback_quote_port_v2::{
    ZDEXAtomicBuybackQuotePortV2, ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2,
};
use zenodex_global_settlement_abi_v1::{
    candidate_zdex_fee_allocation_policy_v1, derive_zdex_tokenomics_buyback_intent_v2,
    hash_global_v1, terminal_from_spot_accepted_v2, transition_zdex_spot_buyback_v2,
    transition_zdex_tokenomics_buyback_v1, transition_zdex_tokenomics_buyback_v2,
    validate_route_terminal_claims_v2, validate_shadow_composed_effect_plan_v2,
    zdex_occurrence_burn_port_v1, zdex_pool_reserve_principal_v1, EconomicEffectKindV1,
    GlobalEconomicEffectPlanV1, LaneIdV1, ReleaseStatusV1, RootV1, ZDEXBuybackExecutionPolicyV1,
    ZDEXBuybackOraclePriceOccurrenceV1, ZDEXBuybackPriceSafetyPolicyV1,
    ZDEXBuybackRouteReceiptClaimsV2, ZDEXBuybackRouteTerminalInputV2,
    ZDEXBuybackRouteTerminalRejectCodeV2, ZDEXBuybackShadowComposerRejectCodeV2,
    ZDEXBuybackSpendPolicyV1, ZDEXBuybackSpendStateV1, ZDEXFeeDestinationAmountV1, ZDEXFeeStateV1,
    ZDEXHyperdeflationPolicyV1, ZDEXSpotBuybackAcceptedV2, ZDEXSpotBuybackAuthorityContextV1,
    ZDEXSpotBuybackAuthorityContextV2, ZDEXSpotBuybackAuthorityInputV2, ZDEXSpotBuybackInputV2,
    ZDEXSpotBuybackReleaseV1, ZDEXSpotBuybackResultV2, ZDEXSpotCurveKindV1, ZDEXSpotFlowIdentityV1,
    ZDEXSpotFlowIdentityV2, ZDEXSpotFlowRoleV1, ZDEXSpotLaneStateV1, ZDEXSpotOracleOccurrenceV1,
    ZDEXSpotOracleRegistryV1, ZDEXSpotOracleStatusV1, ZDEXSpotPoolCreationReleaseV1,
    ZDEXSpotPoolDefinitionV1, ZDEXSpotPoolStatusV1, ZDEXSpotPoolV1, ZDEXSpotPriceEnvelopeV2,
    ZDEXSpotProfileAuthorizationV1, ZDEXSpotTerminalObligationV1,
    ZDEXTokenomicsBuybackAuthorityContextV1, ZDEXTokenomicsBuybackAuthorityInputV1,
    ZDEXTokenomicsBuybackInputV1, ZDEXTokenomicsBuybackInputV2, ZDEXTokenomicsBuybackIntentInputV1,
    ZDEXTokenomicsBuybackIntentResultV2, ZDEXTokenomicsBuybackJournalV2,
    ZDEXTokenomicsBuybackLaneStateV1, ZDEXTokenomicsBuybackRejectCodeV2,
    ZDEXTokenomicsBuybackReleaseV1, ZDEXTokenomicsBuybackResultV1, ZDEXTokenomicsBuybackResultV2,
    ZDEXTokenomicsProfileAuthorizationV1, ZDEXTokenomicsSafeLimitPortV1,
    ZDEXTokenomicsSpotObligationInputV1, ZDEXTokenomicsSupplyControlStateV1,
    ZDEXTokenomicsTerminalInputV2, FEE_BUYBACK_PRINCIPAL_V1, GLOBAL_SETTLEMENT_ABI_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_SCHEMA_V1, ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1,
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1, ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1,
    ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1, ZDEX_FEE_DESTINATIONS_V1,
    ZDEX_TOKENOMICS_RESEARCH_DRAFT_TRANSITION_JOURNAL_SCHEMA_V2, ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("fixed test root")
}

fn spot_seed() -> ZDEXSpotBuybackInputV2 {
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
    let policy = ZDEXBuybackExecutionPolicyV1 {
        schema: ZDEX_BUYBACK_EXECUTION_POLICY_SCHEMA_V1.to_owned(),
        pool_id: definition.pool_id().expect("pool id"),
        pool_definition_root: definition.definition_root().expect("definition root"),
        quote_asset_id: definition.asset0.clone(),
        zdex_asset_id: definition.asset1.clone(),
    };
    let state = ZDEXSpotLaneStateV1 {
        pools: vec![ZDEXSpotPoolV1 {
            pool_id: definition.pool_id().expect("pool id"),
            definition: definition.clone(),
            reserve0_atoms: 1_000,
            reserve1_atoms: 1_000,
            lp_supply_atoms: 1_000,
            status: ZDEXSpotPoolStatusV1::ACTIVE,
            creation_release_id: release.spot_module_release_id.clone(),
            created_height: 1,
        }],
        lp_ownership_root: root(11),
        route_batch_root: root(12),
        fee_residue_root: root(13),
        pool_terminal_obligations_root: root(14),
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
    let port = ZDEXAtomicBuybackQuotePortV2 {
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
        producer_quote_pre_state_root: port.producer_quote_pre_state_root.clone(),
        producer_quote_post_state_root: port.producer_quote_post_state_root.clone(),
        producer_quote_effect_plan_root: port.producer_quote_effect_plan_root.clone(),
        quote_port_root: port.port_root().expect("port root"),
    };
    ZDEXSpotBuybackInputV2 {
        authority: ZDEXSpotBuybackAuthorityInputV2::CONTEXT(Box::new(
            ZDEXSpotBuybackAuthorityContextV2 {
                stable_authority: authority.clone(),
            },
        )),
        pre_state: state,
        quote_port: port,
        price_envelope: ZDEXSpotPriceEnvelopeV2 {
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
        },
    }
}

fn stable_spot_authority(seed: &ZDEXSpotBuybackInputV2) -> &ZDEXSpotBuybackAuthorityContextV1 {
    match &seed.authority {
        ZDEXSpotBuybackAuthorityInputV2::CONTEXT(context) => &context.stable_authority,
        ZDEXSpotBuybackAuthorityInputV2::MALFORMED => panic!("seed authority"),
    }
}

fn phase_a_input(seed: &ZDEXSpotBuybackInputV2) -> ZDEXTokenomicsBuybackIntentInputV1 {
    let spot = stable_spot_authority(seed);
    let policy = spot.execution_policy.clone();
    let fee_policy = candidate_zdex_fee_allocation_policy_v1();
    let spend_policy = ZDEXBuybackSpendPolicyV1 {
        schema: ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1.to_owned(),
        quote_asset_id: policy.quote_asset_id.clone(),
        minimum_quote_spend_atoms: 1,
        per_command_quote_cap_atoms: 200,
        minimum_interval_blocks: 5,
    };
    let hyperdeflation = ZDEXHyperdeflationPolicyV1 {
        asset_id: policy.zdex_asset_id.clone(),
        retained_numerator: 1,
        retained_denominator: 10,
        maximum_decimals: 38,
        maximum_decimal_step: 8,
    };
    let state = ZDEXTokenomicsBuybackLaneStateV1 {
        supply: ZDEXTokenomicsSupplyControlStateV1 {
            asset_id: hyperdeflation.asset_id.clone(),
            policy_root: hyperdeflation.policy_root().expect("policy root"),
            decimals: 8,
            precision_epoch: 0,
            live_supply_atoms: 1_000,
            burn_budget_epoch: 0,
            remaining_epoch_burn_cap_atoms: 500,
        },
        fee_allocation_states: vec![ZDEXFeeStateV1 {
            fee_asset_id: policy.quote_asset_id.clone(),
            policy_root: fee_policy.policy_root().expect("policy root"),
            fee_ingress_atoms: 125,
            unallocated_reserve_atoms: 0,
            destination_balances: ZDEX_FEE_DESTINATIONS_V1
                .iter()
                .copied()
                .enumerate()
                .map(|(index, destination)| ZDEXFeeDestinationAmountV1 {
                    destination,
                    allocation_atoms: if index == 0 { 100 } else { 0 },
                })
                .collect(),
            owned_and_custodied_atoms: 10_000,
            supply_atoms: 10_000,
        }],
        buyback_cadence_states: vec![ZDEXBuybackSpendStateV1 {
            schema: ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1.to_owned(),
            quote_asset_id: policy.quote_asset_id.clone(),
            policy_root: spend_policy.policy_root().expect("policy root"),
            last_execution_height: None,
        }],
        staking_state_root: root(800),
        host_claims_state_root: root(801),
        treasury_claims_state_root: root(802),
        proof_rewards_state_root: root(803),
        cover_reserve_state_root: root(804),
        lp_rebates_state_root: root(805),
    };
    let release = ZDEXTokenomicsBuybackReleaseV1 {
        tokenomics_module_release_id: spot.tokenomics_module_release_id.clone(),
        spot_module_release_id: spot.spot_module_release_id.clone(),
        route_release_id: spot.route_release_id.clone(),
        fee_asset_count_cap: 64,
    };
    let price_policy_root = spot.price_policy.policy_root().expect("price policy root");
    let profile = ZDEXTokenomicsProfileAuthorizationV1 {
        profile_root: spot.profile_root.clone(),
        chain_id: spot.chain_id.clone(),
        deployment_root: spot.deployment_root.clone(),
        route_release_id: spot.route_release_id.clone(),
        spot_module_release_id: spot.spot_module_release_id.clone(),
        tokenomics_module_release_id: spot.tokenomics_module_release_id.clone(),
        release_root: release.release_root().expect("release root"),
        execution_policy_root: policy.policy_root().expect("policy root"),
        fee_policy_root: fee_policy.policy_root().expect("policy root"),
        spend_policy_root: spend_policy.policy_root().expect("policy root"),
        hyperdeflation_policy_root: hyperdeflation.policy_root().expect("policy root"),
        price_policy_root: price_policy_root.clone(),
    };
    let state_root = state.state_root().expect("state root");
    let authority = ZDEXTokenomicsBuybackAuthorityContextV1 {
        chain_id: spot.chain_id.clone(),
        deployment_root: spot.deployment_root.clone(),
        profile_root: spot.profile_root.clone(),
        profile_authorization_root: profile.authorization_root().expect("profile root"),
        route_release_id: spot.route_release_id.clone(),
        command_occurrence_id: spot.command_occurrence_id.clone(),
        global_pre_state_root: spot.global_pre_state_root.clone(),
        tokenomics_pre_state_root: state_root.clone(),
        writer_epoch: spot.writer_epoch,
        current_height: spot.current_height,
        spot_module_release_id: spot.spot_module_release_id.clone(),
        tokenomics_module_release_id: spot.tokenomics_module_release_id.clone(),
        price_policy_root: price_policy_root.clone(),
        release,
        execution_policy: policy.clone(),
        fee_policy,
        spend_policy,
        hyperdeflation_policy: hyperdeflation,
        profile_authorization: profile,
    };
    ZDEXTokenomicsBuybackIntentInputV1 {
        authority: ZDEXTokenomicsBuybackAuthorityInputV1::CONTEXT(Box::new(authority)),
        pre_state: state,
        safe_limit_port: ZDEXTokenomicsSafeLimitPortV1 {
            profile_root: spot.profile_root.clone(),
            route_release_id: spot.route_release_id.clone(),
            command_occurrence_id: spot.command_occurrence_id.clone(),
            global_pre_state_root: spot.global_pre_state_root.clone(),
            tokenomics_pre_state_root: state_root,
            selected_pool_id: policy.pool_id.clone(),
            quote_asset_id: policy.quote_asset_id.clone(),
            zdex_asset_id: policy.zdex_asset_id.clone(),
            price_policy_root,
            oracle_occurrence_id: spot.oracle_occurrence.occurrence_id().expect("oracle root"),
            binding_root: root(7_001),
            current_height: spot.current_height,
            route_safe_quote_limit_atoms: 200,
        },
    }
}

fn spot_with_phase_a_quote(
    seed: &ZDEXSpotBuybackInputV2,
    quote_port: ZDEXAtomicBuybackQuotePortV2,
) -> ZDEXSpotBuybackInputV2 {
    let authority = stable_spot_authority(seed);
    let coordinates = zenodex_global_settlement_abi_v1::ZDEXSpotBuybackCoordinatesV2 {
        profile_root: authority.profile_root.clone(),
        route_release_id: authority.route_release_id.clone(),
        command_occurrence_id: authority.command_occurrence_id.clone(),
        global_pre_state_root: authority.global_pre_state_root.clone(),
        spot_pre_state_root: seed.pre_state.state_root().expect("state root"),
        producer_quote_pre_state_root: quote_port.producer_quote_pre_state_root.clone(),
        producer_quote_post_state_root: quote_port.producer_quote_post_state_root.clone(),
        producer_quote_effect_plan_root: quote_port.producer_quote_effect_plan_root.clone(),
        quote_port_root: quote_port.port_root().expect("quote root"),
    };
    ZDEXSpotBuybackInputV2 {
        authority: seed.authority.clone(),
        pre_state: seed.pre_state.clone(),
        quote_port: quote_port.clone(),
        price_envelope: ZDEXSpotPriceEnvelopeV2 {
            coordinates,
            selected_pool_id: quote_port.selected_pool_id,
            oracle_occurrence_id: authority
                .oracle_occurrence
                .occurrence_id()
                .expect("oracle root"),
            oracle_finality_root: authority.oracle_occurrence.finality_root.clone(),
            quote_amount_atoms: quote_port.amount_atoms,
            current_height: authority.current_height,
            oracle_observed_height: authority.oracle_occurrence.price.observed_height,
            oracle_quote_numerator_atoms: authority.oracle_occurrence.price.quote_numerator_atoms,
            oracle_zdex_denominator_atoms: authority.oracle_occurrence.price.zdex_denominator_atoms,
            claimed_route_safe_quote_limit_atoms: 200,
            minimum_output_atoms: 101,
        },
    }
}

fn composed_input() -> (ZDEXSpotBuybackAcceptedV2, ZDEXTokenomicsBuybackInputV2) {
    let seed = spot_seed();
    let intent_input = phase_a_input(&seed);
    let ZDEXTokenomicsBuybackIntentResultV2::Accepted(intent) =
        derive_zdex_tokenomics_buyback_intent_v2(&intent_input).expect("phase A")
    else {
        panic!("phase A must accept");
    };
    assert!(!intent
        .phase_a_effect_plan_is_applicable()
        .expect("commitment status"));
    let spot = spot_with_phase_a_quote(&seed, intent.quote_output().expect("quote").clone());
    let ZDEXSpotBuybackResultV2::Accepted(spot_accepted) =
        transition_zdex_spot_buyback_v2(&spot).expect("spot transition")
    else {
        panic!("Spot V2 must accept the Phase-A quote");
    };
    let terminal = terminal_from_spot_accepted_v2(&spot_accepted).expect("validated terminal");
    (
        *spot_accepted,
        ZDEXTokenomicsBuybackInputV2 {
            intent_input,
            terminal_obligation: ZDEXTokenomicsTerminalInputV2::TERMINAL(Box::new(terminal)),
        },
    )
}

#[test]
fn phase_a_spot_v2_phase_b_burns_exact_purchased_output_once() {
    let (_, input) = composed_input();
    let ZDEXTokenomicsBuybackResultV2::Accepted(accepted) =
        transition_zdex_tokenomics_buyback_v2(&input).expect("typed Phase B")
    else {
        panic!("composition must accept");
    };
    accepted.validate().expect("accepted rederivation");
    assert!(!accepted
        .phase_a_effect_plan_is_applicable()
        .expect("commitment status"));
    let terminal = accepted.terminal_obligation().expect("terminal");
    let journal = accepted.journal().expect("journal");
    let state = accepted.post_state().expect("post state");
    assert_eq!(terminal.purchased_atoms, 111);
    assert_eq!(journal.purchased_zdex_atoms, journal.burned_zdex_atoms);
    assert_eq!(journal.burned_zdex_atoms, terminal.purchased_atoms);
    assert_eq!(state.supply.live_supply_atoms, 889);
    assert_eq!(state.supply.remaining_epoch_burn_cap_atoms, 389);
    assert_eq!(journal.retained_supply_atoms, 100);
    assert!(state.supply.live_supply_atoms >= journal.retained_supply_atoms);
    let burn_rows = accepted
        .effects()
        .expect("effects")
        .rows
        .iter()
        .filter(|row| row.kind == EconomicEffectKindV1::BURN)
        .collect::<Vec<_>>();
    assert_eq!(burn_rows.len(), 1);
    assert_eq!(burn_rows[0].delta_atoms, -111);
}

#[test]
fn tokenomics_rust_journal_uses_an_explicit_non_python_research_draft_schema() {
    assert_eq!(
        ZDEX_TOKENOMICS_RESEARCH_DRAFT_TRANSITION_JOURNAL_SCHEMA_V2,
        "zenodex/zdex-tokenomics-buyback-transition-research-draft/v2"
    );
    assert_ne!(
        ZDEX_TOKENOMICS_RESEARCH_DRAFT_TRANSITION_JOURNAL_SCHEMA_V2,
        "zenodex/zdex-tokenomics-buyback-transition-journal/v2"
    );

    let (_, input) = composed_input();
    let ZDEXTokenomicsBuybackResultV2::Accepted(accepted) =
        transition_zdex_tokenomics_buyback_v2(&input).expect("typed Phase B")
    else {
        panic!("composition must accept");
    };
    let journal = accepted.journal().expect("research draft journal");
    let actual_root = journal.journal_root().expect("research draft root");
    let expected_research_draft_root = tokenomics_journal_root_for_domain(
        journal,
        "zdex-tokenomics-buyback-transition-research-draft-v2",
        ZDEX_TOKENOMICS_RESEARCH_DRAFT_TRANSITION_JOURNAL_SCHEMA_V2,
    );
    let legacy_colliding_root = tokenomics_journal_root_for_domain(
        journal,
        "zdex-tokenomics-buyback-transition-journal-v2",
        "zenodex/zdex-tokenomics-buyback-transition-journal/v2",
    );
    assert_eq!(actual_root, expected_research_draft_root);
    assert_ne!(actual_root, legacy_colliding_root);
}

#[test]
fn m12_v1_terminal_rewrap_is_rejected_without_a_final_effect_plan() {
    let (_, mut input) = composed_input();
    let terminal = match &input.terminal_obligation {
        ZDEXTokenomicsTerminalInputV2::TERMINAL(terminal) => terminal,
        _ => panic!("fixture terminal"),
    };
    let legacy = ZDEXSpotTerminalObligationV1 {
        context_root: terminal.context.context_root().expect("context root"),
        post_state_root: terminal.post_state_root.clone(),
        consumer_module_release_id: terminal.consumer_module_release_id.clone(),
        burn_asset: terminal.burn_asset.clone(),
        burn_principal: terminal.burn_principal.clone(),
        selected_pool_id: terminal.selected_pool_id.clone(),
        quote_input_flow_id: terminal.quote_input_flow_id.clone(),
        purchased_output_flow_id: terminal.purchased_output_flow_id.clone(),
        purchased_atoms: terminal.purchased_atoms,
    };
    input.terminal_obligation = ZDEXTokenomicsTerminalInputV2::V1_REWRAP(Box::new(legacy));
    let ZDEXTokenomicsBuybackResultV2::Rejected(rejected) =
        transition_zdex_tokenomics_buyback_v2(&input).expect("typed Phase B")
    else {
        panic!("legacy rewrap must reject");
    };
    assert_eq!(
        rejected.code(),
        ZDEXTokenomicsBuybackRejectCodeV2::TERMINAL_VERSION_MISMATCH
    );
    rejected.validate().expect("exact no-op");
    assert!(rejected.effects().is_empty());
}

#[test]
fn malformed_terminal_is_rejected_before_burn() {
    let (_, mut input) = composed_input();
    let ZDEXTokenomicsTerminalInputV2::TERMINAL(terminal) = &mut input.terminal_obligation else {
        panic!("fixture terminal");
    };
    terminal.purchased_atoms = 0;
    let ZDEXTokenomicsBuybackResultV2::Rejected(rejected) =
        transition_zdex_tokenomics_buyback_v2(&input).expect("typed Phase B")
    else {
        panic!("malformed terminal must reject");
    };
    assert_eq!(
        rejected.code(),
        ZDEXTokenomicsBuybackRejectCodeV2::TERMINAL_MALFORMED
    );
    rejected.validate().expect("exact no-op");
}

#[test]
fn v1_leaf_accepts_a_coherent_caller_constructed_terminal_without_spot_provenance() {
    let (_, input) = composed_input();
    let terminal = terminal_from_input(&input);
    let ZDEXTokenomicsBuybackIntentResultV2::Accepted(phase_a) =
        derive_zdex_tokenomics_buyback_intent_v2(&input.intent_input).expect("phase A")
    else {
        panic!("phase A must accept");
    };
    let quote_port = phase_a.quote_output().expect("quote");
    let ZDEXTokenomicsBuybackAuthorityInputV1::CONTEXT(authority) = &input.intent_input.authority
    else {
        panic!("fixture authority");
    };
    let foreign_context_root = root(9_901);
    let burn_principal = zdex_occurrence_burn_port_v1(
        &authority.profile_root,
        &authority.route_release_id,
        &authority.command_occurrence_id,
    )
    .expect("burn principal");
    let legacy = ZDEXSpotTerminalObligationV1 {
        context_root: foreign_context_root.clone(),
        post_state_root: root(9_902),
        consumer_module_release_id: authority.tokenomics_module_release_id.clone(),
        burn_asset: authority.execution_policy.zdex_asset_id.clone(),
        burn_principal: burn_principal.clone(),
        selected_pool_id: authority.execution_policy.pool_id.clone(),
        quote_input_flow_id: ZDEXSpotFlowIdentityV1 {
            role: ZDEXSpotFlowRoleV1::QUOTE_INPUT,
            context_root: foreign_context_root.clone(),
            selected_pool_id: authority.execution_policy.pool_id.clone(),
            asset: authority.execution_policy.quote_asset_id.clone(),
            source_principal: FEE_BUYBACK_PRINCIPAL_V1.to_owned(),
            destination_principal: quote_port
                .destination_principal()
                .expect("quote destination"),
            amount_atoms: quote_port.amount_atoms,
        }
        .flow_id()
        .expect("quote flow"),
        purchased_output_flow_id: ZDEXSpotFlowIdentityV1 {
            role: ZDEXSpotFlowRoleV1::PURCHASED_ZDEX_OUTPUT,
            context_root: foreign_context_root,
            selected_pool_id: authority.execution_policy.pool_id.clone(),
            asset: authority.execution_policy.zdex_asset_id.clone(),
            source_principal: zdex_pool_reserve_principal_v1(
                &authority.execution_policy.pool_id,
                &authority.execution_policy.zdex_asset_id,
            )
            .expect("reserve principal"),
            destination_principal: burn_principal,
            amount_atoms: terminal.purchased_atoms,
        }
        .flow_id()
        .expect("purchased flow"),
        purchased_atoms: terminal.purchased_atoms,
    };
    let v1_input = ZDEXTokenomicsBuybackInputV1 {
        intent_input: input.intent_input,
        spot_obligation: ZDEXTokenomicsSpotObligationInputV1::OBLIGATION(Box::new(legacy)),
    };
    let ZDEXTokenomicsBuybackResultV1::Accepted(_) =
        transition_zdex_tokenomics_buyback_v1(&v1_input).expect("typed V1 leaf")
    else {
        panic!("V1 leaf accepts the coherent unauthenticated terminal");
    };
}

fn terminal_from_input(
    input: &ZDEXTokenomicsBuybackInputV2,
) -> zenodex_global_settlement_abi_v1::ZDEXSpotTerminalObligationV2 {
    match &input.terminal_obligation {
        ZDEXTokenomicsTerminalInputV2::TERMINAL(terminal) => terminal.as_ref().clone(),
        _ => panic!("fixture terminal"),
    }
}

fn rebind_terminal_flows(
    terminal: &mut zenodex_global_settlement_abi_v1::ZDEXSpotTerminalObligationV2,
    quote_port: &ZDEXAtomicBuybackQuotePortV2,
    zdex_asset: &RootV1,
) {
    terminal.burn_principal = zdex_occurrence_burn_port_v1(
        &terminal.context.coordinates.profile_root,
        &terminal.context.coordinates.route_release_id,
        &terminal.context.coordinates.command_occurrence_id,
    )
    .expect("burn principal");
    let quote = ZDEXSpotFlowIdentityV2 {
        role: ZDEXSpotFlowRoleV1::QUOTE_INPUT,
        context: terminal.context.clone(),
        selected_pool_id: terminal.selected_pool_id.clone(),
        asset: quote_port.quote_asset_id.clone(),
        source_principal: quote_port.source_principal().to_owned(),
        destination_principal: quote_port
            .destination_principal()
            .expect("quote destination"),
        amount_atoms: quote_port.amount_atoms,
    };
    terminal.quote_input_flow_id = quote.flow_id().expect("quote flow");
    let purchased = ZDEXSpotFlowIdentityV2 {
        role: ZDEXSpotFlowRoleV1::PURCHASED_ZDEX_OUTPUT,
        context: terminal.context.clone(),
        selected_pool_id: terminal.selected_pool_id.clone(),
        asset: zdex_asset.clone(),
        source_principal: zdex_pool_reserve_principal_v1(&terminal.selected_pool_id, zdex_asset)
            .expect("reserve principal"),
        destination_principal: terminal.burn_principal.clone(),
        amount_atoms: terminal.purchased_atoms,
    };
    terminal.purchased_output_flow_id = purchased.flow_id().expect("purchased flow");
}

#[test]
fn route_rejects_coherent_unauthenticated_terminal_substitution() {
    let (_, input) = composed_input();
    let terminal = terminal_from_input(&input);
    let claims = ZDEXBuybackRouteReceiptClaimsV2::from_terminal(&terminal).expect("claims");
    assert_eq!(
        validate_route_terminal_claims_v2(
            &claims,
            &ZDEXBuybackRouteTerminalInputV2::TERMINAL(Box::new(terminal.clone())),
        )
        .expect("binding"),
        Ok(())
    );

    let mut amount = terminal.clone();
    amount.purchased_atoms += 1;
    let zdex_asset = match &input.intent_input.authority {
        ZDEXTokenomicsBuybackAuthorityInputV1::CONTEXT(authority) => {
            authority.execution_policy.zdex_asset_id.clone()
        }
        _ => panic!("fixture authority"),
    };
    let ZDEXTokenomicsBuybackIntentResultV2::Accepted(phase_a) =
        derive_zdex_tokenomics_buyback_intent_v2(&input.intent_input).expect("phase A")
    else {
        panic!("phase A must accept");
    };
    let quote_port = phase_a.quote_output().expect("quote").clone();
    rebind_terminal_flows(&mut amount, &quote_port, &zdex_asset);
    assert_eq!(
        validate_route_terminal_claims_v2(
            &claims,
            &ZDEXBuybackRouteTerminalInputV2::TERMINAL(Box::new(amount)),
        )
        .expect("binding"),
        Err(ZDEXBuybackRouteTerminalRejectCodeV2::AMOUNT_MISMATCH)
    );

    let mut post_root = terminal.clone();
    post_root.post_state_root = root(9_902);
    assert_eq!(
        validate_route_terminal_claims_v2(
            &claims,
            &ZDEXBuybackRouteTerminalInputV2::TERMINAL(Box::new(post_root)),
        )
        .expect("binding"),
        Err(ZDEXBuybackRouteTerminalRejectCodeV2::POST_STATE_MISMATCH)
    );

    let mut quote_port_substitution = terminal.clone();
    quote_port_substitution.context.coordinates.quote_port_root = root(9_906);
    assert_eq!(
        validate_route_terminal_claims_v2(
            &claims,
            &ZDEXBuybackRouteTerminalInputV2::TERMINAL(Box::new(quote_port_substitution)),
        )
        .expect("binding"),
        Err(ZDEXBuybackRouteTerminalRejectCodeV2::QUOTE_PORT_MISMATCH)
    );

    let mut profile = terminal.clone();
    profile.context.coordinates.profile_root = root(9_903);
    rebind_terminal_flows(&mut profile, &quote_port, &zdex_asset);
    assert_eq!(
        validate_route_terminal_claims_v2(
            &claims,
            &ZDEXBuybackRouteTerminalInputV2::TERMINAL(Box::new(profile)),
        )
        .expect("binding"),
        Err(ZDEXBuybackRouteTerminalRejectCodeV2::PROFILE_MISMATCH)
    );

    let mut occurrence = terminal.clone();
    occurrence.context.coordinates.command_occurrence_id = root(9_904);
    rebind_terminal_flows(&mut occurrence, &quote_port, &zdex_asset);
    assert_eq!(
        validate_route_terminal_claims_v2(
            &claims,
            &ZDEXBuybackRouteTerminalInputV2::TERMINAL(Box::new(occurrence)),
        )
        .expect("binding"),
        Err(ZDEXBuybackRouteTerminalRejectCodeV2::OCCURRENCE_MISMATCH)
    );

    let mut flow = terminal.clone();
    flow.quote_input_flow_id = root(9_905);
    assert_eq!(
        validate_route_terminal_claims_v2(
            &claims,
            &ZDEXBuybackRouteTerminalInputV2::TERMINAL(Box::new(flow)),
        )
        .expect("binding"),
        Err(ZDEXBuybackRouteTerminalRejectCodeV2::FLOW_MISMATCH)
    );

    let legacy = ZDEXSpotTerminalObligationV1 {
        context_root: terminal.context.context_root().expect("context root"),
        post_state_root: terminal.post_state_root.clone(),
        consumer_module_release_id: terminal.consumer_module_release_id.clone(),
        burn_asset: terminal.burn_asset.clone(),
        burn_principal: terminal.burn_principal.clone(),
        selected_pool_id: terminal.selected_pool_id.clone(),
        quote_input_flow_id: terminal.quote_input_flow_id.clone(),
        purchased_output_flow_id: terminal.purchased_output_flow_id.clone(),
        purchased_atoms: terminal.purchased_atoms,
    };
    assert_eq!(
        validate_route_terminal_claims_v2(
            &claims,
            &ZDEXBuybackRouteTerminalInputV2::V1_REWRAP(Box::new(legacy)),
        )
        .expect("binding"),
        Err(ZDEXBuybackRouteTerminalRejectCodeV2::TERMINAL_VERSION_MISMATCH)
    );
}

#[test]
fn exact_two_lane_plan_contains_spot_pool_deltas_and_both_governed_writes() {
    let (spot_accepted, input) = composed_input();
    let ZDEXTokenomicsBuybackResultV2::Accepted(accepted) =
        transition_zdex_tokenomics_buyback_v2(&input).expect("typed Phase B")
    else {
        panic!("composition must accept");
    };
    let plan = expected_complete_plan(&spot_accepted, &accepted);
    assert_eq!(
        validate_shadow_composed_effect_plan_v2(&spot_accepted, &accepted, &plan)
            .expect("predicate"),
        Ok(())
    );
    assert_eq!(plan.lane_writes.len(), 2);
    assert_eq!(plan.lane_writes[0].lane_id, LaneIdV1::SPOT_LIQUIDITY);
    assert_eq!(plan.lane_writes[1].lane_id, LaneIdV1::ZDEX_TOKENOMICS);

    let spot_effects = spot_accepted.effects().expect("spot effects");
    assert_eq!(spot_effects.rows.len(), 2);
    assert!(plan.rows.contains(&spot_effects.rows[0]));
    assert!(plan.rows.contains(&spot_effects.rows[1]));
    assert!(spot_effects.rows.iter().any(|row| {
        row.kind == EconomicEffectKindV1::ACCOUNT_MOVEMENT && row.delta_atoms == 125
    }));
    assert!(spot_effects.rows.iter().any(|row| {
        row.kind == EconomicEffectKindV1::ACCOUNT_MOVEMENT && row.delta_atoms == -111
    }));

    let mut missing_pool_delta = plan.clone();
    missing_pool_delta
        .rows
        .retain(|row| row != &spot_effects.rows[0]);
    missing_pool_delta.validate().expect("well-formed mutant");
    assert_eq!(
        validate_shadow_composed_effect_plan_v2(&spot_accepted, &accepted, &missing_pool_delta)
            .expect("predicate"),
        Err(ZDEXBuybackShadowComposerRejectCodeV2::FINAL_EFFECT_PLAN_MISMATCH)
    );

    let mut missing_lane_write = plan.clone();
    missing_lane_write.lane_writes.remove(0);
    missing_lane_write.validate().expect("well-formed mutant");
    assert_eq!(
        validate_shadow_composed_effect_plan_v2(&spot_accepted, &accepted, &missing_lane_write)
            .expect("predicate"),
        Err(ZDEXBuybackShadowComposerRejectCodeV2::FINAL_EFFECT_PLAN_MISMATCH)
    );
}

#[test]
fn forged_coherent_terminal_and_claims_cannot_bind_to_the_real_spot_leaf() {
    let (spot_accepted, input) = composed_input();
    let mut forged_terminal = terminal_from_input(&input);
    forged_terminal.purchased_atoms = 110;
    let zdex_asset = match &input.intent_input.authority {
        ZDEXTokenomicsBuybackAuthorityInputV1::CONTEXT(authority) => {
            authority.execution_policy.zdex_asset_id.clone()
        }
        _ => panic!("fixture authority"),
    };
    let ZDEXTokenomicsBuybackIntentResultV2::Accepted(phase_a) =
        derive_zdex_tokenomics_buyback_intent_v2(&input.intent_input).expect("phase A")
    else {
        panic!("phase A must accept");
    };
    rebind_terminal_flows(
        &mut forged_terminal,
        &phase_a.quote_output().expect("quote").clone(),
        &zdex_asset,
    );
    let forged_claims =
        ZDEXBuybackRouteReceiptClaimsV2::from_terminal(&forged_terminal).expect("claims");
    assert_eq!(
        validate_route_terminal_claims_v2(
            &forged_claims,
            &ZDEXBuybackRouteTerminalInputV2::TERMINAL(Box::new(forged_terminal.clone())),
        )
        .expect("predicate"),
        Ok(())
    );

    let forged_input = ZDEXTokenomicsBuybackInputV2 {
        intent_input: input.intent_input,
        terminal_obligation: ZDEXTokenomicsTerminalInputV2::TERMINAL(Box::new(forged_terminal)),
    };
    let ZDEXTokenomicsBuybackResultV2::Accepted(forged_tokenomics) =
        transition_zdex_tokenomics_buyback_v2(&forged_input).expect("typed Phase B")
    else {
        panic!("locally coherent forged terminal reaches the research leaf");
    };
    assert_eq!(
        validate_shadow_composed_effect_plan_v2(
            &spot_accepted,
            &forged_tokenomics,
            &empty_effect_plan(),
        )
        .expect("predicate"),
        Err(ZDEXBuybackShadowComposerRejectCodeV2::CROSS_LANE_BINDING_MISMATCH)
    );
}

fn expected_complete_plan(
    spot_accepted: &ZDEXSpotBuybackAcceptedV2,
    tokenomics_accepted: &zenodex_global_settlement_abi_v1::ZDEXTokenomicsBuybackAcceptedV2,
) -> GlobalEconomicEffectPlanV1 {
    let spot_effects = spot_accepted.effects().expect("spot effects");
    let tokenomics_effects = tokenomics_accepted.effects().expect("tokenomics effects");
    assert_eq!(spot_effects.lane_writes.len(), 1);
    assert_eq!(tokenomics_effects.lane_writes.len(), 1);
    let mut rows = spot_effects.rows.clone();
    rows.extend(tokenomics_effects.rows.clone());
    rows.sort_by(|left, right| {
        (
            effect_kind_label(left.kind),
            left.asset.as_str(),
            left.principal.as_str(),
            left.custody_domain.as_str(),
        )
            .cmp(&(
                effect_kind_label(right.kind),
                right.asset.as_str(),
                right.principal.as_str(),
                right.custody_domain.as_str(),
            ))
    });
    let plan = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows,
        asset_conservation: tokenomics_effects.asset_conservation.clone(),
        fee_conservation: tokenomics_effects.fee_conservation.clone(),
        lane_writes: vec![
            spot_effects.lane_writes[0].clone(),
            tokenomics_effects.lane_writes[0].clone(),
        ],
        occurrence_consumptions: tokenomics_effects.occurrence_consumptions.clone(),
        external_outbox_enqueue: Vec::new(),
    };
    plan.validate().expect("expected complete plan");
    plan
}

fn empty_effect_plan() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: Vec::new(),
        asset_conservation: Vec::new(),
        fee_conservation: Vec::new(),
        lane_writes: Vec::new(),
        occurrence_consumptions: Vec::new(),
        external_outbox_enqueue: Vec::new(),
    }
}

fn tokenomics_journal_root_for_domain(
    journal: &ZDEXTokenomicsBuybackJournalV2,
    domain: &str,
    schema: &str,
) -> RootV1 {
    #[derive(Serialize)]
    struct Canonical<'a> {
        schema: &'a str,
        phase_a_context_root: &'a RootV1,
        quote_port_root: &'a RootV1,
        terminal_obligation_id: &'a RootV1,
        pre_state_root: &'a RootV1,
        spend_post_state_root: &'a RootV1,
        post_state_root: &'a RootV1,
        effect_plan_root: &'a RootV1,
        purchased_zdex_atoms: u128,
        burned_zdex_atoms: u128,
        live_supply_pre_atoms: u128,
        live_supply_post_atoms: u128,
        retained_supply_atoms: u128,
        remaining_epoch_burn_cap_pre_atoms: u128,
        remaining_epoch_burn_cap_post_atoms: u128,
    }
    hash_global_v1(
        domain,
        &Canonical {
            schema,
            phase_a_context_root: &journal.phase_a_context_root,
            quote_port_root: &journal.quote_port_root,
            terminal_obligation_id: &journal.terminal_obligation_id,
            pre_state_root: &journal.pre_state_root,
            spend_post_state_root: &journal.spend_post_state_root,
            post_state_root: &journal.post_state_root,
            effect_plan_root: &journal.effect_plan_root,
            purchased_zdex_atoms: journal.purchased_zdex_atoms,
            burned_zdex_atoms: journal.burned_zdex_atoms,
            live_supply_pre_atoms: journal.live_supply_pre_atoms,
            live_supply_post_atoms: journal.live_supply_post_atoms,
            retained_supply_atoms: journal.retained_supply_atoms,
            remaining_epoch_burn_cap_pre_atoms: journal.remaining_epoch_burn_cap_pre_atoms,
            remaining_epoch_burn_cap_post_atoms: journal.remaining_epoch_burn_cap_post_atoms,
        },
    )
    .expect("fixed journal hash inputs")
}

fn effect_kind_label(kind: EconomicEffectKindV1) -> &'static str {
    match kind {
        EconomicEffectKindV1::ACCOUNT_MOVEMENT => "ACCOUNT_MOVEMENT",
        EconomicEffectKindV1::ISSUE => "ISSUE",
        EconomicEffectKindV1::BURN => "BURN",
        EconomicEffectKindV1::CUSTODY => "CUSTODY",
        EconomicEffectKindV1::LIABILITY => "LIABILITY",
        EconomicEffectKindV1::RESERVE => "RESERVE",
        EconomicEffectKindV1::FEE_ALLOCATION => "FEE_ALLOCATION",
        EconomicEffectKindV1::REWARD => "REWARD",
        EconomicEffectKindV1::SLASH => "SLASH",
    }
}
