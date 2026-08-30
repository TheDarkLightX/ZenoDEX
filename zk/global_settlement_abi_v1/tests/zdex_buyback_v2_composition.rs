//! End-to-end SHADOW composition evidence for Phase A -> Spot V2 -> Phase B.

use zenodex_global_settlement_abi_v1::zdex_atomic_buyback_quote_port_v2::{
    ZDEXAtomicBuybackQuotePortV2, ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2,
};
use zenodex_global_settlement_abi_v1::{
    apply_final_composite_once_v2, candidate_zdex_fee_allocation_policy_v1,
    derive_zdex_tokenomics_buyback_intent_v2, terminal_from_spot_accepted_v2,
    transition_zdex_spot_buyback_v2, transition_zdex_tokenomics_buyback_v1,
    transition_zdex_tokenomics_buyback_v2, validate_route_terminal_claims_v2,
    zdex_occurrence_burn_port_v1, zdex_pool_reserve_principal_v1, EconomicEffectKindV1,
    ReleaseStatusV1, RootV1, ZDEXBuybackExecutionPolicyV1, ZDEXBuybackOraclePriceOccurrenceV1,
    ZDEXBuybackPriceSafetyPolicyV1, ZDEXBuybackRouteReceiptClaimsV2,
    ZDEXBuybackRouteTerminalInputV2, ZDEXBuybackRouteTerminalRejectCodeV2,
    ZDEXBuybackShadowComposerRejectCodeV2, ZDEXBuybackShadowComposerResultV2,
    ZDEXBuybackShadowComposerStateV2, ZDEXBuybackSpendPolicyV1, ZDEXBuybackSpendStateV1,
    ZDEXFeeDestinationAmountV1, ZDEXFeeStateV1, ZDEXHyperdeflationPolicyV1,
    ZDEXSpotBuybackAuthorityContextV1, ZDEXSpotBuybackAuthorityContextV2,
    ZDEXSpotBuybackAuthorityInputV2, ZDEXSpotBuybackInputV2, ZDEXSpotBuybackReleaseV1,
    ZDEXSpotBuybackResultV2, ZDEXSpotCurveKindV1, ZDEXSpotFlowIdentityV1, ZDEXSpotFlowIdentityV2,
    ZDEXSpotFlowRoleV1, ZDEXSpotLaneStateV1, ZDEXSpotOracleOccurrenceV1, ZDEXSpotOracleRegistryV1,
    ZDEXSpotOracleStatusV1, ZDEXSpotPoolCreationReleaseV1, ZDEXSpotPoolDefinitionV1,
    ZDEXSpotPoolStatusV1, ZDEXSpotPoolV1, ZDEXSpotPriceEnvelopeV2, ZDEXSpotProfileAuthorizationV1,
    ZDEXSpotTerminalObligationV1, ZDEXTokenomicsBuybackAuthorityContextV1,
    ZDEXTokenomicsBuybackAuthorityInputV1, ZDEXTokenomicsBuybackInputV1,
    ZDEXTokenomicsBuybackInputV2, ZDEXTokenomicsBuybackIntentInputV1,
    ZDEXTokenomicsBuybackIntentResultV2, ZDEXTokenomicsBuybackLaneStateV1,
    ZDEXTokenomicsBuybackRejectCodeV2, ZDEXTokenomicsBuybackReleaseV1,
    ZDEXTokenomicsBuybackResultV1, ZDEXTokenomicsBuybackResultV2,
    ZDEXTokenomicsProfileAuthorizationV1, ZDEXTokenomicsSafeLimitPortV1,
    ZDEXTokenomicsSpotObligationInputV1, ZDEXTokenomicsSupplyControlStateV1,
    ZDEXTokenomicsTerminalInputV2, FEE_BUYBACK_PRINCIPAL_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_SCHEMA_V1, ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1,
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1, ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1,
    ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1, ZDEX_FEE_DESTINATIONS_V1, ZERO_ROOT_V1,
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

fn composed_input() -> ZDEXTokenomicsBuybackInputV2 {
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
    ZDEXTokenomicsBuybackInputV2 {
        intent_input,
        terminal_obligation: ZDEXTokenomicsTerminalInputV2::TERMINAL(Box::new(
            terminal_from_spot_accepted_v2(&spot_accepted).expect("validated terminal"),
        )),
    }
}

#[test]
fn phase_a_spot_v2_phase_b_burns_exact_purchased_output_once() {
    let input = composed_input();
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
fn m12_v1_terminal_rewrap_is_rejected_without_a_final_effect_plan() {
    let mut input = composed_input();
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
    let mut input = composed_input();
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
    let input = composed_input();
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
    let input = composed_input();
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
fn publisher_replay_and_phase_a_double_application_are_noops() {
    let input = composed_input();
    let ZDEXTokenomicsBuybackResultV2::Accepted(accepted) =
        transition_zdex_tokenomics_buyback_v2(&input).expect("typed Phase B")
    else {
        panic!("composition must accept");
    };
    assert!(!accepted
        .phase_a_effect_plan_is_applicable()
        .expect("commitment status"));
    let claims = ZDEXBuybackRouteReceiptClaimsV2::from_terminal(
        accepted.terminal_obligation().expect("terminal"),
    )
    .expect("claims");
    let state = ZDEXBuybackShadowComposerStateV2::default();
    let ZDEXBuybackShadowComposerResultV2::Applied(applied) =
        apply_final_composite_once_v2(&state, &accepted, &claims).expect("composer")
    else {
        panic!("first final composite must be staged once");
    };
    assert!(!applied.final_effect_plan.is_empty());
    let ZDEXBuybackShadowComposerResultV2::Rejected(replayed) =
        apply_final_composite_once_v2(&applied.next_state, &accepted, &claims).expect("composer")
    else {
        panic!("replay must be a typed no-op");
    };
    assert_eq!(
        replayed.code,
        ZDEXBuybackShadowComposerRejectCodeV2::REPLAYED
    );
    assert_eq!(replayed.retained_state, applied.next_state);
    replayed.validate().expect("exact no-op");
}
