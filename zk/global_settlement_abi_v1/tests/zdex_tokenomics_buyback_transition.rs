//! Rust refinement evidence for the bounded SHADOW Tokenomics buyback core.
//!
//! The literal roots below are independently pinned by
//! `tests/core/test_zdex_tokenomics_buyback_transition_v1.py`.  The composed
//! cases run the real Rust Spot leaf on the governed quote port.  This proves
//! only that the two local runtimes agree on this bounded surface; it grants
//! no route, receipt, settlement, or publication authority.

use zenodex_global_settlement_abi_v1::{
    candidate_zdex_fee_allocation_policy_v1, derive_zdex_tokenomics_buyback_intent_v1,
    transition_zdex_spot_buyback_v1, transition_zdex_tokenomics_buyback_v1, EconomicEffectKindV1,
    LaneIdV1, ReleaseStatusV1, RootV1, ZDEXBuybackExecutionPolicyV1,
    ZDEXBuybackOraclePriceOccurrenceV1, ZDEXBuybackPriceSafetyPolicyV1, ZDEXBuybackSpendPolicyV1,
    ZDEXBuybackSpendRejectCodeV1, ZDEXBuybackSpendStateV1, ZDEXFeeAllocationRejectCodeV1,
    ZDEXFeeDestinationAmountV1, ZDEXFeeStateV1, ZDEXHyperdeflationPolicyV1,
    ZDEXSpotBuybackAcceptedV1, ZDEXSpotBuybackAuthorityContextV1, ZDEXSpotBuybackAuthorityInputV1,
    ZDEXSpotBuybackInputV1, ZDEXSpotBuybackReleaseV1, ZDEXSpotBuybackResultV1, ZDEXSpotCurveKindV1,
    ZDEXSpotLaneStateV1, ZDEXSpotOracleOccurrenceV1, ZDEXSpotOracleRegistryV1,
    ZDEXSpotOracleStatusV1, ZDEXSpotPoolCreationReleaseV1, ZDEXSpotPoolDefinitionV1,
    ZDEXSpotPoolStatusV1, ZDEXSpotPoolV1, ZDEXSpotPriceEnvelopeV1, ZDEXSpotProfileAuthorizationV1,
    ZDEXSpotQuoteInputPortV1, ZDEXSpotTerminalObligationV1, ZDEXTokenomicsBurnRejectCodeV1,
    ZDEXTokenomicsBuybackAcceptedV1, ZDEXTokenomicsBuybackAuthorityContextV1,
    ZDEXTokenomicsBuybackAuthorityInputV1, ZDEXTokenomicsBuybackInputV1,
    ZDEXTokenomicsBuybackIntentInputV1, ZDEXTokenomicsBuybackIntentResultV1,
    ZDEXTokenomicsBuybackIntentV1, ZDEXTokenomicsBuybackLaneStateV1,
    ZDEXTokenomicsBuybackRejectCodeV1, ZDEXTokenomicsBuybackReleaseV1,
    ZDEXTokenomicsBuybackResultV1, ZDEXTokenomicsProfileAuthorizationV1,
    ZDEXTokenomicsSafeLimitPortV1, ZDEXTokenomicsSpotObligationInputV1,
    ZDEXTokenomicsSupplyControlStateV1, FEE_BUYBACK_PRINCIPAL_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_SCHEMA_V1, ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1,
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1, ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1,
    ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1, ZDEX_FEE_DESTINATIONS_V1, ZERO_ROOT_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("fixed test root")
}

/// The Spot Rust fixture, value-identical to `tests/zdex_spot_buyback_transition.rs`.
fn spot_candidate() -> ZDEXSpotBuybackInputV1 {
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

fn spot_authority(spot: &ZDEXSpotBuybackInputV1) -> &ZDEXSpotBuybackAuthorityContextV1 {
    match &spot.authority {
        ZDEXSpotBuybackAuthorityInputV1::CONTEXT(authority) => authority,
        ZDEXSpotBuybackAuthorityInputV1::MALFORMED => panic!("spot fixture lost authority"),
    }
}

struct Knobs {
    fee_ingress_atoms: u128,
    buyback_reserve_atoms: u128,
    live_supply_atoms: u128,
    remaining_cap_atoms: u128,
    safe_limit_atoms: u128,
    minimum_spend_atoms: u128,
    spend_cap_atoms: u128,
    last_execution_height: Option<u64>,
}

impl Default for Knobs {
    fn default() -> Self {
        Self {
            fee_ingress_atoms: 125,
            buyback_reserve_atoms: 100,
            live_supply_atoms: 1_000,
            remaining_cap_atoms: 500,
            safe_limit_atoms: 200,
            minimum_spend_atoms: 1,
            spend_cap_atoms: 200,
            last_execution_height: None,
        }
    }
}

fn intent_input(knobs: Knobs) -> ZDEXTokenomicsBuybackIntentInputV1 {
    let spot = spot_candidate();
    let spot_authority = spot_authority(&spot);
    let policy = spot_authority.execution_policy.clone();
    let fee_policy = candidate_zdex_fee_allocation_policy_v1();
    let spend_policy = ZDEXBuybackSpendPolicyV1 {
        schema: ZDEX_BUYBACK_SPEND_POLICY_SCHEMA_V1.to_owned(),
        quote_asset_id: policy.quote_asset_id.clone(),
        minimum_quote_spend_atoms: knobs.minimum_spend_atoms,
        per_command_quote_cap_atoms: knobs.spend_cap_atoms,
        minimum_interval_blocks: 5,
    };
    let hyperdeflation = ZDEXHyperdeflationPolicyV1 {
        asset_id: policy.zdex_asset_id.clone(),
        retained_numerator: 1,
        retained_denominator: 10,
        maximum_decimals: 38,
        maximum_decimal_step: 8,
    };
    let owned = (knobs.fee_ingress_atoms + knobs.buyback_reserve_atoms).max(10_000);
    let state = ZDEXTokenomicsBuybackLaneStateV1 {
        supply: ZDEXTokenomicsSupplyControlStateV1 {
            asset_id: hyperdeflation.asset_id.clone(),
            policy_root: hyperdeflation.policy_root().expect("policy root"),
            decimals: 8,
            precision_epoch: 0,
            live_supply_atoms: knobs.live_supply_atoms,
            burn_budget_epoch: 0,
            remaining_epoch_burn_cap_atoms: knobs.remaining_cap_atoms,
        },
        fee_allocation_states: vec![ZDEXFeeStateV1 {
            fee_asset_id: policy.quote_asset_id.clone(),
            policy_root: fee_policy.policy_root().expect("policy root"),
            fee_ingress_atoms: knobs.fee_ingress_atoms,
            unallocated_reserve_atoms: 0,
            destination_balances: ZDEX_FEE_DESTINATIONS_V1
                .iter()
                .copied()
                .enumerate()
                .map(|(index, destination)| ZDEXFeeDestinationAmountV1 {
                    destination,
                    allocation_atoms: if index == 0 {
                        knobs.buyback_reserve_atoms
                    } else {
                        0
                    },
                })
                .collect(),
            owned_and_custodied_atoms: owned,
            supply_atoms: owned,
        }],
        buyback_cadence_states: vec![ZDEXBuybackSpendStateV1 {
            schema: ZDEX_BUYBACK_SPEND_STATE_SCHEMA_V1.to_owned(),
            quote_asset_id: policy.quote_asset_id.clone(),
            policy_root: spend_policy.policy_root().expect("policy root"),
            last_execution_height: knobs.last_execution_height,
        }],
        staking_state_root: root(800),
        host_claims_state_root: root(801),
        treasury_claims_state_root: root(802),
        proof_rewards_state_root: root(803),
        cover_reserve_state_root: root(804),
        lp_rebates_state_root: root(805),
    };
    let release = ZDEXTokenomicsBuybackReleaseV1 {
        tokenomics_module_release_id: spot_authority.tokenomics_module_release_id.clone(),
        spot_module_release_id: spot_authority.spot_module_release_id.clone(),
        route_release_id: spot_authority.route_release_id.clone(),
        fee_asset_count_cap: 64,
    };
    let price_policy_root = spot_authority.price_policy.policy_root().expect("root");
    let profile = ZDEXTokenomicsProfileAuthorizationV1 {
        profile_root: spot_authority.profile_root.clone(),
        chain_id: spot_authority.chain_id.clone(),
        deployment_root: spot_authority.deployment_root.clone(),
        route_release_id: spot_authority.route_release_id.clone(),
        spot_module_release_id: spot_authority.spot_module_release_id.clone(),
        tokenomics_module_release_id: spot_authority.tokenomics_module_release_id.clone(),
        release_root: release.release_root().expect("root"),
        execution_policy_root: policy.policy_root().expect("root"),
        fee_policy_root: fee_policy.policy_root().expect("root"),
        spend_policy_root: spend_policy.policy_root().expect("root"),
        hyperdeflation_policy_root: hyperdeflation.policy_root().expect("root"),
        price_policy_root: price_policy_root.clone(),
    };
    let state_root = state.state_root().expect("state root");
    let authority = ZDEXTokenomicsBuybackAuthorityContextV1 {
        chain_id: spot_authority.chain_id.clone(),
        deployment_root: spot_authority.deployment_root.clone(),
        profile_root: spot_authority.profile_root.clone(),
        profile_authorization_root: profile.authorization_root().expect("root"),
        route_release_id: spot_authority.route_release_id.clone(),
        command_occurrence_id: spot_authority.command_occurrence_id.clone(),
        global_pre_state_root: spot_authority.global_pre_state_root.clone(),
        tokenomics_pre_state_root: state_root.clone(),
        writer_epoch: spot_authority.writer_epoch,
        current_height: spot_authority.current_height,
        spot_module_release_id: spot_authority.spot_module_release_id.clone(),
        tokenomics_module_release_id: spot_authority.tokenomics_module_release_id.clone(),
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
            profile_root: spot_authority.profile_root.clone(),
            route_release_id: spot_authority.route_release_id.clone(),
            command_occurrence_id: spot_authority.command_occurrence_id.clone(),
            global_pre_state_root: spot_authority.global_pre_state_root.clone(),
            tokenomics_pre_state_root: state_root,
            selected_pool_id: policy.pool_id.clone(),
            quote_asset_id: policy.quote_asset_id.clone(),
            zdex_asset_id: policy.zdex_asset_id.clone(),
            price_policy_root,
            oracle_occurrence_id: spot_authority
                .oracle_occurrence
                .occurrence_id()
                .expect("root"),
            binding_root: root(7_001),
            current_height: spot_authority.current_height,
            route_safe_quote_limit_atoms: knobs.safe_limit_atoms,
        },
    }
}

fn authority_mut(
    candidate: &mut ZDEXTokenomicsBuybackIntentInputV1,
) -> &mut ZDEXTokenomicsBuybackAuthorityContextV1 {
    match &mut candidate.authority {
        ZDEXTokenomicsBuybackAuthorityInputV1::CONTEXT(authority) => authority,
        ZDEXTokenomicsBuybackAuthorityInputV1::MALFORMED => panic!("candidate lost authority"),
    }
}

fn rebind_state(candidate: &mut ZDEXTokenomicsBuybackIntentInputV1) {
    let state_root = candidate.pre_state.state_root().expect("state root");
    candidate.safe_limit_port.tokenomics_pre_state_root = state_root.clone();
    authority_mut(candidate).tokenomics_pre_state_root = state_root;
}

fn rebind_profile(candidate: &mut ZDEXTokenomicsBuybackIntentInputV1) {
    let authority = authority_mut(candidate);
    let release_root = authority.release.release_root().expect("root");
    let execution_policy_root = authority.execution_policy.policy_root().expect("root");
    let fee_policy_root = authority.fee_policy.policy_root().expect("root");
    let spend_policy_root = authority.spend_policy.policy_root().expect("root");
    let hyperdeflation_policy_root = authority.hyperdeflation_policy.policy_root().expect("root");
    let profile = &mut authority.profile_authorization;
    profile.release_root = release_root;
    profile.execution_policy_root = execution_policy_root;
    profile.fee_policy_root = fee_policy_root;
    profile.spend_policy_root = spend_policy_root;
    profile.hyperdeflation_policy_root = hyperdeflation_policy_root;
    authority.profile_authorization_root = profile.authorization_root().expect("root");
}

fn intent(candidate: &ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackIntentV1 {
    match derive_zdex_tokenomics_buyback_intent_v1(candidate).expect("typed intent") {
        ZDEXTokenomicsBuybackIntentResultV1::Accepted(intent) => *intent,
        ZDEXTokenomicsBuybackIntentResultV1::Rejected(rejected) => {
            panic!("intent must accept: {:?}", rejected.code())
        }
    }
}

/// Spot V1 consumes the acyclic V2 port fields plus two placeholder provenance
/// roots (`source_journal_root`, `source_receipt_binding_root`).  A Spot V2
/// port without those roots is required work; nothing here claims receipt
/// authentication.
fn spot_accepted(
    intent: &ZDEXTokenomicsBuybackIntentV1,
    amount_override: Option<u128>,
) -> ZDEXSpotBuybackAcceptedV1 {
    let mut spot = spot_candidate();
    let quote = intent.quote_output();
    let amount = amount_override.unwrap_or(quote.amount_atoms);
    spot.quote_port.source_module_release_id = quote.producer_module_release_id.clone();
    spot.quote_port.destination_module_release_id = quote.consumer_module_release_id.clone();
    spot.quote_port.source_pre_state_root = quote.producer_quote_pre_state_root.clone();
    spot.quote_port.source_post_state_root = quote.producer_quote_post_state_root.clone();
    spot.quote_port.source_effect_plan_root = quote.producer_quote_effect_plan_root.clone();
    spot.quote_port.amount_atoms = amount;
    spot.price_envelope.quote_amount_atoms = amount;
    match transition_zdex_spot_buyback_v1(&spot).expect("typed spot transition") {
        ZDEXSpotBuybackResultV1::Accepted(accepted) => *accepted,
        ZDEXSpotBuybackResultV1::Rejected(rejected) => {
            panic!("spot leaf must accept: {:?}", rejected.code())
        }
    }
}

fn obligation_input(
    obligation: &ZDEXSpotTerminalObligationV1,
) -> ZDEXTokenomicsSpotObligationInputV1 {
    ZDEXTokenomicsSpotObligationInputV1::OBLIGATION(Box::new(obligation.clone()))
}

fn candidate(intent_input: ZDEXTokenomicsBuybackIntentInputV1) -> ZDEXTokenomicsBuybackInputV1 {
    let spot = spot_accepted(&intent(&intent_input), None);
    ZDEXTokenomicsBuybackInputV1 {
        intent_input,
        spot_obligation: obligation_input(spot.terminal_obligation()),
    }
}

fn accepted(candidate: &ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackAcceptedV1 {
    match transition_zdex_tokenomics_buyback_v1(candidate).expect("typed transition") {
        ZDEXTokenomicsBuybackResultV1::Accepted(accepted) => {
            accepted.validate().expect("accepted cross-bindings");
            *accepted
        }
        ZDEXTokenomicsBuybackResultV1::Rejected(rejected) => {
            panic!("transition must accept: {:?}", rejected.code())
        }
    }
}

fn reject_code(candidate: &ZDEXTokenomicsBuybackInputV1) -> ZDEXTokenomicsBuybackRejectCodeV1 {
    match transition_zdex_tokenomics_buyback_v1(candidate).expect("typed transition") {
        ZDEXTokenomicsBuybackResultV1::Rejected(rejected) => {
            rejected.validate().expect("reject invariant");
            assert_eq!(rejected.pre_state(), &candidate.intent_input.pre_state);
            assert_eq!(rejected.post_state(), &candidate.intent_input.pre_state);
            assert!(rejected.effects().is_empty());
            rejected.code()
        }
        ZDEXTokenomicsBuybackResultV1::Accepted(_) => panic!("expected exact no-op rejection"),
    }
}

fn intent_reject_code(
    candidate: &ZDEXTokenomicsBuybackIntentInputV1,
) -> ZDEXTokenomicsBuybackRejectCodeV1 {
    match derive_zdex_tokenomics_buyback_intent_v1(candidate).expect("typed intent") {
        ZDEXTokenomicsBuybackIntentResultV1::Rejected(rejected) => {
            rejected.validate().expect("reject invariant");
            assert_eq!(rejected.pre_state(), &candidate.pre_state);
            assert!(rejected.effects().is_empty());
            rejected.code()
        }
        ZDEXTokenomicsBuybackIntentResultV1::Accepted(_) => panic!("expected intent rejection"),
    }
}

fn spend_rejected(
    spend_code: ZDEXBuybackSpendRejectCodeV1,
    fee_code: Option<ZDEXFeeAllocationRejectCodeV1>,
) -> ZDEXTokenomicsBuybackRejectCodeV1 {
    ZDEXTokenomicsBuybackRejectCodeV1::SPEND_REJECTED {
        spend_code,
        fee_code,
    }
}

#[test]
fn roots_match_python_shadow_core_golden_vectors() {
    // Arrange: F=125 -> b=25, other=67, r=33; B0=100 -> q=125; p=111.
    let candidate = candidate(intent_input(Knobs::default()));

    // Act.
    let result = accepted(&candidate);

    // Assert: amounts plus the roots pinned by the Python core.
    let journal = result.journal();
    assert_eq!(
        (journal.fee_charged_atoms, journal.buyback_allocation_atoms),
        (125, 25)
    );
    assert_eq!(
        (
            journal.other_allocations_atoms,
            journal.carried_residue_atoms
        ),
        (67, 33)
    );
    assert_eq!(
        (
            journal.buyback_reserve_pre_atoms,
            journal.buyback_reserve_post_atoms
        ),
        (100, 0)
    );
    assert_eq!(
        (journal.quote_spend_atoms, journal.purchased_zdex_atoms),
        (125, 111)
    );
    assert_eq!(
        (
            journal.live_supply_pre_atoms,
            journal.live_supply_post_atoms
        ),
        (1_000, 889)
    );
    assert_eq!(journal.retained_supply_atoms, 100);
    assert_eq!(
        (
            journal.remaining_epoch_burn_cap_pre_atoms,
            journal.remaining_epoch_burn_cap_post_atoms
        ),
        (500, 389)
    );
    assert_eq!(
        journal.pre_state_root.to_string(),
        "0x44548c4fded129f4828955555b716701b5ffff55bb708e9dffdfbe0bdb7e63d0"
    );
    assert_eq!(
        journal.context_root.to_string(),
        "0xf2045fc3df8081d684d162de7827a0ed29da3f8f00a981e4d9e6bbf3e4dba560"
    );
    assert_eq!(
        journal.spend_post_state_root.to_string(),
        "0x9350876b5f505828506f098d1bff098b121a86a9857a18a464ac33ec7c5d37fb"
    );
    assert_eq!(
        journal.post_state_root.to_string(),
        "0xd130b5a2697fccd6e0b9216948c9a181edfe6a0fe200464aee22ce36f1e8a7b7"
    );
    assert_eq!(
        journal.spend_effect_plan_root.to_string(),
        "0x22edf33b9e3436a4beef01c9fdd4f3b00e68f17e7e5dee4d50c8c0bb883aea06"
    );
    assert_eq!(
        journal.quote_port_root.to_string(),
        "0x7dc8539d4dda504287cf1a05f01afda38d29ba8f094b2d7dc281b105a2064460"
    );
    assert_eq!(
        journal.effect_plan_root.to_string(),
        "0x4ecdfd59112a923527512bf6c3790ea12fe1a8b64d0f0582d2348687d196f480"
    );
    assert_eq!(
        journal.private_ports_root.to_string(),
        "0x251feb17eb4488b50a0c33ff2bca17839104692221380d9819812707078357c8"
    );
    assert_eq!(
        journal.discharged_obligation_id.to_string(),
        "0x8783d36dbb5bfad76dbf286b2bea269d36da560ef38d1ee8a5107c88fb5536ff"
    );
    assert_eq!(
        journal.journal_root().expect("root").to_string(),
        "0x8e63890c22ffb41985e051604df2ab01971500bc0c117328d247b259ee9c0381"
    );
}

#[test]
fn ports_pair_exactly_with_the_spot_leaf_and_discharge_its_obligation() {
    // Arrange.
    let intent_input = intent_input(Knobs::default());
    let intent = intent(&intent_input);
    let spot = spot_accepted(&intent, None);
    let candidate = ZDEXTokenomicsBuybackInputV1 {
        intent_input,
        spot_obligation: obligation_input(spot.terminal_obligation()),
    };

    // Act.
    let result = accepted(&candidate);

    // Assert: Lean ExactlyPaired witness plus principal-level pairing.
    assert_eq!(
        result.ports().quote_output.amount_atoms,
        spot.ports().quote_input.amount_atoms
    );
    assert_eq!(
        result.ports().burn_input.purchased_atoms,
        spot.ports().purchased_output.amount_atoms
    );
    assert_eq!(
        result.ports().quote_output.source_principal(),
        FEE_BUYBACK_PRINCIPAL_V1
    );
    assert_eq!(
        result
            .ports()
            .quote_output
            .destination_principal()
            .expect("derived destination"),
        spot.ports().quote_input.destination_principal
    );
    assert_eq!(&result.ports().burn_input, spot.terminal_obligation());
    assert_eq!(
        result.journal().discharged_obligation_id,
        spot.terminal_obligation().obligation_id().expect("root")
    );
    assert_eq!(
        result.journal().quote_port_root,
        result.quote_output().port_root().expect("root")
    );
    assert_eq!(intent.spend_post_state().supply, intent.pre_state().supply);
    assert!(intent.spend_effects().lane_writes.is_empty());
}

#[test]
fn effect_plan_has_exact_shape_and_no_ephemeral_port_row() {
    // Arrange / Act.
    let result = accepted(&candidate(intent_input(Knobs::default())));

    // Assert.
    let effects = result.effects();
    let count =
        |kind: EconomicEffectKindV1| effects.rows.iter().filter(|row| row.kind == kind).count();
    assert_eq!(count(EconomicEffectKindV1::BURN), 1);
    assert_eq!(count(EconomicEffectKindV1::CUSTODY), 2);
    assert_eq!(count(EconomicEffectKindV1::RESERVE), 1);
    assert_eq!(count(EconomicEffectKindV1::FEE_ALLOCATION), 5);
    assert_eq!(count(EconomicEffectKindV1::ACCOUNT_MOVEMENT), 0);
    let burn_principal = &result.discharged_obligation().burn_principal;
    assert!(effects
        .rows
        .iter()
        .all(|row| &row.principal != burn_principal));
    let burn_row = effects
        .rows
        .iter()
        .find(|row| row.kind == EconomicEffectKindV1::BURN)
        .expect("burn row");
    assert_eq!(burn_row.delta_atoms, -111);
    let reserve_debit = effects
        .rows
        .iter()
        .find(|row| {
            row.kind == EconomicEffectKindV1::CUSTODY && row.principal == FEE_BUYBACK_PRINCIPAL_V1
        })
        .expect("reserve debit");
    assert_eq!(reserve_debit.delta_atoms, -125);
    assert_eq!(effects.lane_writes.len(), 1);
    assert_eq!(effects.lane_writes[0].lane_id, LaneIdV1::ZDEX_TOKENOMICS);
    assert_eq!(effects.occurrence_consumptions, vec![root(92)]);
    assert!(result
        .spend_effects()
        .rows
        .iter()
        .all(|row| effects.rows.contains(row)));
}

#[test]
fn spend_selection_is_the_governed_minimum() {
    for (safe_limit_atoms, spend_cap_atoms, buyback_reserve_atoms, expected) in [
        (200, 200, 100, 125),
        (124, 200, 100, 124),
        (200, 30, 100, 30),
        (200, 200, 0, 25),
        (1, 200, 100, 1),
    ] {
        let intent = intent(&intent_input(Knobs {
            safe_limit_atoms,
            spend_cap_atoms,
            buyback_reserve_atoms,
            ..Knobs::default()
        }));
        assert_eq!(intent.quote_output().amount_atoms, expected);
        assert_eq!(
            intent.spend().fee_post_state().destination_balances[0].allocation_atoms,
            buyback_reserve_atoms + 25 - expected
        );
    }
}

#[test]
fn burn_capacity_boundaries_are_exact() {
    // Arrange: p=111; retained = ceil(live / 10).
    for (live_supply_atoms, remaining_cap_atoms, expected) in [
        (1_000, 111, None),
        (
            1_000,
            110,
            Some(ZDEXTokenomicsBurnRejectCodeV1::BURN_EXCEEDS_CAPACITY),
        ),
        (
            1_000,
            0,
            Some(ZDEXTokenomicsBurnRejectCodeV1::EPOCH_BURN_CAP_REACHED),
        ),
        (124, 500, None),
        (
            123,
            500,
            Some(ZDEXTokenomicsBurnRejectCodeV1::BURN_EXCEEDS_CAPACITY),
        ),
        (
            1,
            500,
            Some(ZDEXTokenomicsBurnRejectCodeV1::RETAINED_SUPPLY_FLOOR_REACHED),
        ),
    ] {
        let candidate = candidate(intent_input(Knobs {
            live_supply_atoms,
            remaining_cap_atoms,
            ..Knobs::default()
        }));
        match expected {
            None => {
                let result = accepted(&candidate);
                assert_eq!(
                    result.journal().live_supply_post_atoms,
                    live_supply_atoms - 111
                );
                assert!(
                    result.journal().live_supply_post_atoms
                        >= result.journal().retained_supply_atoms
                );
            }
            Some(code) => assert_eq!(
                reject_code(&candidate),
                ZDEXTokenomicsBuybackRejectCodeV1::BURN_REJECTED(code)
            ),
        }
    }
}

#[test]
fn reject_precedence_and_mutation_killers_are_exact_noops() {
    let obligation = candidate(intent_input(Knobs::default())).spot_obligation;
    let full = |intent_input: ZDEXTokenomicsBuybackIntentInputV1| ZDEXTokenomicsBuybackInputV1 {
        intent_input,
        spot_obligation: obligation.clone(),
    };

    let mut malformed = intent_input(Knobs::default());
    malformed.authority = ZDEXTokenomicsBuybackAuthorityInputV1::MALFORMED;
    assert_eq!(
        intent_reject_code(&malformed),
        ZDEXTokenomicsBuybackRejectCodeV1::AUTHORITY_MALFORMED
    );
    assert_eq!(
        reject_code(&full(malformed)),
        ZDEXTokenomicsBuybackRejectCodeV1::AUTHORITY_MALFORMED
    );

    let mut release = intent_input(Knobs::default());
    authority_mut(&mut release).release.fee_asset_count_cap = 2;
    assert_eq!(
        reject_code(&full(release)),
        ZDEXTokenomicsBuybackRejectCodeV1::RELEASE_MISMATCH
    );

    let mut profile = intent_input(Knobs::default());
    authority_mut(&mut profile).profile_authorization_root = root(9_001);
    assert_eq!(
        reject_code(&full(profile)),
        ZDEXTokenomicsBuybackRejectCodeV1::PROFILE_MISMATCH
    );

    let mut state = intent_input(Knobs::default());
    authority_mut(&mut state).tokenomics_pre_state_root = root(9_002);
    assert_eq!(
        reject_code(&full(state)),
        ZDEXTokenomicsBuybackRejectCodeV1::STATE_COMMITMENT_MISMATCH
    );

    let mut safety = intent_input(Knobs::default());
    safety.safe_limit_port.selected_pool_id = root(9_003);
    assert_eq!(
        reject_code(&full(safety)),
        ZDEXTokenomicsBuybackRejectCodeV1::SAFETY_LIMIT_MISMATCH
    );

    let mut policy = intent_input(Knobs::default());
    {
        let authority = authority_mut(&mut policy);
        authority.spend_policy.quote_asset_id = authority.execution_policy.zdex_asset_id.clone();
    }
    rebind_profile(&mut policy);
    assert_eq!(
        reject_code(&full(policy)),
        ZDEXTokenomicsBuybackRejectCodeV1::POLICY_MISMATCH
    );

    let mut lane = intent_input(Knobs::default());
    lane.pre_state.supply.decimals = 39;
    rebind_state(&mut lane);
    assert_eq!(
        reject_code(&full(lane)),
        ZDEXTokenomicsBuybackRejectCodeV1::LANE_MALFORMED
    );

    let mut selection = intent_input(Knobs::default());
    selection.pre_state.fee_allocation_states[0].policy_root = root(9_005);
    rebind_state(&mut selection);
    assert_eq!(
        reject_code(&full(selection)),
        ZDEXTokenomicsBuybackRejectCodeV1::SELECTION_MISMATCH
    );

    let cooldown = intent_input(Knobs {
        last_execution_height: Some(77),
        ..Knobs::default()
    });
    assert_eq!(
        reject_code(&full(cooldown)),
        spend_rejected(ZDEXBuybackSpendRejectCodeV1::COOLDOWN_NOT_ELAPSED, None)
    );

    let regression = intent_input(Knobs {
        last_execution_height: Some(78),
        ..Knobs::default()
    });
    assert_eq!(
        intent_reject_code(&regression),
        spend_rejected(ZDEXBuybackSpendRejectCodeV1::HEIGHT_REGRESSION, None)
    );

    let zero_fee = intent_input(Knobs {
        fee_ingress_atoms: 0,
        ..Knobs::default()
    });
    assert_eq!(
        reject_code(&full(zero_fee)),
        spend_rejected(
            ZDEXBuybackSpendRejectCodeV1::FEE_ALLOCATION_REJECTED,
            Some(ZDEXFeeAllocationRejectCodeV1::ZERO_FEE)
        )
    );

    let safe_limit_zero = intent_input(Knobs {
        safe_limit_atoms: 0,
        ..Knobs::default()
    });
    assert_eq!(
        reject_code(&full(safe_limit_zero)),
        spend_rejected(ZDEXBuybackSpendRejectCodeV1::ROUTE_SAFE_LIMIT_ZERO, None)
    );

    let below_minimum = intent_input(Knobs {
        minimum_spend_atoms: 126,
        ..Knobs::default()
    });
    assert_eq!(
        intent_reject_code(&below_minimum),
        spend_rejected(ZDEXBuybackSpendRejectCodeV1::SPEND_BELOW_MINIMUM, None)
    );

    let mut precedence = intent_input(Knobs::default());
    authority_mut(&mut precedence).release.fee_asset_count_cap = 2;
    authority_mut(&mut precedence).profile_authorization_root = root(9_001);
    assert_eq!(
        reject_code(&full(precedence)),
        ZDEXTokenomicsBuybackRejectCodeV1::RELEASE_MISMATCH
    );
}

#[test]
fn purchase_port_guards_bind_pool_asset_principal_amount_and_exact_quote() {
    let baseline = candidate(intent_input(Knobs::default()));
    let ZDEXTokenomicsSpotObligationInputV1::OBLIGATION(obligation) = &baseline.spot_obligation
    else {
        panic!("baseline must carry an obligation");
    };
    let with_obligation = |mutate: &dyn Fn(&mut ZDEXSpotTerminalObligationV1)| {
        let mut forged = obligation.as_ref().clone();
        mutate(&mut forged);
        ZDEXTokenomicsBuybackInputV1 {
            intent_input: baseline.intent_input.clone(),
            spot_obligation: obligation_input(&forged),
        }
    };

    let malformed = ZDEXTokenomicsBuybackInputV1 {
        intent_input: baseline.intent_input.clone(),
        spot_obligation: ZDEXTokenomicsSpotObligationInputV1::MALFORMED,
    };
    assert_eq!(
        reject_code(&malformed),
        ZDEXTokenomicsBuybackRejectCodeV1::PURCHASE_PORT_MISMATCH
    );
    assert_eq!(
        reject_code(&with_obligation(
            &|o| o.consumer_module_release_id = root(9_006)
        )),
        ZDEXTokenomicsBuybackRejectCodeV1::PURCHASE_PORT_MISMATCH
    );
    assert_eq!(
        reject_code(&with_obligation(&|o| o.burn_asset = root(9_007))),
        ZDEXTokenomicsBuybackRejectCodeV1::PURCHASE_PORT_MISMATCH
    );
    assert_eq!(
        reject_code(&with_obligation(
            &|o| o.burn_principal = "mallory:burn-port".to_owned()
        )),
        ZDEXTokenomicsBuybackRejectCodeV1::PURCHASE_PORT_MISMATCH
    );
    assert_eq!(
        reject_code(&with_obligation(&|o| o.selected_pool_id = root(9_008))),
        ZDEXTokenomicsBuybackRejectCodeV1::PURCHASE_PORT_MISMATCH
    );
    assert_eq!(
        reject_code(&with_obligation(&|o| o.purchased_atoms = 1)),
        ZDEXTokenomicsBuybackRejectCodeV1::PURCHASE_PORT_MISMATCH
    );
    assert_eq!(
        reject_code(&with_obligation(&|o| o.quote_input_flow_id = root(9_009))),
        ZDEXTokenomicsBuybackRejectCodeV1::QUOTE_FLOW_MISMATCH
    );

    // The Spot leaf ran with a smaller quote than the governed spend.
    let smaller = spot_accepted(&intent(&baseline.intent_input), Some(124));
    let substituted = ZDEXTokenomicsBuybackInputV1 {
        intent_input: baseline.intent_input.clone(),
        spot_obligation: obligation_input(smaller.terminal_obligation()),
    };
    assert_eq!(
        reject_code(&substituted),
        ZDEXTokenomicsBuybackRejectCodeV1::QUOTE_FLOW_MISMATCH
    );

    // A purchase-port defect precedes an exhausted burn cap.
    let mut exhausted = candidate(intent_input(Knobs {
        remaining_cap_atoms: 0,
        ..Knobs::default()
    }));
    if let ZDEXTokenomicsSpotObligationInputV1::OBLIGATION(obligation) =
        &mut exhausted.spot_obligation
    {
        obligation.consumer_module_release_id = root(9_006);
    }
    assert_eq!(
        reject_code(&exhausted),
        ZDEXTokenomicsBuybackRejectCodeV1::PURCHASE_PORT_MISMATCH
    );
}

#[test]
fn malformed_retained_inputs_reject_as_exact_noops_with_python_parity() {
    // Arrange / Act / Assert: each malformed retained input maps to the same
    // public reject family exercised by the Python hostile-object corpus.
    let mut authority = intent_input(Knobs::default());
    authority_mut(&mut authority).chain_id.clear();
    assert_eq!(
        intent_reject_code(&authority),
        ZDEXTokenomicsBuybackRejectCodeV1::AUTHORITY_MALFORMED
    );

    let mut safe_limit = intent_input(Knobs::default());
    safe_limit.safe_limit_port.route_safe_quote_limit_atoms = (i128::MAX as u128) + 1;
    assert_eq!(
        intent_reject_code(&safe_limit),
        ZDEXTokenomicsBuybackRejectCodeV1::SAFETY_LIMIT_MISMATCH
    );

    let mut obligation = candidate(intent_input(Knobs::default()));
    if let ZDEXTokenomicsSpotObligationInputV1::OBLIGATION(value) = &mut obligation.spot_obligation
    {
        value.burn_principal.clear();
    }
    assert_eq!(
        reject_code(&obligation),
        ZDEXTokenomicsBuybackRejectCodeV1::PURCHASE_PORT_MISMATCH
    );
}

#[test]
fn signed_effect_and_u128_supply_boundaries_match_python() {
    // Arrange / Act / Assert: i128 max remains live, while max+1 fails before
    // an effect row can be represented.
    let live_fee = intent_input(Knobs {
        fee_ingress_atoms: i128::MAX as u128,
        ..Knobs::default()
    });
    assert_eq!(intent(&live_fee).quote_output().amount_atoms, 200);

    let overflow_fee = intent_input(Knobs {
        fee_ingress_atoms: (i128::MAX as u128) + 1,
        ..Knobs::default()
    });
    assert_eq!(
        intent_reject_code(&overflow_fee),
        spend_rejected(
            ZDEXBuybackSpendRejectCodeV1::FEE_ALLOCATION_REJECTED,
            Some(ZDEXFeeAllocationRejectCodeV1::EFFECT_WIDTH_EXCEEDED),
        )
    );

    // The full u128 supply and epoch-cap boundary must conserve exactly after
    // the real Spot fixture determines the purchased amount.
    let boundary = candidate(intent_input(Knobs {
        live_supply_atoms: u128::MAX,
        remaining_cap_atoms: u128::MAX,
        ..Knobs::default()
    }));
    let accepted = accepted(&boundary);
    let burned = accepted.journal().burned_zdex_atoms;
    assert_eq!(
        accepted
            .post_state()
            .supply
            .live_supply_atoms
            .checked_add(burned),
        Some(u128::MAX)
    );
    assert_eq!(
        accepted
            .post_state()
            .supply
            .remaining_epoch_burn_cap_atoms
            .checked_add(burned),
        Some(u128::MAX)
    );
    let supply_row = accepted
        .effects()
        .asset_conservation
        .iter()
        .find(|row| row.authorized_burn_atoms != 0)
        .expect("burn conservation row");
    assert_eq!(
        supply_row
            .owned_and_custodied_post_atoms
            .checked_add(burned),
        Some(supply_row.owned_and_custodied_pre_atoms)
    );
    assert_eq!(
        supply_row.supply_post_atoms.checked_add(burned),
        Some(supply_row.supply_pre_atoms)
    );
}

#[test]
fn quote_port_v2_is_acyclic_and_reserved_fields_are_absent() {
    // Arrange / Act.
    let result = accepted(&candidate(intent_input(Knobs::default())));
    let port = result.quote_output();

    // Assert: the port serializes without journal or receipt-binding roots.
    let encoded = serde_json::to_value(port).expect("port encodes");
    let keys: Vec<&str> = encoded
        .as_object()
        .expect("object")
        .keys()
        .map(String::as_str)
        .collect();
    assert_eq!(keys.len(), 13);
    assert!(keys
        .iter()
        .all(|key| !key.contains("journal") && !key.contains("receipt")));
    assert_eq!(
        port.producer_quote_pre_state_root,
        result.pre_state().state_root().expect("root")
    );
    assert_eq!(
        port.producer_quote_post_state_root,
        result.spend_post_state().state_root().expect("root")
    );
    let mut cyclic = port.clone();
    cyclic.producer_quote_post_state_root = cyclic.producer_quote_pre_state_root.clone();
    assert!(cyclic.validate().is_err());
    let mut zero_amount = port.clone();
    zero_amount.amount_atoms = 0;
    assert!(zero_amount.port_root().is_err());
    let mut same_module = port.clone();
    same_module.consumer_module_release_id = same_module.producer_module_release_id.clone();
    assert!(same_module.port_root().is_err());
}
