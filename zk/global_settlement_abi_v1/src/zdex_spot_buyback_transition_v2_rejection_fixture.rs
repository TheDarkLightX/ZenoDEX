use super::*;
use crate::canonical::ZERO_ROOT_V1;
use crate::release::ReleaseStatusV1;
use crate::zdex_atomic_buyback_quote_port_v2::ZDEX_ATOMIC_BUYBACK_QUOTE_PORT_SCHEMA_V2;
use crate::zdex_buyback_price_safety::{
    ZDEXBuybackOraclePriceOccurrenceV1, ZDEXBuybackPriceSafetyPolicyV1,
    ZDEX_BUYBACK_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1, ZDEX_BUYBACK_PRICE_SAFETY_POLICY_SCHEMA_V1,
};
use crate::zdex_purchase_burn_types::{
    ZDEXBuybackExecutionPolicyV1, ZDEX_BUYBACK_EXECUTION_POLICY_SCHEMA_V1,
};
use crate::zdex_spot_buyback_transition::{
    ZDEXSpotBuybackReleaseV1, ZDEXSpotCurveKindV1, ZDEXSpotOracleOccurrenceV1,
    ZDEXSpotOracleRegistryV1, ZDEXSpotOracleStatusV1, ZDEXSpotPoolCreationReleaseV1,
    ZDEXSpotPoolDefinitionV1, ZDEXSpotPoolStatusV1, ZDEXSpotPoolV1, ZDEXSpotProfileAuthorizationV1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(format!("0x{value:064x}"), "test root", false).expect("fixed root")
}

pub(super) fn accepted_candidate() -> ZDEXSpotBuybackInputV2 {
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
        oracle_id: "zenodex-test-oracle".to_owned(),
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
    let coordinates = ZDEXSpotBuybackCoordinatesV2 {
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
    ZDEXSpotBuybackInputV2 {
        authority: ZDEXSpotBuybackAuthorityInputV2::CONTEXT(Box::new(
            ZDEXSpotBuybackAuthorityContextV2 {
                stable_authority: authority.clone(),
            },
        )),
        pre_state: state,
        quote_port,
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
