//! Cross-language and adversarial evidence for Oracle occurrence authority.

use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    hash_global_v1, verify_global_oracle_occurrence_authority_v1,
    verify_global_oracle_price_occurrence_v1, AbiErrorV1, EconomicCommandOccurrenceV1,
    GlobalEconomicStateV1, GlobalOracleOccurrenceAuthorityCandidateV1,
    GlobalOracleOccurrencePolicyV1, GlobalOraclePriceOccurrenceV1, LaneIdV1, LaneStateRootV1,
    OracleOccurrenceStateV1, ReleaseStatusV1, RootV1, RouteReleaseV1, ALL_LANE_IDS_V1,
    GLOBAL_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1, GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1,
};

const ORACLE_ID: &str = "zenodex.oracle.current-dispute-status.v1";
const COMMAND_KIND: &str = "PERPS_SETTLE_EPOCH";

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "oracle authority test root",
        false,
    )
    .unwrap()
}

fn zero_root() -> RootV1 {
    RootV1::parse(ZERO_ROOT_V1, "oracle authority test zero root", true).unwrap()
}

fn policy(max_age_blocks: u64) -> GlobalOracleOccurrencePolicyV1 {
    GlobalOracleOccurrencePolicyV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        oracle_id: ORACLE_ID.to_owned(),
        max_observation_age_blocks: max_age_blocks,
    }
}

fn route(policy: &GlobalOracleOccurrencePolicyV1) -> RouteReleaseV1 {
    let ordered_lanes = vec![LaneIdV1::PERPS_MARKET];
    let module_release_ids = vec![root(101)];
    let dependency_roles = vec!["PERPS_SETTLEMENT".to_owned()];
    let port_schema_roots = vec![root(102)];
    let guest_image_id = root(103);
    let specification_root = root(104);
    let source_root = root(105);
    let toolchain_root = root(106);
    let oracle_policy_root = policy.policy_root().unwrap();
    let issue_burn_policy_root = root(107);
    let content = json!({
        "schema": GLOBAL_SETTLEMENT_ABI_V1,
        "command_kind": COMMAND_KIND,
        "ordered_lanes": ordered_lanes,
        "module_release_ids": module_release_ids,
        "dependency_roles": dependency_roles,
        "port_schema_roots": port_schema_roots,
        "guest_image_id": guest_image_id,
        "specification_root": specification_root,
        "source_root": source_root,
        "toolchain_root": toolchain_root,
        "oracle_policy_root": oracle_policy_root,
        "issue_burn_policy_root": issue_burn_policy_root,
        "max_cycles": 1_000_000,
        "max_journal_bytes": 65_536,
    });
    RouteReleaseV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        route_release_id: hash_global_v1("global-route-release-content-v1", &content).unwrap(),
        semantic_version: "1.0.0-oracle-authority-test".to_owned(),
        command_kind: COMMAND_KIND.to_owned(),
        ordered_lanes,
        module_release_ids,
        dependency_roles,
        port_schema_roots,
        guest_image_id,
        specification_root,
        source_root,
        toolchain_root,
        oracle_policy_root,
        issue_burn_policy_root,
        max_cycles: 1_000_000,
        max_journal_bytes: 65_536,
        status: ReleaseStatusV1::SHADOW,
        accepts_new_objects: false,
        evidence_statuses: vec![],
    }
}

fn state(observed_height: u64, finalized: bool) -> GlobalEconomicStateV1 {
    state_with_root(observed_height, finalized, root(501))
}

fn state_with_root(
    observed_height: u64,
    finalized: bool,
    occurrence_root: RootV1,
) -> GlobalEconomicStateV1 {
    GlobalEconomicStateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "zeno-oracle-authority-test".to_owned(),
        deployment_root: root(201),
        writer_epoch: 7,
        height: 41,
        profile_root: root(202),
        lane_roots: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane_id)| LaneStateRootV1 {
                lane_id: *lane_id,
                module_release_id: root(300 + index as u64),
                enabled: *lane_id == LaneIdV1::PERPS_MARKET,
                state_root: root(400 + index as u64),
            })
            .collect(),
        balances: vec![],
        supplies: vec![],
        custody: vec![],
        liabilities: vec![],
        reserves: vec![],
        oracle_occurrences: vec![OracleOccurrenceStateV1 {
            oracle_id: ORACLE_ID.to_owned(),
            occurrence_root,
            observed_height,
            finalized,
        }],
        replay_state: vec![],
        terminal_obligations: vec![],
        history_root: zero_root(),
        outbox: vec![],
    }
}

fn price_payload(price_e8: u128) -> GlobalOraclePriceOccurrenceV1 {
    GlobalOraclePriceOccurrenceV1 {
        schema: GLOBAL_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1.to_owned(),
        oracle_id: ORACLE_ID.to_owned(),
        market_id: "BTC-ZUSD-PERP".to_owned(),
        base_asset: "BTC".to_owned(),
        quote_asset: "zUSD".to_owned(),
        price_e8,
        observed_height: 40,
    }
}

fn occurrence(
    state: &GlobalEconomicStateV1,
    route: &RouteReleaseV1,
    consumed: Vec<String>,
) -> EconomicCommandOccurrenceV1 {
    EconomicCommandOccurrenceV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: state.chain_id.clone(),
        deployment_root: state.deployment_root.clone(),
        height: state.height + 1,
        tx_index: 0,
        op_index: 0,
        command_kind: route.command_kind.clone(),
        command_body_hash: root(601),
        route_release_id: route.route_release_id.clone(),
        subject_id: "perps-settlement-operator".to_owned(),
        grant_root: root(602),
        nonce: 1,
        profile_root: state.profile_root.clone(),
        pre_state_root: state.state_root().unwrap(),
        consumed_object_ids: consumed,
    }
}

#[test]
fn exact_route_boundary_constructs_state_bound_authority() {
    let policy = policy(2);
    let route = route(&policy);
    let state = state(40, true);
    let occurrence = occurrence(&state, &route, vec![]);

    let authority =
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &state,
            route: &route,
            occurrence: &occurrence,
            policy: &policy,
        })
        .unwrap();

    assert_eq!(authority.pre_state_root(), &state.state_root().unwrap());
    assert_eq!(authority.route_release_id(), &route.route_release_id);
    assert_eq!(
        authority.command_occurrence_id(),
        &occurrence.occurrence_id().unwrap()
    );
    assert_eq!(authority.policy_root(), &policy.policy_root().unwrap());
    assert_eq!(authority.oracle_id(), ORACLE_ID);
    assert_eq!(authority.occurrence_root(), &root(501));
    assert_eq!(authority.observed_height(), 40);
    assert_eq!(authority.state_height(), 41);
    assert_eq!(authority.evaluation_height(), 42);
    assert_eq!(authority.observation_age_blocks(), 2);
    assert_eq!(
        policy.policy_root().unwrap().as_str(),
        "0xe9236ce39308b70f6b2e762c8c87a1fda35d384e2a582067be108f693d3fda79"
    );
    assert_eq!(
        authority.authority_root().unwrap().as_str(),
        "0x00228373028ec566e41b391ee7ee4ab299b510205b54fa1f14d2af0fe0538974"
    );
}

#[test]
fn finalized_occurrence_root_binds_one_exact_price_payload() {
    let policy = policy(2);
    let route = route(&policy);
    let payload = price_payload(6_500_000_000_000);
    let state = state_with_root(40, true, payload.occurrence_root().unwrap());
    let occurrence = occurrence(&state, &route, vec![]);
    let authority =
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &state,
            route: &route,
            occurrence: &occurrence,
            policy: &policy,
        })
        .unwrap();

    let verified = verify_global_oracle_price_occurrence_v1(&authority, &payload).unwrap();

    assert_eq!(
        verified.oracle_authority_root(),
        &authority.authority_root().unwrap()
    );
    assert_eq!(
        verified.command_occurrence_id(),
        &occurrence.occurrence_id().unwrap()
    );
    assert_eq!(verified.market_id(), "BTC-ZUSD-PERP");
    assert_eq!(verified.base_asset(), "BTC");
    assert_eq!(verified.quote_asset(), "zUSD");
    assert_eq!(verified.price_e8(), 6_500_000_000_000);

    let python_parity_payload = GlobalOraclePriceOccurrenceV1 {
        schema: GLOBAL_ORACLE_PRICE_OCCURRENCE_SCHEMA_V1.to_owned(),
        oracle_id: "zenodex.oracle.perps-index-price.v1".to_owned(),
        market_id: "BTC-ZUSD-PERP".to_owned(),
        base_asset: "BTC".to_owned(),
        quote_asset: "zUSD".to_owned(),
        price_e8: 6_500_000_000_000,
        observed_height: 40,
    };
    assert_eq!(
        python_parity_payload.occurrence_root().unwrap().as_str(),
        "0x9805b6e0554b0b824cb35c5e5e9ef23bd6951a1d9ca0a6fa996ed36a94060729"
    );
}

#[test]
fn one_field_price_payload_substitutions_reject() {
    let policy = policy(2);
    let route = route(&policy);
    let payload = price_payload(6_500_000_000_000);
    let state = state_with_root(40, true, payload.occurrence_root().unwrap());
    let occurrence = occurrence(&state, &route, vec![]);
    let authority =
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &state,
            route: &route,
            occurrence: &occurrence,
            policy: &policy,
        })
        .unwrap();

    let mut substitutions = Vec::new();
    let mut market = payload.clone();
    market.market_id = "ETH-ZUSD-PERP".to_owned();
    substitutions.push(market);
    let mut base = payload.clone();
    base.base_asset = "ETH".to_owned();
    substitutions.push(base);
    let mut quote = payload.clone();
    quote.quote_asset = "USDC".to_owned();
    substitutions.push(quote);
    let mut price = payload.clone();
    price.price_e8 += 1;
    substitutions.push(price);
    let mut height = payload.clone();
    height.observed_height -= 1;
    substitutions.push(height);

    for substituted in substitutions {
        assert!(verify_global_oracle_price_occurrence_v1(&authority, &substituted).is_err());
    }
}

#[test]
fn price_boundaries_reject_zero_and_accept_one_and_u128_max() {
    assert_eq!(
        price_payload(0).validate().unwrap_err(),
        AbiErrorV1::InvalidBounds("global Oracle price e8")
    );
    for price_e8 in [1, u128::MAX] {
        let policy = policy(2);
        let route = route(&policy);
        let payload = price_payload(price_e8);
        let state = state_with_root(40, true, payload.occurrence_root().unwrap());
        let occurrence = occurrence(&state, &route, vec![]);
        let authority = verify_global_oracle_occurrence_authority_v1(
            GlobalOracleOccurrenceAuthorityCandidateV1 {
                pre_state: &state,
                route: &route,
                occurrence: &occurrence,
                policy: &policy,
            },
        )
        .unwrap();
        assert_eq!(
            verify_global_oracle_price_occurrence_v1(&authority, &payload)
                .unwrap()
                .price_e8(),
            price_e8
        );
    }
}

#[test]
fn one_block_past_maximum_age_is_rejected() {
    let policy = policy(2);
    let route = route(&policy);
    let state = state(39, true);
    let occurrence = occurrence(&state, &route, vec![]);

    let error =
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &state,
            route: &route,
            occurrence: &occurrence,
            policy: &policy,
        })
        .unwrap_err();

    assert_eq!(
        error,
        AbiErrorV1::InvalidBounds("oracle occurrence freshness")
    );
}

#[test]
fn command_height_freshness_accepts_one_and_rejects_zero_policy() {
    let accepted_policy = policy(1);
    let accepted_route = route(&accepted_policy);
    let state = state(41, true);
    let accepted_occurrence = occurrence(&state, &accepted_route, vec![]);
    let authority =
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &state,
            route: &accepted_route,
            occurrence: &accepted_occurrence,
            policy: &accepted_policy,
        })
        .unwrap();
    assert_eq!(authority.observation_age_blocks(), 1);

    let zero_policy = policy(0);
    let zero_route = route(&zero_policy);
    let zero_occurrence = occurrence(&state, &zero_route, vec![]);
    assert_eq!(
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &state,
            route: &zero_route,
            occurrence: &zero_occurrence,
            policy: &zero_policy,
        },),
        Err(AbiErrorV1::InvalidBounds("oracle occurrence freshness"))
    );
}

#[test]
fn future_and_unfinalized_occurrences_are_rejected() {
    let policy = policy(2);
    let route = route(&policy);
    for (candidate_state, expected) in [
        (
            state(42, true),
            AbiErrorV1::InvalidBounds("oracle occurrence observed height"),
        ),
        (
            state(39, false),
            AbiErrorV1::InvalidBinding("oracle occurrence finality"),
        ),
    ] {
        let occurrence = occurrence(&candidate_state, &route, vec![]);
        let error = verify_global_oracle_occurrence_authority_v1(
            GlobalOracleOccurrenceAuthorityCandidateV1 {
                pre_state: &candidate_state,
                route: &route,
                occurrence: &occurrence,
                policy: &policy,
            },
        )
        .unwrap_err();
        assert_eq!(error, expected);
    }
}

#[test]
fn finalized_oracle_is_reusable_while_missing_state_is_rejected() {
    let policy = policy(2);
    let route = route(&policy);
    let state = state(40, true);
    let reusable = occurrence(&state, &route, vec![]);
    let first =
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &state,
            route: &route,
            occurrence: &reusable,
            policy: &policy,
        })
        .unwrap();
    let second =
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &state,
            route: &route,
            occurrence: &reusable,
            policy: &policy,
        })
        .unwrap();
    assert_eq!(
        first.authority_root().unwrap(),
        second.authority_root().unwrap()
    );

    let mut missing = state;
    missing.oracle_occurrences.clear();
    let missing_occurrence = occurrence(&missing, &route, vec![]);
    let missing_error =
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &missing,
            route: &route,
            occurrence: &missing_occurrence,
            policy: &policy,
        })
        .unwrap_err();
    assert_eq!(
        missing_error,
        AbiErrorV1::InvalidBinding("route-bound oracle occurrence")
    );
}

#[test]
fn caller_selected_policy_and_stale_head_are_rejected() {
    let governed_policy = policy(2);
    let route = route(&governed_policy);
    let state = state(38, true);
    let occurrence = occurrence(&state, &route, vec![]);
    let caller_policy = policy(3);
    let policy_error =
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &state,
            route: &route,
            occurrence: &occurrence,
            policy: &caller_policy,
        })
        .unwrap_err();
    assert_eq!(
        policy_error,
        AbiErrorV1::InvalidBinding("route oracle policy root")
    );

    let mut raced_state = state;
    raced_state.history_root = root(999);
    let head_error =
        verify_global_oracle_occurrence_authority_v1(GlobalOracleOccurrenceAuthorityCandidateV1 {
            pre_state: &raced_state,
            route: &route,
            occurrence: &occurrence,
            policy: &governed_policy,
        })
        .unwrap_err();
    assert_eq!(
        head_error,
        AbiErrorV1::InvalidBinding("oracle authority command context")
    );
}
