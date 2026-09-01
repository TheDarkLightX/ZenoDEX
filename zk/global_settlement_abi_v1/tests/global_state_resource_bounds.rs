use zenodex_global_settlement_abi_v1::*;

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "global-state resource-bound test root",
        false,
    )
    .unwrap()
}

fn zero_root() -> RootV1 {
    RootV1::parse(
        ZERO_ROOT_V1.to_owned(),
        "global-state resource-bound zero root",
        true,
    )
    .unwrap()
}

fn state() -> GlobalEconomicStateV1 {
    GlobalEconomicStateV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: "resource-bound-test".to_owned(),
        deployment_root: root(1),
        writer_epoch: 1,
        height: 1,
        profile_root: root(2),
        lane_roots: ALL_LANE_IDS_V1
            .iter()
            .enumerate()
            .map(|(index, lane_id)| LaneStateRootV1 {
                lane_id: *lane_id,
                module_release_id: root(100 + u64::try_from(index).unwrap()),
                enabled: false,
                state_root: zero_root(),
            })
            .collect(),
        balances: vec![],
        supplies: vec![],
        custody: vec![],
        liabilities: vec![],
        reserves: vec![],
        oracle_occurrences: vec![],
        replay_state: vec![],
        terminal_obligations: vec![],
        history_root: zero_root(),
        outbox: vec![],
    }
}

macro_rules! assert_collection_bound {
    ($field:ident, $limit:expr, $row:expr, $bound_name:literal) => {{
        let row = $row;
        let mut at_limit = state();
        at_limit.$field = vec![row.clone(); $limit];
        assert!(matches!(
            at_limit.validate(),
            Err(AbiErrorV1::InvalidOrder(_))
        ));

        let mut above_limit = state();
        above_limit.$field = vec![row; $limit + 1];
        assert_eq!(
            above_limit.validate().unwrap_err(),
            AbiErrorV1::InvalidBounds($bound_name)
        );
    }};
}

#[test]
fn global_state_collection_bounds_accept_limit_and_reject_next_before_traversal() {
    let amount = EconomicAmountV1 {
        owner: "alice".to_owned(),
        asset: "USD".to_owned(),
        custody_domain: "accounts".to_owned(),
        amount_atoms: 1,
    };
    assert_collection_bound!(
        balances,
        MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
        amount.clone(),
        "global state balances"
    );
    assert_collection_bound!(
        custody,
        MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
        amount.clone(),
        "global state custody"
    );
    assert_collection_bound!(
        liabilities,
        MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
        amount.clone(),
        "global state liabilities"
    );
    assert_collection_bound!(
        reserves,
        MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1,
        amount,
        "global state reserves"
    );
    assert_collection_bound!(
        supplies,
        MAX_GLOBAL_SUPPLY_ROWS_V1,
        AssetSupplyV1 {
            asset: "USD".to_owned(),
            amount_atoms: 1,
        },
        "global state supplies"
    );
    assert_collection_bound!(
        oracle_occurrences,
        MAX_GLOBAL_ORACLE_ROWS_V1,
        OracleOccurrenceStateV1 {
            oracle_id: "oracle-usd".to_owned(),
            occurrence_root: root(10),
            observed_height: 1,
            finalized: true,
        },
        "global state oracle occurrences"
    );
    assert_collection_bound!(
        replay_state,
        MAX_GLOBAL_REPLAY_ROWS_V1,
        ReplayStateV1 {
            replay_id: "replay-1".to_owned(),
            occurrence_id: root(11),
        },
        "global state replay state"
    );
    assert_collection_bound!(
        terminal_obligations,
        MAX_GLOBAL_TERMINAL_ROWS_V1,
        TerminalObligationV1 {
            obligation_id: "obligation-1".to_owned(),
            lane_id: LaneIdV1::ASSET_TRANSFER,
            claimant: "alice".to_owned(),
            asset: "USD".to_owned(),
            amount_atoms: 1,
            status: TerminalObligationStatusV1::OPEN,
        },
        "global state terminal obligations"
    );
    assert_collection_bound!(
        outbox,
        MAX_GLOBAL_OUTBOX_ROWS_V1,
        OutboxStateV1 {
            effect_id: root(12),
            destination_id: "registered-bridge".to_owned(),
            payload_hash: root(13),
            commit_id: root(14),
            status: OutboxStatusV1::PENDING,
        },
        "global state outbox"
    );
}

#[test]
fn global_state_resource_limits_are_frozen() {
    assert_eq!(MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1, 4_096);
    assert_eq!(MAX_GLOBAL_SUPPLY_ROWS_V1, 256);
    assert_eq!(MAX_GLOBAL_ORACLE_ROWS_V1, 4_096);
    assert_eq!(MAX_GLOBAL_REPLAY_ROWS_V1, 4_096);
    assert_eq!(MAX_GLOBAL_TERMINAL_ROWS_V1, 4_096);
    assert_eq!(MAX_GLOBAL_OUTBOX_ROWS_V1, 4_096);
}
