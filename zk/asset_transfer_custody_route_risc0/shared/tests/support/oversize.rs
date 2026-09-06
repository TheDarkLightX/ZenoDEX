//! Valid maximum-row fixture for the outer route size contract.

use super::*;

fn max_token(family: &str, index: usize) -> String {
    let prefix = format!("{family}{index:04}");
    assert!(prefix.len() <= MAX_TOKEN_BYTES_V1);
    format!("{prefix}{}", "x".repeat(MAX_TOKEN_BYTES_V1 - prefix.len()))
}

fn maximal_balances() -> Vec<EconomicAmountV1> {
    let mut rows = vec![
        EconomicAmountV1 {
            owner: "alice".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: 100,
        },
        EconomicAmountV1 {
            owner: "bob".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: 10,
        },
        EconomicAmountV1 {
            owner: "treasury".to_owned(),
            asset: "USD".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: 5,
        },
    ];
    rows.extend(
        (0..MAX_ASSET_BALANCE_ROWS_V1 - 3).map(|index| EconomicAmountV1 {
            owner: max_token("u", index),
            asset: "USD".to_owned(),
            custody_domain: "accounts".to_owned(),
            amount_atoms: 1,
        }),
    );
    rows
}

fn maximal_backed_liabilities() -> Vec<EconomicAmountV1> {
    (0..MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1)
        .map(|index| EconomicAmountV1 {
            owner: max_token("l", index),
            asset: "USD".to_owned(),
            custody_domain: "escrow".to_owned(),
            amount_atoms: 1,
        })
        .collect()
}

fn maximal_oracle_history() -> Vec<OracleOccurrenceStateV1> {
    (0..MAX_GLOBAL_ORACLE_ROWS_V1)
        .map(|index| OracleOccurrenceStateV1 {
            oracle_id: max_token("o", index),
            occurrence_root: root(10_000 + index as u64),
            observed_height: support::PREDECESSOR_HEIGHT,
            finalized: true,
        })
        .collect()
}

fn predecessor_replay_history() -> Vec<ReplayStateV1> {
    (0..MAX_GLOBAL_REPLAY_ROWS_V1 - 1)
        .map(|index| ReplayStateV1 {
            replay_id: max_token("r", index),
            occurrence_id: root(20_000 + index as u64),
        })
        .collect()
}

fn coherent_oversized_typed_input() -> AssetTransferCustodyRouteInputV1 {
    let custody_atoms = MAX_GLOBAL_AMOUNT_ROWS_PER_TABLE_V1 as u128;
    let mut governance = Governance::build(&Options::matching(custody_rows(custody_atoms)));
    governance.module_input.pre_state.balances = maximal_balances();
    governance.module_input.pre_state.supplies[0].amount_atoms =
        115 + (MAX_ASSET_BALANCE_ROWS_V1 - 3) as u128 + custody_atoms;
    let mut input = governance.route_input();

    let liabilities = maximal_backed_liabilities();
    input.pre_state.liabilities = liabilities.clone();
    input.post_state.liabilities = liabilities;

    let oracles = maximal_oracle_history();
    input.pre_state.oracle_occurrences = oracles.clone();
    input.post_state.oracle_occurrences = oracles;

    input.pre_state.replay_state = predecessor_replay_history();
    input.occurrence.pre_state_root = input.pre_state.state_root().unwrap();
    let occurrence_id = input.occurrence.occurrence_id().unwrap();
    assert!(input
        .pre_state
        .replay_state
        .iter()
        .all(|row| row.occurrence_id != occurrence_id));
    input.lane_input.module_input.context.command_occurrence_id = occurrence_id.clone();
    input.lane_input.coordinator_context.command_occurrence_id = occurrence_id.clone();
    input.post_state.replay_state = input.pre_state.replay_state.clone();
    input.post_state.replay_state.push(ReplayStateV1 {
        replay_id: input.occurrence.replay_id().unwrap().as_str().to_owned(),
        occurrence_id,
    });
    input
        .post_state
        .replay_state
        .sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
    input
}

#[test]
fn coherent_oversized_typed_route_rejects_at_the_same_outer_wire_ceiling() {
    const CHILD_INPUT_CEILING: usize = 1_048_576;
    let input = coherent_oversized_typed_input();
    support::assert_coherent(&input);
    input.lane_input.module_input.validate().unwrap();
    input.lane_input.coordinator_context.validate().unwrap();
    input.pre_state.validate().unwrap();
    input.post_state.validate().unwrap();

    let module_bytes = canonical_bytes_v1(&input.lane_input.module_input).unwrap();
    let lane_bytes = canonical_bytes_v1(&input.lane_input).unwrap();
    assert!(module_bytes.len() <= CHILD_INPUT_CEILING);
    assert!(lane_bytes.len() <= CHILD_INPUT_CEILING);
    let bytes = canonical_bytes_v1(&input).unwrap();
    assert!(bytes.len() > MAX_ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_BYTES_V1);

    println!(
        "canonical bytes: module={}, lane={}, route={}",
        module_bytes.len(),
        lane_bytes.len(),
        bytes.len()
    );
    assert_eq!(
        prepare_asset_transfer_custody_route_v1(input.clone()).map(|_| ()),
        Err(AssetTransferCustodyRouteErrorV1::Bounds),
    );
    assert_eq!(
        prepare_asset_transfer_custody_route_from_bytes_v1(&bytes),
        Err(AssetTransferCustodyRouteErrorV1::Bounds)
    );
    assert_eq!(
        canonical_asset_transfer_custody_route_input_bytes_v1(&input),
        Err(AssetTransferCustodyRouteErrorV1::Bounds)
    );
}
