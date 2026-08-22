use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    derive_economic_initial_state_terminal_continuity_root_v1, AbiErrorV1,
    EconomicInitialStateKindV1, GlobalEconomicStateV1, LaneIdV1, TerminalObligationStatusV1,
    TerminalObligationV1, MAX_INITIAL_STATE_ATOM_ROWS_V1,
};

fn state_fixture() -> GlobalEconomicStateV1 {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_settlement_abi_v1_golden.json");
    let fixture: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    serde_json::from_value(fixture["vectors"]["global_state"]["canonical"].clone()).unwrap()
}

fn obligation(index: usize, status: TerminalObligationStatusV1) -> TerminalObligationV1 {
    TerminalObligationV1 {
        obligation_id: format!("obligation-{index:04}"),
        lane_id: LaneIdV1::ZUSD_MONETARY,
        claimant: format!("claimant-{index:04}"),
        asset: "zUSD".to_owned(),
        amount_atoms: u128::try_from(index).unwrap() + 1,
        status,
    }
}

#[test]
fn genesis_commits_nonempty_terminal_obligations() {
    // Arrange
    let mut state = state_fixture();
    state.terminal_obligations = vec![
        obligation(1, TerminalObligationStatusV1::OPEN),
        obligation(2, TerminalObligationStatusV1::DRAINED),
        obligation(3, TerminalObligationStatusV1::TOMBSTONED),
    ];

    // Act / Assert
    assert!(derive_economic_initial_state_terminal_continuity_root_v1(
        EconomicInitialStateKindV1::GENESIS,
        &state,
        None,
    )
    .is_ok());
}

#[test]
fn kind_requires_exact_predecessor_shape() {
    // Arrange
    let state = state_fixture();

    // Act / Assert
    assert_eq!(
        derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1::GENESIS,
            &state,
            Some(&state),
        ),
        Err(AbiErrorV1::InvalidBinding("genesis terminal predecessor"))
    );
    assert_eq!(
        derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            &state,
            None,
        ),
        Err(AbiErrorV1::InvalidBinding("migration terminal predecessor"))
    );
}

#[test]
fn migration_rejects_every_terminal_field_mutation() {
    // Arrange
    let mut predecessor = state_fixture();
    predecessor.terminal_obligations = vec![
        obligation(1, TerminalObligationStatusV1::OPEN),
        obligation(2, TerminalObligationStatusV1::DRAINED),
    ];
    let exact_target = predecessor.clone();
    let first = &exact_target.terminal_obligations[0];
    let mut mutations = Vec::new();
    let mut changed = first.clone();
    changed.obligation_id = "obligation-0000".to_owned();
    mutations.push(changed);
    let mut changed = first.clone();
    changed.lane_id = LaneIdV1::PERPS_MARKET;
    mutations.push(changed);
    let mut changed = first.clone();
    changed.claimant = "other-claimant".to_owned();
    mutations.push(changed);
    let mut changed = first.clone();
    changed.asset = "ZDEX".to_owned();
    mutations.push(changed);
    let mut changed = first.clone();
    changed.amount_atoms += 1;
    mutations.push(changed);
    let mut changed = first.clone();
    changed.status = TerminalObligationStatusV1::TOMBSTONED;
    mutations.push(changed);
    let mut changed_targets = vec![{
        let mut target = exact_target.clone();
        target.terminal_obligations.pop();
        target
    }];
    let mut added = exact_target.clone();
    added
        .terminal_obligations
        .push(obligation(3, TerminalObligationStatusV1::OPEN));
    changed_targets.push(added);
    for changed_first in mutations {
        let mut target = exact_target.clone();
        target.terminal_obligations[0] = changed_first;
        changed_targets.push(target);
    }

    // Act / Assert
    assert!(derive_economic_initial_state_terminal_continuity_root_v1(
        EconomicInitialStateKindV1::MIGRATION,
        &exact_target,
        Some(&predecessor),
    )
    .is_ok());
    for target in changed_targets {
        assert_eq!(
            derive_economic_initial_state_terminal_continuity_root_v1(
                EconomicInitialStateKindV1::MIGRATION,
                &target,
                Some(&predecessor),
            ),
            Err(AbiErrorV1::InvalidBinding(
                "migration terminal predecessor preservation"
            ))
        );
    }
    let mut reordered = exact_target;
    reordered.terminal_obligations.reverse();
    assert_eq!(
        derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            &reordered,
            Some(&predecessor),
        ),
        Err(AbiErrorV1::InvalidOrder("global terminal obligations"))
    );
}

#[test]
fn terminal_bound_accepts_maximum_rows() {
    // Arrange
    let mut predecessor = state_fixture();
    predecessor.balances.clear();
    predecessor.supplies.clear();
    predecessor.custody.clear();
    predecessor.liabilities.clear();
    predecessor.reserves.clear();
    predecessor.terminal_obligations = (0..MAX_INITIAL_STATE_ATOM_ROWS_V1)
        .map(|index| obligation(index, TerminalObligationStatusV1::OPEN))
        .collect();
    let target = predecessor.clone();

    // Act / Assert
    assert!(derive_economic_initial_state_terminal_continuity_root_v1(
        EconomicInitialStateKindV1::MIGRATION,
        &target,
        Some(&predecessor),
    )
    .is_ok());
}

#[test]
fn terminal_bound_rejects_maximum_plus_one_before_row_validation() {
    // Arrange
    let mut oversized = state_fixture();
    oversized.balances.clear();
    oversized.supplies.clear();
    oversized.custody.clear();
    oversized.liabilities.clear();
    oversized.reserves.clear();
    oversized.terminal_obligations = (0..=MAX_INITIAL_STATE_ATOM_ROWS_V1)
        .map(|index| obligation(index, TerminalObligationStatusV1::OPEN))
        .collect();
    oversized.terminal_obligations[0].claimant.clear();

    // Act / Assert
    assert_eq!(
        derive_economic_initial_state_terminal_continuity_root_v1(
            EconomicInitialStateKindV1::GENESIS,
            &oversized,
            None,
        ),
        Err(AbiErrorV1::InvalidBounds(
            "initial state explicit value rows"
        ))
    );
}
