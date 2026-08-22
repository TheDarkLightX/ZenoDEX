use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    derive_economic_initial_state_replay_continuity_root_v1, AbiErrorV1,
    EconomicInitialStateKindV1, GlobalEconomicStateV1, ReplayStateV1, RootV1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "replay continuity test root",
        false,
    )
    .unwrap()
}

fn state_fixture() -> GlobalEconomicStateV1 {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_settlement_abi_v1_golden.json");
    let fixture: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    serde_json::from_value(fixture["vectors"]["global_state"]["canonical"].clone()).unwrap()
}

#[test]
fn migration_preserves_source_rows_and_commits_target_additions() {
    // Arrange
    let mut predecessor = state_fixture();
    predecessor.replay_state = vec![ReplayStateV1 {
        replay_id: "replay-a".to_owned(),
        occurrence_id: root(9_001),
    }];
    let mut target = predecessor.clone();
    target.replay_state.push(ReplayStateV1 {
        replay_id: "replay-b".to_owned(),
        occurrence_id: root(9_002),
    });

    // Act
    let with_addition = derive_economic_initial_state_replay_continuity_root_v1(
        EconomicInitialStateKindV1::MIGRATION,
        &target,
        Some(&predecessor),
    )
    .unwrap();
    let without_addition = derive_economic_initial_state_replay_continuity_root_v1(
        EconomicInitialStateKindV1::MIGRATION,
        &predecessor,
        Some(&predecessor),
    )
    .unwrap();

    // Assert
    assert_ne!(with_addition, without_addition);
}

#[test]
fn migration_rejects_deleted_or_rewritten_source_rows() {
    // Arrange
    let mut predecessor = state_fixture();
    predecessor.replay_state = vec![ReplayStateV1 {
        replay_id: "replay-a".to_owned(),
        occurrence_id: root(9_003),
    }];
    let mut rewritten = predecessor.clone();
    rewritten.replay_state[0].occurrence_id = root(9_004);
    let mut deleted = predecessor.clone();
    deleted.replay_state.clear();

    // Act / Assert
    for target in [&rewritten, &deleted] {
        assert_eq!(
            derive_economic_initial_state_replay_continuity_root_v1(
                EconomicInitialStateKindV1::MIGRATION,
                target,
                Some(&predecessor),
            ),
            Err(AbiErrorV1::InvalidBinding(
                "migration replay predecessor preservation"
            ))
        );
    }
}

#[test]
fn genesis_requires_an_empty_replay_table() {
    // Arrange
    let empty = state_fixture();
    let mut nonempty = empty.clone();
    nonempty.replay_state = vec![ReplayStateV1 {
        replay_id: "genesis-replay".to_owned(),
        occurrence_id: root(9_005),
    }];

    // Act / Assert
    assert!(derive_economic_initial_state_replay_continuity_root_v1(
        EconomicInitialStateKindV1::GENESIS,
        &empty,
        None,
    )
    .is_ok());
    assert_eq!(
        derive_economic_initial_state_replay_continuity_root_v1(
            EconomicInitialStateKindV1::GENESIS,
            &nonempty,
            None,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "genesis replay state must be empty"
        ))
    );
}
