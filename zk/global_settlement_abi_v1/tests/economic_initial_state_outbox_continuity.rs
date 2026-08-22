use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    derive_economic_initial_state_outbox_continuity_root_v1, AbiErrorV1,
    EconomicInitialStateKindV1, GlobalEconomicStateV1, OutboxStateV1, OutboxStatusV1, RootV1,
    MAX_INITIAL_STATE_OUTBOX_ROWS_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "outbox continuity test root",
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

fn outbox_row(index: u64, status: OutboxStatusV1) -> OutboxStateV1 {
    OutboxStateV1 {
        effect_id: root(10_000 + index),
        destination_id: "bridge:test".to_owned(),
        payload_hash: root(20_000 + index),
        commit_id: root(30_000 + index),
        status,
    }
}

#[test]
fn migration_requires_exact_outbox_preservation() {
    // Arrange
    let mut predecessor = state_fixture();
    predecessor.outbox = vec![
        outbox_row(1, OutboxStatusV1::PENDING),
        outbox_row(2, OutboxStatusV1::ACKNOWLEDGED),
    ];
    let exact_target = predecessor.clone();
    let mut deleted = exact_target.clone();
    deleted.outbox.pop();
    let mut added = exact_target.clone();
    added.outbox.push(outbox_row(3, OutboxStatusV1::PENDING));
    let mut rewritten_effect = exact_target.clone();
    rewritten_effect.outbox[0].effect_id = root(9_999);
    let mut rewritten_destination = exact_target.clone();
    rewritten_destination.outbox[0].destination_id = "bridge:evil".to_owned();
    let mut rewritten_payload = exact_target.clone();
    rewritten_payload.outbox[0].payload_hash = root(99_001);
    let mut rewritten_commit = exact_target.clone();
    rewritten_commit.outbox[0].commit_id = root(99_002);
    let mut rewritten_status = exact_target.clone();
    rewritten_status.outbox[0].status = OutboxStatusV1::ACKNOWLEDGED;
    let mut reordered = exact_target.clone();
    reordered.outbox.reverse();

    // Act / Assert
    assert!(derive_economic_initial_state_outbox_continuity_root_v1(
        EconomicInitialStateKindV1::MIGRATION,
        &exact_target,
        Some(&predecessor),
    )
    .is_ok());
    for target in [
        &deleted,
        &added,
        &rewritten_effect,
        &rewritten_destination,
        &rewritten_payload,
        &rewritten_commit,
        &rewritten_status,
    ] {
        assert_eq!(
            derive_economic_initial_state_outbox_continuity_root_v1(
                EconomicInitialStateKindV1::MIGRATION,
                target,
                Some(&predecessor),
            ),
            Err(AbiErrorV1::InvalidBinding(
                "migration outbox predecessor preservation"
            ))
        );
    }
    assert_eq!(
        derive_economic_initial_state_outbox_continuity_root_v1(
            EconomicInitialStateKindV1::MIGRATION,
            &reordered,
            Some(&predecessor),
        ),
        Err(AbiErrorV1::InvalidOrder("global outbox"))
    );
}

#[test]
fn genesis_requires_an_empty_outbox() {
    // Arrange
    let empty = state_fixture();
    let mut nonempty = empty.clone();
    nonempty.outbox = vec![outbox_row(1, OutboxStatusV1::PENDING)];

    // Act / Assert
    assert!(derive_economic_initial_state_outbox_continuity_root_v1(
        EconomicInitialStateKindV1::GENESIS,
        &empty,
        None,
    )
    .is_ok());
    assert_eq!(
        derive_economic_initial_state_outbox_continuity_root_v1(
            EconomicInitialStateKindV1::GENESIS,
            &nonempty,
            None,
        ),
        Err(AbiErrorV1::InvalidBinding(
            "genesis outbox state must be empty"
        ))
    );
}

#[test]
fn outbox_bound_accepts_maximum_rows() {
    // Arrange
    let mut predecessor = state_fixture();
    predecessor.outbox = (0..MAX_INITIAL_STATE_OUTBOX_ROWS_V1)
        .map(|index| outbox_row(index as u64, OutboxStatusV1::PENDING))
        .collect();
    let target = predecessor.clone();

    // Act / Assert
    assert!(derive_economic_initial_state_outbox_continuity_root_v1(
        EconomicInitialStateKindV1::MIGRATION,
        &target,
        Some(&predecessor),
    )
    .is_ok());
}

#[test]
fn outbox_bound_rejects_maximum_plus_one_before_row_validation() {
    // Arrange
    let mut oversized = state_fixture();
    oversized.outbox = (0..=MAX_INITIAL_STATE_OUTBOX_ROWS_V1)
        .map(|index| outbox_row(index as u64, OutboxStatusV1::PENDING))
        .collect();
    oversized.outbox[0].destination_id.clear();

    // Act / Assert
    assert_eq!(
        derive_economic_initial_state_outbox_continuity_root_v1(
            EconomicInitialStateKindV1::GENESIS,
            &oversized,
            None,
        ),
        Err(AbiErrorV1::InvalidBounds("initial state outbox rows"))
    );
}
