//! Python/Rust vectors for the owned, data-only epoch state constructor.
//!
//! The fixture is a structural parity record with authority `NONE`. The
//! existing epoch relation checks allocation content after projection.

use std::fs;
use std::path::PathBuf;

use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, check_asset_transfer_epoch_allocation_v1, hash_bytes_sha256_v1,
    project_asset_transfer_epoch_position_v1, AbiErrorV1, AssetTransferEpochPositionV1,
    AssetTransferGlobalAllocationCandidateV1, AssetTransferLaneModuleAcceptedV1,
    EconomicCommandOccurrenceV1, GlobalEconomicStateV1, ReplayStateV1, RootV1,
    MAX_EPOCH_COMMANDS_V1, MAX_GLOBAL_REPLAY_ROWS_V1,
};

const FIXTURE_SCHEMA: &str = "zenodex/asset-transfer-epoch-projection-golden/v1";

fn fixture() -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/data/asset_transfer_epoch_projection_v1_golden.json");
    serde_json::from_slice(&fs::read(path).expect("projection fixture readable"))
        .expect("projection fixture JSON")
}

fn text<'a>(value: &'a Value, field: &str) -> &'a str {
    value[field]
        .as_str()
        .unwrap_or_else(|| panic!("{field} must be text"))
}

fn row_named<'a>(fixture: &'a Value, name: &str) -> &'a Value {
    fixture["cases"]
        .as_array()
        .expect("projection cases")
        .iter()
        .find(|row| row["name"].as_str() == Some(name))
        .unwrap_or_else(|| panic!("missing projection case {name}"))
}

fn expected_bytes(value: &str) -> Vec<u8> {
    let hex_value = value.strip_prefix("0x").unwrap_or(value);
    hex::decode(hex_value).expect("canonical current bytes")
}

fn source_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .to_path_buf()
}

fn assert_source_pins(fixture: &Value) {
    for (path, expected) in fixture["source_sha256"]
        .as_object()
        .expect("source hash map")
    {
        let file = source_root().join(path);
        let digest = hash_bytes_sha256_v1(
            &fs::read(&file)
                .unwrap_or_else(|error| panic!("source pin path {path} unreadable: {error}")),
        );
        let expected = expected
            .as_str()
            .unwrap_or_else(|| panic!("source digest must be text"));
        let expected = expected.strip_prefix("0x").unwrap_or(expected);
        assert_eq!(digest, expected, "source pin {path}");
    }
}

fn typed_case(
    row: &Value,
) -> (
    AssetTransferLaneModuleAcceptedV1,
    EconomicCommandOccurrenceV1,
    GlobalEconomicStateV1,
    GlobalEconomicStateV1,
    usize,
) {
    (
        serde_json::from_value(row["accepted"].clone()).expect("accepted value"),
        serde_json::from_value(row["occurrence"].clone()).expect("occurrence value"),
        serde_json::from_value(row["predecessor"].clone()).expect("predecessor value"),
        serde_json::from_value(row["source"].clone()).expect("source value"),
        usize::try_from(row["index"].as_u64().expect("position index")).expect("usize index"),
    )
}

#[test]
fn owned_projection_matches_full_python_vectors_and_epoch_relation() {
    let fixture = fixture();
    assert_eq!(text(&fixture, "schema"), FIXTURE_SCHEMA);
    assert_eq!(text(&fixture, "authority"), "NONE");
    assert_source_pins(&fixture);

    for row in fixture["cases"].as_array().expect("projection cases") {
        let name = text(row, "name");
        let accepted: AssetTransferLaneModuleAcceptedV1 =
            serde_json::from_value(row["accepted"].clone()).expect("accepted value");
        let occurrence: EconomicCommandOccurrenceV1 =
            serde_json::from_value(row["occurrence"].clone()).expect("occurrence value");
        let predecessor: GlobalEconomicStateV1 =
            serde_json::from_value(row["predecessor"].clone()).expect("predecessor value");
        let current: GlobalEconomicStateV1 =
            serde_json::from_value(row["current"].clone()).expect("current value");
        let source: GlobalEconomicStateV1 =
            serde_json::from_value(row["source"].clone()).expect("source value");
        let index =
            usize::try_from(row["index"].as_u64().expect("position index")).expect("usize index");
        let expected_code = row["expected_code"].as_str().map(str::to_owned);

        let relation = check_asset_transfer_epoch_allocation_v1(
            AssetTransferGlobalAllocationCandidateV1 {
                accepted: &accepted,
                occurrence: &occurrence,
                predecessor: &predecessor,
                current: &current,
            },
            AssetTransferEpochPositionV1 {
                epoch_source: &source,
                occurrence_index: index,
            },
        )
        .expect("epoch relation boundary");
        assert_eq!(
            relation.map(|code| format!("{code:?}")),
            expected_code,
            "{name}"
        );

        let projection = project_asset_transfer_epoch_position_v1(
            AssetTransferEpochPositionV1 {
                epoch_source: &source,
                occurrence_index: index,
            },
            &predecessor,
            &occurrence,
            &accepted,
        )
        .expect("valid projection");

        assert_eq!(projection.position().epoch_source(), &source, "{name}");
        assert_eq!(projection.position().occurrence_index(), index, "{name}");
        assert_eq!(projection.predecessor(), &predecessor, "{name}");
        assert_eq!(projection.occurrence(), &occurrence, "{name}");
        assert_eq!(projection.accepted(), &accepted, "{name}");
        assert!(!std::ptr::eq(projection.position().epoch_source(), &source));
        assert!(!std::ptr::eq(projection.predecessor(), &predecessor));
        assert!(!std::ptr::eq(projection.occurrence(), &occurrence));
        assert!(!std::ptr::eq(projection.accepted(), &accepted));
        assert_eq!(projection.post_state(), &current, "{name}");

        let current_bytes = canonical_bytes_v1(projection.post_state()).expect("current bytes");
        assert_eq!(
            current_bytes,
            expected_bytes(text(row, "canonical_current_hex")),
            "{name}"
        );
        assert_eq!(
            projection
                .post_state()
                .state_root()
                .expect("current root")
                .as_str(),
            text(row, "current_root"),
            "{name}"
        );

        let projected_relation = check_asset_transfer_epoch_allocation_v1(
            AssetTransferGlobalAllocationCandidateV1 {
                accepted: projection.accepted(),
                occurrence: projection.occurrence(),
                predecessor: projection.predecessor(),
                current: projection.post_state(),
            },
            AssetTransferEpochPositionV1 {
                epoch_source: projection.position().epoch_source(),
                occurrence_index: projection.position().occurrence_index(),
            },
        )
        .expect("projected epoch relation boundary");
        assert_eq!(
            projected_relation.map(|code| format!("{code:?}")),
            expected_code,
            "{name} projected relation"
        );
    }
}

#[test]
fn constructor_rejects_position_bound_and_malformed_private_projection() {
    let fixture = fixture();
    let (accepted, occurrence, predecessor, source, _) =
        typed_case(row_named(&fixture, "height_7_position_0"));

    let position_bound = project_asset_transfer_epoch_position_v1(
        AssetTransferEpochPositionV1 {
            epoch_source: &source,
            occurrence_index: MAX_EPOCH_COMMANDS_V1,
        },
        &predecessor,
        &occurrence,
        &accepted,
    );
    assert_eq!(
        position_bound,
        Err(AbiErrorV1::InvalidBinding(
            "asset transfer epoch projection position index",
        ))
    );

    let mut malformed_accepted = accepted;
    malformed_accepted.private_port.post_state.balances.clear();
    assert!(project_asset_transfer_epoch_position_v1(
        AssetTransferEpochPositionV1 {
            epoch_source: &source,
            occurrence_index: 0,
        },
        &predecessor,
        &occurrence,
        &malformed_accepted,
    )
    .is_err());
}

#[test]
fn constructor_rejects_duplicate_replay_identity_and_full_replay_table() {
    let fixture = fixture();
    let (accepted, occurrence, predecessor, source, _) =
        typed_case(row_named(&fixture, "height_7_position_0"));
    let replay = ReplayStateV1 {
        replay_id: occurrence
            .replay_id()
            .expect("replay id")
            .as_str()
            .to_owned(),
        occurrence_id: occurrence.occurrence_id().expect("occurrence id"),
    };

    let mut duplicate_predecessor = predecessor.clone();
    duplicate_predecessor.replay_state.push(replay);
    duplicate_predecessor
        .replay_state
        .sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
    duplicate_predecessor
        .validate()
        .expect("valid replay predecessor");
    assert!(matches!(
        project_asset_transfer_epoch_position_v1(
            AssetTransferEpochPositionV1 {
                epoch_source: &source,
                occurrence_index: 0,
            },
            &duplicate_predecessor,
            &occurrence,
            &accepted,
        ),
        Err(AbiErrorV1::InvalidOrder(_))
    ));

    let mut occurrence_collision = predecessor.clone();
    occurrence_collision.replay_state.push(ReplayStateV1 {
        replay_id: "distinct-replay-id".to_owned(),
        occurrence_id: occurrence.occurrence_id().expect("occurrence id"),
    });
    occurrence_collision
        .replay_state
        .sort_by(|left, right| left.replay_id.cmp(&right.replay_id));
    occurrence_collision
        .validate()
        .expect("valid occurrence predecessor");
    assert_eq!(
        project_asset_transfer_epoch_position_v1(
            AssetTransferEpochPositionV1 {
                epoch_source: &source,
                occurrence_index: 0
            },
            &occurrence_collision,
            &occurrence,
            &accepted,
        ),
        Err(AbiErrorV1::InvalidOrder("global replay occurrence ids"))
    );

    let mut full_predecessor = predecessor;
    full_predecessor.replay_state = (0..MAX_GLOBAL_REPLAY_ROWS_V1)
        .map(|index| ReplayStateV1 {
            replay_id: format!("replay-{index:04}"),
            occurrence_id: RootV1::parse(
                format!("0x{:064x}", index + 1),
                "projection replay fixture root",
                false,
            )
            .expect("replay fixture root"),
        })
        .collect();
    full_predecessor
        .validate()
        .expect("valid full replay predecessor");
    let mut almost_full = full_predecessor.clone();
    almost_full.replay_state.pop();
    almost_full.validate().expect("valid capacity neighbour");
    let capacity_boundary = project_asset_transfer_epoch_position_v1(
        AssetTransferEpochPositionV1 {
            epoch_source: &source,
            occurrence_index: 0,
        },
        &almost_full,
        &occurrence,
        &accepted,
    )
    .expect("one remaining replay row is constructible");
    assert_eq!(
        capacity_boundary.post_state().replay_state.len(),
        MAX_GLOBAL_REPLAY_ROWS_V1
    );
    assert_eq!(
        almost_full.replay_state.len(),
        MAX_GLOBAL_REPLAY_ROWS_V1 - 1
    );
    // These structurally valid frames intentionally retain the original
    // command root. Capacity checks alone confer no allocation admission.
    assert!(matches!(
        project_asset_transfer_epoch_position_v1(
            AssetTransferEpochPositionV1 {
                epoch_source: &source,
                occurrence_index: 0,
            },
            &full_predecessor,
            &occurrence,
            &accepted,
        ),
        Err(AbiErrorV1::InvalidBounds("global state replay state"))
    ));
}
