use serde_json::{json, Value};
use zenodex_global_economic_delta_v2::{
    decode_delta_plan_v2, decode_source_history_statement_v2, SourceHistoryRejectCodeV2,
    MAX_SOURCE_HISTORY_INPUT_BYTES_V2, SOURCE_HISTORY_SCHEMA_V2,
};

const PLAN_VECTOR: &str = include_str!("../../../tests/data/global_economic_delta_v2_plan.json");
const HISTORY_VECTOR: &str =
    include_str!("../../../tests/data/global_economic_source_history_v2_statement.json");

fn plan() -> zenodex_global_economic_delta_v2::StructurallyValidDeltaPlanV2 {
    decode_delta_plan_v2(PLAN_VECTOR.as_bytes()).unwrap()
}

fn statement() -> Value {
    serde_json::from_str(HISTORY_VECTOR).unwrap()
}

fn encoded(value: &Value) -> Vec<u8> {
    serde_json::to_vec(value).unwrap()
}

#[test]
fn checked_history_statement_binds_exact_plan_and_canonical_bytes() {
    // Arrange
    let delta_plan = plan();

    // Act
    let checked =
        decode_source_history_statement_v2(&delta_plan, HISTORY_VECTOR.as_bytes()).unwrap();

    // Assert
    assert_eq!(checked.source_claim_count(), 3);
    assert_eq!(checked.delta_plan_root(), delta_plan.root());
    assert_eq!(checked.history_height(), 30);
    assert_eq!(checked.writer_epoch(), 1);
    assert_eq!(checked.chain_id(), "zenodex:research");
    assert_eq!(
        checked.profile_root(),
        "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
    );
    assert_eq!(checked.canonical_bytes(), HISTORY_VECTOR.as_bytes());
    assert_eq!(
        checked.root(),
        "sha256:27218cf30e6dc87974e8190cf77510969472a3015b42b6fb9a59e16af55d3744"
    );
}

#[test]
fn source_kind_asset_amount_and_root_must_equal_the_plan_binding() {
    // Arrange
    let cases = [
        ("source_kind", json!("ancestor_claim")),
        ("asset", json!("zusd")),
        ("amount_atoms", json!(6)),
        (
            "source_root",
            json!("sha256:1212121212121212121212121212121212121212121212121212121212121212"),
        ),
    ];

    // Act / Assert -- kills omission of any source-binding equality.
    for (field, replacement) in cases {
        let mut candidate = statement();
        candidate["source_availability_claims"][0][field] = replacement;
        let rejected =
            decode_source_history_statement_v2(&plan(), &encoded(&candidate)).unwrap_err();
        assert_eq!(
            rejected.code,
            SourceHistoryRejectCodeV2::SourceBindingMismatch
        );
    }
}

#[test]
fn source_claims_are_exact_count_unique_and_canonically_ordered() {
    // Arrange
    let mut missing = statement();
    missing["source_availability_claims"]
        .as_array_mut()
        .unwrap()
        .pop();
    let mut duplicate = statement();
    duplicate["source_availability_claims"][1] = duplicate["source_availability_claims"][0].clone();
    let mut reordered = statement();
    reordered["source_availability_claims"]
        .as_array_mut()
        .unwrap()
        .swap(0, 1);

    // Act / Assert
    let cases = [
        (missing, SourceHistoryRejectCodeV2::SourceCountMismatch),
        (duplicate, SourceHistoryRejectCodeV2::DuplicateSourceClaim),
        (
            reordered,
            SourceHistoryRejectCodeV2::NoncanonicalSourceOrder,
        ),
    ];
    for (candidate, expected) in cases {
        let rejected =
            decode_source_history_statement_v2(&plan(), &encoded(&candidate)).unwrap_err();
        assert_eq!(rejected.code, expected);
    }
}

#[test]
fn finality_order_and_occurrence_coordinates_are_closed() {
    // Arrange
    let mut source_after_finality = statement();
    source_after_finality["source_availability_claims"][0]["source_height"] = json!(21);
    let mut finality_after_history = statement();
    finality_after_history["source_availability_claims"][0]["finalized_height"] = json!(31);
    let mut duplicate_coordinate = statement();
    for field in ["source_height", "tx_index", "op_index"] {
        duplicate_coordinate["source_availability_claims"][1][field] =
            duplicate_coordinate["source_availability_claims"][0][field].clone();
    }
    let mut exact_u64_edge = statement();
    exact_u64_edge["history_height"] = json!(u64::MAX);
    exact_u64_edge["source_availability_claims"][0]["source_height"] = json!(u64::MAX);
    exact_u64_edge["source_availability_claims"][0]["finalized_height"] = json!(u64::MAX);

    // Act / Assert
    for candidate in [source_after_finality, finality_after_history] {
        let rejected =
            decode_source_history_statement_v2(&plan(), &encoded(&candidate)).unwrap_err();
        assert_eq!(
            rejected.code,
            SourceHistoryRejectCodeV2::FinalityOrderInvalid
        );
    }
    assert!(decode_source_history_statement_v2(&plan(), &encoded(&exact_u64_edge)).is_ok());
    let rejected =
        decode_source_history_statement_v2(&plan(), &encoded(&duplicate_coordinate)).unwrap_err();
    assert_eq!(
        rejected.code,
        SourceHistoryRejectCodeV2::DuplicateOccurrence
    );
}

#[test]
fn writer_epoch_bva_accepts_one_and_rejects_zero() {
    // Arrange
    let accepted = statement();
    let mut rejected = statement();
    rejected["writer_epoch"] = json!(0);
    let mut maximum = statement();
    maximum["writer_epoch"] = json!(u64::MAX);

    // Act / Assert
    assert_eq!(
        decode_source_history_statement_v2(&plan(), &encoded(&accepted))
            .unwrap()
            .writer_epoch(),
        1
    );
    assert_eq!(
        decode_source_history_statement_v2(&plan(), &encoded(&maximum))
            .unwrap()
            .writer_epoch(),
        u64::MAX
    );
    assert_eq!(
        decode_source_history_statement_v2(&plan(), &encoded(&rejected))
            .unwrap_err()
            .code,
        SourceHistoryRejectCodeV2::WriterEpochInvalid
    );
}

#[test]
fn duplicate_consumption_nullifier_rejects() {
    // Arrange
    let mut duplicate_nullifier = statement();
    duplicate_nullifier["source_availability_claims"][1]["consumption_nullifier"] =
        duplicate_nullifier["source_availability_claims"][0]["consumption_nullifier"].clone();
    // Act
    let rejected =
        decode_source_history_statement_v2(&plan(), &encoded(&duplicate_nullifier)).unwrap_err();

    // Assert
    assert_eq!(
        rejected.code,
        SourceHistoryRejectCodeV2::DuplicateConsumptionNullifier
    );
}

#[test]
fn source_finality_and_nullifier_root_roles_cannot_alias() {
    // Arrange
    let cases = [
        ("finality_anchor_root", "source_root"),
        ("consumption_nullifier", "source_root"),
        ("consumption_nullifier", "finality_anchor_root"),
    ];

    // Act / Assert -- kills a mutant that treats all roots as interchangeable.
    for (target, source) in cases {
        let mut candidate = statement();
        candidate["source_availability_claims"][0][target] =
            candidate["source_availability_claims"][0][source].clone();
        assert_eq!(
            decode_source_history_statement_v2(&plan(), &encoded(&candidate))
                .unwrap_err()
                .code,
            SourceHistoryRejectCodeV2::RootRoleConflict
        );
    }
}

#[test]
fn caller_supplied_unconsumed_flag_and_unknown_fields_reject() {
    // Arrange -- history-proof semantics own nullifier absence.
    let mut candidate = statement();
    candidate["source_availability_claims"][0]["unconsumed"] = json!(true);

    // Act
    let rejected = decode_source_history_statement_v2(&plan(), &encoded(&candidate)).unwrap_err();

    // Assert
    assert_eq!(rejected.code, SourceHistoryRejectCodeV2::DecodeInvalid);
}

#[test]
fn plan_root_schema_input_bytes_and_u32_coordinates_fail_closed() {
    // Arrange
    let mut wrong_plan = statement();
    wrong_plan["delta_plan_root"] =
        json!("sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");
    let mut wrong_schema = statement();
    wrong_schema["schema"] = json!("zenodex/global-economic-source-history-statement/v3");
    let mut above_u32 = statement();
    above_u32["source_availability_claims"][0]["tx_index"] = json!(u64::from(u32::MAX) + 1);
    let mut exact_u32 = statement();
    exact_u32["source_availability_claims"][0]["tx_index"] = json!(u32::MAX);

    // Act / Assert
    for (candidate, expected) in [
        (wrong_plan, SourceHistoryRejectCodeV2::DeltaPlanRootMismatch),
        (wrong_schema, SourceHistoryRejectCodeV2::SchemaMismatch),
        (above_u32, SourceHistoryRejectCodeV2::DecodeInvalid),
    ] {
        assert_eq!(
            decode_source_history_statement_v2(&plan(), &encoded(&candidate))
                .unwrap_err()
                .code,
            expected
        );
    }
    assert_eq!(
        SOURCE_HISTORY_SCHEMA_V2,
        "zenodex/global-economic-source-history-statement/v2"
    );
    assert_eq!(
        decode_source_history_statement_v2(
            &plan(),
            &vec![b' '; MAX_SOURCE_HISTORY_INPUT_BYTES_V2 + 1],
        )
        .unwrap_err()
        .code,
        SourceHistoryRejectCodeV2::InputTooLarge
    );
    assert!(decode_source_history_statement_v2(&plan(), &encoded(&exact_u32)).is_ok());
    let mut exact_bytes = HISTORY_VECTOR.as_bytes().to_vec();
    exact_bytes.resize(MAX_SOURCE_HISTORY_INPUT_BYTES_V2, b' ');
    assert!(decode_source_history_statement_v2(&plan(), &exact_bytes).is_ok());
}

#[test]
fn object_key_insertion_order_does_not_change_canonical_statement() {
    // Arrange
    let original = statement();
    let reversed_fields = original
        .as_object()
        .unwrap()
        .iter()
        .rev()
        .map(|(key, value)| {
            format!(
                "{}:{}",
                serde_json::to_string(key).unwrap(),
                serde_json::to_string(value).unwrap()
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let reordered = format!("{{{reversed_fields}}}").into_bytes();

    // Act
    let ordinary = decode_source_history_statement_v2(&plan(), &encoded(&original)).unwrap();
    let permuted = decode_source_history_statement_v2(&plan(), &reordered).unwrap();

    // Assert
    assert_eq!(permuted.canonical_bytes(), ordinary.canonical_bytes());
    assert_eq!(permuted.root(), ordinary.root());
}
