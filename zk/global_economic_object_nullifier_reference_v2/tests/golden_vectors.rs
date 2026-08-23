use serde::Deserialize;
use serde_json::{Map, Value};
use std::collections::BTreeSet;
use zenodex_global_economic_object_nullifier_reference_v2::{
    apply_reference_object_nullifiers_v2, canonical_reference_archive_bytes_v2,
    reference_archive_digest_v2, CanonicalReferenceNullifierArchiveV2, ReferenceConsumptionClaimV2,
    ReferenceNullifierEntryV2, ReferenceObjectIdV2, ReferenceOccurrenceIdV2, ReferenceRejectCodeV2,
    ReferenceResultV2, MAX_REFERENCE_CLAIMS_PER_STEP_V2, MAX_REFERENCE_NULLIFIERS_V2,
    REFERENCE_SCHEMA_V2,
};

const GOLDEN: &str =
    include_str!("../../../tests/data/global_economic_object_nullifier_reference_v2_golden.json");

fn id(number: usize) -> String {
    format!("0x{number:064x}")
}

fn object_id(number: usize) -> ReferenceObjectIdV2 {
    ReferenceObjectIdV2::new(&id(number)).expect("test object id is valid")
}

fn occurrence_id(number: usize) -> ReferenceOccurrenceIdV2 {
    ReferenceOccurrenceIdV2::new(&id(number)).expect("test occurrence id is valid")
}

fn claim(object: usize, occurrence: usize) -> ReferenceConsumptionClaimV2 {
    ReferenceConsumptionClaimV2::new(object_id(object), occurrence_id(occurrence))
}

fn entry(object: usize, occurrence: usize) -> ReferenceNullifierEntryV2 {
    ReferenceNullifierEntryV2::new(object_id(object), occurrence_id(occurrence))
}

fn archive(size: usize) -> CanonicalReferenceNullifierArchiveV2 {
    CanonicalReferenceNullifierArchiveV2::new(
        (1..=size)
            .map(|index| entry(index, 10_000 + index))
            .collect(),
    )
    .expect("test archive is canonical")
}

fn exact_keys(value: &Map<String, Value>, expected: &[&str]) {
    let actual: Vec<&str> = value.keys().map(String::as_str).collect();
    let mut expected_sorted = expected.to_vec();
    expected_sorted.sort_unstable();
    assert_eq!(actual, expected_sorted);
}

fn as_object(value: &Value) -> &Map<String, Value> {
    value.as_object().expect("fixture row must be an object")
}

fn as_array(value: &Value) -> &[Value] {
    value.as_array().expect("fixture field must be an array")
}

fn as_string(value: &Value) -> &str {
    value.as_str().expect("fixture field must be a string")
}

fn fixture_entry(value: &Value) -> ReferenceNullifierEntryV2 {
    let row = as_object(value);
    exact_keys(row, &["first_consumed_by_occurrence_id", "object_id"]);
    ReferenceNullifierEntryV2::new(
        ReferenceObjectIdV2::new(as_string(&row["object_id"])).expect("fixture object id is valid"),
        ReferenceOccurrenceIdV2::new(as_string(&row["first_consumed_by_occurrence_id"]))
            .expect("fixture occurrence id is valid"),
    )
}

fn fixture_claim(value: &Value) -> ReferenceConsumptionClaimV2 {
    let row = as_object(value);
    exact_keys(row, &["consumed_by_occurrence_id", "object_id"]);
    ReferenceConsumptionClaimV2::new(
        ReferenceObjectIdV2::new(as_string(&row["object_id"])).expect("fixture object id is valid"),
        ReferenceOccurrenceIdV2::new(as_string(&row["consumed_by_occurrence_id"]))
            .expect("fixture occurrence id is valid"),
    )
}

#[allow(dead_code)]
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ClosedGoldenFixture {
    digest_prefix_hex: String,
    limits: ClosedLimits,
    reference_schema: String,
    schema: String,
    vectors: Vec<ClosedVector>,
}

#[allow(dead_code)]
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ClosedLimits {
    max_archive_bytes: usize,
    max_claims_per_step: usize,
    max_nullifiers: usize,
}

#[allow(dead_code)]
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ClosedVector {
    claims: Vec<ClosedClaim>,
    expected: ClosedExpected,
    name: String,
    pre_canonical_json: String,
    pre_entries: Vec<ClosedEntry>,
    pre_reference_archive_digest: String,
}

#[allow(dead_code)]
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ClosedClaim {
    consumed_by_occurrence_id: String,
    object_id: String,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct ClosedEntry {
    first_consumed_by_occurrence_id: String,
    object_id: String,
}

#[allow(dead_code)]
#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum ClosedExpected {
    Accepted(ClosedAccepted),
    Rejected(ClosedRejected),
}

#[allow(dead_code)]
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ClosedAccepted {
    kind: String,
    post_canonical_json: String,
    post_entries: Vec<ClosedEntry>,
    post_reference_archive_digest: String,
}

#[allow(dead_code)]
#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ClosedRejected {
    code: String,
    kind: String,
}

#[test]
fn golden_vectors_match_reference_bytes_digests_and_outcomes() {
    let closed: ClosedGoldenFixture =
        serde_json::from_str(GOLDEN).expect("golden JSON has a closed schema");
    assert_eq!(
        closed.digest_prefix_hex,
        "676c6f62616c2d65636f6e6f6d69632d6f626a6563742d6e756c6c69666965722d7265666572656e6365003200"
    );
    assert_eq!(
        closed.schema,
        "zenodex/global-economic-object-nullifier-reference-golden/v1"
    );
    assert_eq!(closed.reference_schema, REFERENCE_SCHEMA_V2);
    assert_eq!(
        (
            closed.limits.max_archive_bytes,
            closed.limits.max_claims_per_step,
            closed.limits.max_nullifiers,
        ),
        (1_048_576, 64, 4_096)
    );
    assert_eq!(
        closed
            .vectors
            .iter()
            .map(|vector| vector.name.as_str())
            .collect::<Vec<_>>(),
        vec![
            "empty_identity",
            "insert_one",
            "insert_two_reverse",
            "duplicate_in_batch",
            "already_consumed",
        ]
    );

    let fixture: Value = serde_json::from_str(GOLDEN).expect("golden JSON is valid");
    let root = as_object(&fixture);
    exact_keys(
        root,
        &[
            "digest_prefix_hex",
            "limits",
            "reference_schema",
            "schema",
            "vectors",
        ],
    );

    for vector_value in as_array(&root["vectors"]) {
        let vector = as_object(vector_value);
        exact_keys(
            vector,
            &[
                "claims",
                "expected",
                "name",
                "pre_canonical_json",
                "pre_entries",
                "pre_reference_archive_digest",
            ],
        );
        let pre = CanonicalReferenceNullifierArchiveV2::new(
            as_array(&vector["pre_entries"])
                .iter()
                .map(fixture_entry)
                .collect(),
        )
        .expect("fixture pre-archive is canonical");
        assert_eq!(
            canonical_reference_archive_bytes_v2(&pre),
            as_string(&vector["pre_canonical_json"]).as_bytes()
        );
        assert_eq!(
            reference_archive_digest_v2(&pre),
            as_string(&vector["pre_reference_archive_digest"])
        );

        let claims: Vec<_> = as_array(&vector["claims"])
            .iter()
            .map(fixture_claim)
            .collect();
        let expected = as_object(&vector["expected"]);
        match apply_reference_object_nullifiers_v2(&pre, &claims) {
            ReferenceResultV2::Accepted(accepted) => {
                exact_keys(
                    expected,
                    &[
                        "kind",
                        "post_canonical_json",
                        "post_entries",
                        "post_reference_archive_digest",
                    ],
                );
                assert_eq!(as_string(&expected["kind"]), "accepted");
                assert_eq!(
                    canonical_reference_archive_bytes_v2(accepted.post_archive()),
                    as_string(&expected["post_canonical_json"]).as_bytes()
                );
                assert_eq!(
                    accepted.post_reference_archive_digest(),
                    as_string(&expected["post_reference_archive_digest"])
                );
                let actual_entries = accepted
                    .post_archive()
                    .entries()
                    .iter()
                    .map(|entry| {
                        serde_json::json!({
                            "first_consumed_by_occurrence_id": entry
                                .first_consumed_by_occurrence_id
                                .as_str(),
                            "object_id": entry.object_id.as_str(),
                        })
                    })
                    .collect::<Vec<_>>();
                assert_eq!(Value::Array(actual_entries), expected["post_entries"]);
            }
            ReferenceResultV2::Rejected(rejected) => {
                exact_keys(expected, &["code", "kind"]);
                assert_eq!(as_string(&expected["kind"]), "rejected");
                assert_eq!(rejected.code().as_str(), as_string(&expected["code"]));
            }
        }
    }
}

#[test]
fn boundaries_match_reference() {
    for count in [0, 1, 63, 64, 65] {
        let claims: Vec<_> = (1..=count)
            .map(|index| claim(index, 1_000 + index))
            .collect();
        let result = apply_reference_object_nullifiers_v2(
            &CanonicalReferenceNullifierArchiveV2::empty(),
            &claims,
        );
        if count <= MAX_REFERENCE_CLAIMS_PER_STEP_V2 {
            assert!(matches!(result, ReferenceResultV2::Accepted(_)));
        } else {
            assert!(matches!(
                result,
                ReferenceResultV2::Rejected(ref rejected)
                    if rejected.code() == ReferenceRejectCodeV2::ReferenceStepLimitExceeded
            ));
        }
    }

    let at_4095 = archive(MAX_REFERENCE_NULLIFIERS_V2 - 1);
    assert!(matches!(
        apply_reference_object_nullifiers_v2(
            &at_4095,
            &[claim(MAX_REFERENCE_NULLIFIERS_V2, 90_000)]
        ),
        ReferenceResultV2::Accepted(_)
    ));
    let at_4096 = archive(MAX_REFERENCE_NULLIFIERS_V2);
    assert!(matches!(
        apply_reference_object_nullifiers_v2(
            &at_4096,
            &[claim(MAX_REFERENCE_NULLIFIERS_V2 + 1, 90_001)]
        ),
        ReferenceResultV2::Rejected(ref rejected)
            if rejected.code() == ReferenceRejectCodeV2::ReferenceArchiveCapacityExceeded
    ));
}

#[test]
fn reject_precedence_and_noop_match_reference() {
    let full = archive(MAX_REFERENCE_NULLIFIERS_V2);
    let full_digest = reference_archive_digest_v2(&full);
    let too_many = vec![claim(1, 77_777); 65];
    assert_rejection(
        apply_reference_object_nullifiers_v2(&full, &too_many),
        ReferenceRejectCodeV2::ReferenceStepLimitExceeded,
        &full_digest,
        "reference step claim count exceeds 64",
    );

    let duplicate = [claim(1, 101), claim(1, 102)];
    assert_rejection(
        apply_reference_object_nullifiers_v2(&full, &duplicate),
        ReferenceRejectCodeV2::ReferenceDuplicateInBatch,
        &full_digest,
        "reference step repeats an object identifier",
    );
    assert_rejection(
        apply_reference_object_nullifiers_v2(&full, &[claim(1, 103)]),
        ReferenceRejectCodeV2::ReferenceAlreadyConsumed,
        &full_digest,
        "reference step includes a previously consumed object",
    );
    assert_rejection(
        apply_reference_object_nullifiers_v2(
            &full,
            &[claim(MAX_REFERENCE_NULLIFIERS_V2 + 1, 99_999)],
        ),
        ReferenceRejectCodeV2::ReferenceArchiveCapacityExceeded,
        &full_digest,
        "reference archive successor exceeds 4096 entries",
    );
    assert_eq!(reference_archive_digest_v2(&full), full_digest);
}

fn assert_rejection(
    result: ReferenceResultV2,
    expected_code: ReferenceRejectCodeV2,
    expected_pre_digest: &str,
    expected_diagnostic: &str,
) {
    let ReferenceResultV2::Rejected(rejected) = result else {
        panic!("expected reference rejection");
    };
    assert_eq!(rejected.code(), expected_code);
    assert_eq!(rejected.pre_reference_archive_digest(), expected_pre_digest);
    assert_eq!(rejected.diagnostic(), expected_diagnostic);
}

#[test]
fn permutations_and_three_step_history_match_reference() {
    let permutations = [
        [claim(1, 101), claim(2, 102), claim(3, 103)],
        [claim(1, 101), claim(3, 103), claim(2, 102)],
        [claim(2, 102), claim(1, 101), claim(3, 103)],
        [claim(2, 102), claim(3, 103), claim(1, 101)],
        [claim(3, 103), claim(1, 101), claim(2, 102)],
        [claim(3, 103), claim(2, 102), claim(1, 101)],
    ];
    let mut digests = BTreeSet::new();
    for claims in permutations {
        let ReferenceResultV2::Accepted(accepted) = apply_reference_object_nullifiers_v2(
            &CanonicalReferenceNullifierArchiveV2::empty(),
            &claims,
        ) else {
            panic!("fresh permutation must accept");
        };
        digests.insert(accepted.post_reference_archive_digest());
    }
    assert_eq!(digests.len(), 1);

    let ReferenceResultV2::Accepted(step_one) = apply_reference_object_nullifiers_v2(
        &CanonicalReferenceNullifierArchiveV2::empty(),
        &[claim(2, 102)],
    ) else {
        panic!("step one must accept");
    };
    let ReferenceResultV2::Accepted(step_two) = apply_reference_object_nullifiers_v2(
        step_one.post_archive(),
        &[claim(1, 101), claim(3, 103)],
    ) else {
        panic!("step two must accept");
    };
    assert!(matches!(
        apply_reference_object_nullifiers_v2(step_two.post_archive(), &[claim(2, 202)]),
        ReferenceResultV2::Rejected(ref rejected)
            if rejected.code() == ReferenceRejectCodeV2::ReferenceAlreadyConsumed
    ));
}

#[test]
fn closed_fixture_decode_rejects_unknown_duplicate_and_noncanonical_fields() {
    let unknown = GOLDEN.replacen('{', "{\"unknown\":0,", 1);
    assert!(serde_json::from_str::<ClosedGoldenFixture>(&unknown).is_err());
    let duplicate = GOLDEN.replacen(
        "\"schema\": \"zenodex/global-economic-object-nullifier-reference-golden/v1\"",
        "\"schema\": \"zenodex/global-economic-object-nullifier-reference-golden/v1\",\n  \"schema\": \"duplicate\"",
        1,
    );
    assert!(serde_json::from_str::<ClosedGoldenFixture>(&duplicate).is_err());
    assert!(ReferenceObjectIdV2::new(&format!("0x{}", "A".repeat(64))).is_err());
    assert!(ReferenceObjectIdV2::new(&format!("0x{}", "0".repeat(64))).is_err());
}
