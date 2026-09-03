//! Rust side of the shared GlobalAccountingAllocationCertificateV1 parity vector.
//!
//! Every recorded state and certificate is decoded from canonical JSON, re-encoded
//! and hashed (binding it to the Python renderer), and checked through the Rust
//! implementation. The exact outcome (status, code, detail, message) and every
//! derived root must equal the fixture rendered by
//! `tools/render_global_accounting_allocation_certificate_v1_golden.py`.
//! Authority: NONE.

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use serde::Deserialize;
use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, check_global_accounting_allocation_certificate_v1,
    derive_allocation_root_v1, derive_canonical_allocation_rows_v1, derive_field_ownership_root_v1,
    derive_terminal_binding_root_v1, hash_bytes_sha256_v1, AllocationCertificateOutcomeV1,
    AllocationCertificateRejectCodeV1, GlobalAccountingAllocationCertificateV1,
    GlobalEconomicStateV1, LaneProducerKindV1, ALL_LANE_IDS_V1, EMPTY_LANE_WITNESS_SLOTS_V1,
    LANE_ALLOCATION_PRODUCER_REGISTRY_V1,
};

const FIXTURE_SCHEMA: &str = "zenodex/global-accounting-allocation-certificate-v1-golden/v2";

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    fixture_schema: String,
    authority: String,
    certificate_schema: String,
    reject_messages: BTreeMap<String, String>,
    check_order: Vec<String>,
    fold_overflow_labels: Vec<String>,
    producer_registry: BTreeMap<String, RegistryEntry>,
    vectors: BTreeMap<String, Vector>,
    mutation_killers: BTreeMap<String, MutationKiller>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct RegistryEntry {
    producer_kind: String,
    blocked_on: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct MutationKiller {
    vector: String,
    expected_code: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Derived {
    lane_fragment_roots: Vec<String>,
    field_ownership_root: String,
    terminal_binding_root: String,
    allocation_root: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Outcome {
    status: String,
    #[serde(default)]
    code: Option<String>,
    #[serde(default)]
    detail: Option<String>,
    #[serde(default)]
    message: Option<String>,
    #[serde(default)]
    lane_fragment_roots: Option<Vec<String>>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Vector {
    obligation: String,
    spec: Value,
    certificate_mutation: String,
    state: Value,
    state_bytes_sha256: String,
    expected_state_root: String,
    certificate: Value,
    certificate_bytes_sha256: String,
    derived: Derived,
    expected_outcome: Outcome,
}

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_accounting_allocation_certificate_v1_golden.json")
}

fn load_fixture() -> Fixture {
    let bytes = fs::read(fixture_path()).expect("certificate fixture must be readable");
    let fixture: Fixture =
        serde_json::from_slice(&bytes).expect("certificate fixture must be typed JSON");
    assert_eq!(fixture.fixture_schema, FIXTURE_SCHEMA);
    assert_eq!(fixture.authority, "NONE");
    assert_eq!(
        fixture.certificate_schema,
        zenodex_global_settlement_abi_v1::GLOBAL_ACCOUNTING_ALLOCATION_CERTIFICATE_SCHEMA_V1
    );
    fixture
}

#[test]
fn reject_message_table_check_order_and_registry_are_shared() {
    let fixture = load_fixture();
    let expected: BTreeMap<String, String> = AllocationCertificateRejectCodeV1::ALL
        .into_iter()
        .map(|code| (code.code().to_owned(), code.message().to_owned()))
        .collect();
    assert_eq!(fixture.reject_messages, expected);
    assert_eq!(fixture.check_order.len(), 13);
    assert_eq!(
        fixture.fold_overflow_labels,
        [
            "{lane} controlled",
            "{lane} assignments",
            "reserves",
            "terminal totals",
            "custody"
        ],
        "the shared fold-overflow labels are pinned; the src unit tests exercise each fold against them"
    );
    let lanes: Vec<String> = ALL_LANE_IDS_V1
        .iter()
        .map(|lane| format!("{lane:?}"))
        .collect();
    let registry_lanes: Vec<String> = fixture.producer_registry.keys().cloned().collect();
    let mut sorted_lanes = lanes.clone();
    sorted_lanes.sort();
    assert_eq!(registry_lanes, sorted_lanes);
    for (lane, kind, blocked_on) in LANE_ALLOCATION_PRODUCER_REGISTRY_V1 {
        let entry = &fixture.producer_registry[&format!("{lane:?}")];
        assert_eq!(entry.producer_kind, format!("{kind:?}"));
        assert_eq!(entry.blocked_on, blocked_on);
        assert_ne!(kind, LaneProducerKindV1::RECEIPT_BACKED);
    }
}

#[test]
fn every_vector_replays_outcome_and_derived_roots() {
    let fixture = load_fixture();
    assert_eq!(
        fixture.vectors.len(),
        28,
        "fixture must carry the 28 named vectors"
    );
    for (name, vector) in &fixture.vectors {
        assert!(
            !vector.obligation.is_empty() && vector.spec.is_object(),
            "{name}"
        );
        assert!(!vector.certificate_mutation.is_empty(), "{name}");
        let state: GlobalEconomicStateV1 = serde_json::from_value(vector.state.clone())
            .unwrap_or_else(|error| panic!("{name}: state must decode: {error}"));
        let state_bytes = canonical_bytes_v1(&state).expect("state encodes");
        assert_eq!(
            hash_bytes_sha256_v1(&state_bytes),
            vector.state_bytes_sha256,
            "{name}"
        );
        assert_eq!(
            state.state_root().expect("state root").as_str(),
            vector.expected_state_root,
            "{name}"
        );
        let certificate: GlobalAccountingAllocationCertificateV1 =
            serde_json::from_value(vector.certificate.clone())
                .unwrap_or_else(|error| panic!("{name}: certificate must decode: {error}"));
        let certificate_bytes = canonical_bytes_v1(&certificate).expect("certificate encodes");
        assert_eq!(
            hash_bytes_sha256_v1(&certificate_bytes),
            vector.certificate_bytes_sha256,
            "{name}"
        );
        let round_trip: Value = serde_json::from_slice(&certificate_bytes).expect("JSON");
        assert_eq!(round_trip, vector.certificate, "{name}");
        let fragments = &certificate.ordered_lane_fragments;
        let roots: Vec<String> = fragments
            .iter()
            .map(|f| {
                f.fragment_root()
                    .expect("fragment root")
                    .as_str()
                    .to_owned()
            })
            .collect();
        assert_eq!(roots, vector.derived.lane_fragment_roots, "{name}");
        assert_eq!(
            derive_field_ownership_root_v1(fragments)
                .expect("ownership root")
                .as_str(),
            vector.derived.field_ownership_root,
            "{name}"
        );
        assert_eq!(
            derive_terminal_binding_root_v1(fragments)
                .expect("terminal root")
                .as_str(),
            vector.derived.terminal_binding_root,
            "{name}"
        );
        let rows = derive_canonical_allocation_rows_v1(fragments).expect("rows fold");
        assert_eq!(
            derive_allocation_root_v1(fragments, &rows)
                .expect("allocation root")
                .as_str(),
            vector.derived.allocation_root,
            "{name}"
        );
        let outcome = check_global_accounting_allocation_certificate_v1(
            &certificate,
            &state,
            &EMPTY_LANE_WITNESS_SLOTS_V1,
        )
        .unwrap_or_else(|error| panic!("{name}: checker must not fail to parse: {error}"));
        match (vector.expected_outcome.status.as_str(), outcome) {
            ("ACCEPT", AllocationCertificateOutcomeV1::Accepted(accepted)) => {
                let roots: Vec<String> = accepted
                    .lane_fragment_roots
                    .iter()
                    .map(|r| r.as_str().to_owned())
                    .collect();
                assert_eq!(
                    Some(roots),
                    vector.expected_outcome.lane_fragment_roots,
                    "{name}"
                );
                assert_eq!(
                    accepted.allocation_root.as_str(),
                    vector.derived.allocation_root,
                    "{name}"
                );
                assert_eq!(accepted.authority, "NONE");
            }
            ("REJECT", AllocationCertificateOutcomeV1::Rejected(rejected)) => {
                assert_eq!(
                    vector.expected_outcome.code.as_deref(),
                    Some(rejected.code.code()),
                    "{name}"
                );
                assert_eq!(
                    vector.expected_outcome.detail.as_deref(),
                    Some(rejected.detail.as_str()),
                    "{name}"
                );
                assert_eq!(
                    vector.expected_outcome.message.as_deref(),
                    Some(rejected.code.message()),
                    "{name}"
                );
                assert_eq!(rejected.pre_state_root, rejected.post_state_root, "{name}");
                assert_eq!(
                    rejected.pre_state_root.as_str(),
                    vector.expected_state_root,
                    "{name}"
                );
            }
            (status, outcome) => panic!("{name}: outcome {status} does not match {outcome:?}"),
        }
    }
}

#[test]
fn mutation_killers_name_recorded_vectors_with_the_expected_polarity() {
    let fixture = load_fixture();
    for (mutation, killer) in &fixture.mutation_killers {
        let vector = fixture
            .vectors
            .get(&killer.vector)
            .unwrap_or_else(|| panic!("{mutation}: {}", killer.vector));
        if killer.expected_code == "ACCEPT" {
            assert_eq!(vector.expected_outcome.status, "ACCEPT", "{mutation}");
        } else {
            assert_eq!(vector.expected_outcome.status, "REJECT", "{mutation}");
            assert_eq!(
                vector.expected_outcome.code.as_deref(),
                Some(killer.expected_code.as_str()),
                "{mutation}"
            );
        }
    }
}
