//! Rust side of the shared claimant-backing guard parity vector.
//!
//! Every recorded V1 state is decoded from its canonical JSON, re-encoded and
//! hashed (binding it to the Python builder), and then folded into the
//! claimant-backing view. The view bytes, the view root, and the exact reject
//! code and message must equal the fixture rendered by
//! `tools/render_global_claimant_backing_guard_v1_golden.py`. Authority: NONE.

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use serde::Deserialize;
use serde_json::Value;
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, classify_claimant_backing_error_v1, derive_claimant_backing_view_v1,
    hash_bytes_sha256_v1, require_claimant_backing_v1, AbiErrorV1, ClaimantBackingRejectCodeV1,
    GlobalEconomicStateV1, CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1,
};

const FIXTURE_SCHEMA: &str = "zenodex/global-claimant-backing-guard-v1-golden/v1";

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Fixture {
    fixture_schema: String,
    authority: String,
    hash_domain: String,
    reject_messages: BTreeMap<String, String>,
    vectors: BTreeMap<String, Vector>,
    histories: BTreeMap<String, Vec<String>>,
    mutation_killers: BTreeMap<String, String>,
    unreachable_mutations: BTreeMap<String, String>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Vector {
    obligation: String,
    spec: Value,
    state: Value,
    state_bytes_sha256: String,
    expected_state_root: String,
    expected_view: Option<Value>,
    expected_view_root: Option<String>,
    expected_outcome: Outcome,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Outcome {
    status: String,
    #[serde(default)]
    code: Option<String>,
    #[serde(default)]
    message: Option<String>,
}

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("tests/data/global_claimant_backing_guard_v1_golden.json")
}

fn load_fixture() -> Fixture {
    let bytes = fs::read(fixture_path()).expect("claimant backing fixture must be readable");
    let fixture: Fixture =
        serde_json::from_slice(&bytes).expect("claimant backing fixture must be typed JSON");
    assert_eq!(fixture.fixture_schema, FIXTURE_SCHEMA);
    assert_eq!(fixture.authority, "NONE");
    assert_eq!(fixture.hash_domain, CLAIMANT_BACKING_VIEW_HASH_DOMAIN_V1);
    fixture
}

fn reject(error: &AbiErrorV1) -> (String, String) {
    let code = classify_claimant_backing_error_v1(error)
        .expect("guard errors must classify to a closed claimant-backing code");
    match error {
        AbiErrorV1::Conservation(message) => (code.code().to_owned(), (*message).to_owned()),
        other => panic!("claimant backing guard raised a non-conservation error: {other}"),
    }
}

fn assert_outcome(outcome: &Outcome, actual: Result<(), (String, String)>) {
    match (outcome.status.as_str(), actual) {
        ("ACCEPT", Ok(())) => {
            assert!(outcome.code.is_none() && outcome.message.is_none());
        }
        ("REJECT", Err((code, message))) => {
            assert_eq!(outcome.code.as_deref(), Some(code.as_str()));
            assert_eq!(outcome.message.as_deref(), Some(message.as_str()));
        }
        (status, actual) => panic!("outcome {status} does not match {actual:?}"),
    }
}

#[test]
fn reject_message_table_is_shared_with_python() {
    let fixture = load_fixture();
    let expected: BTreeMap<String, String> = ClaimantBackingRejectCodeV1::ALL
        .into_iter()
        .map(|code| (code.code().to_owned(), code.message().to_owned()))
        .collect();
    assert_eq!(fixture.reject_messages, expected);
    for code in ClaimantBackingRejectCodeV1::ALL {
        assert_eq!(
            ClaimantBackingRejectCodeV1::from_message(code.message()),
            Some(code)
        );
    }
    assert_eq!(ClaimantBackingRejectCodeV1::from_message("unrelated"), None);
}

#[test]
fn every_vector_replays_state_view_root_and_outcome() {
    let fixture = load_fixture();
    assert!(
        fixture.vectors.len() == 27,
        "fixture must carry exactly the 27 named obligations rendered by Python"
    );
    for (name, vector) in &fixture.vectors {
        assert!(!vector.obligation.is_empty(), "{name} needs an obligation");
        assert!(vector.spec.is_object(), "{name} needs a builder spec");
        let state: GlobalEconomicStateV1 = serde_json::from_value(vector.state.clone())
            .unwrap_or_else(|error| panic!("{name}: canonical state must decode: {error}"));
        let bytes = canonical_bytes_v1(&state).expect("state must encode");
        assert_eq!(
            hash_bytes_sha256_v1(&bytes),
            vector.state_bytes_sha256,
            "{name}"
        );
        let round_trip: Value = serde_json::from_slice(&bytes).expect("canonical bytes are JSON");
        assert_eq!(round_trip, vector.state, "{name}");
        assert_eq!(
            state.state_root().expect("state root").as_str(),
            vector.expected_state_root,
            "{name}"
        );
        let actual = match derive_claimant_backing_view_v1(&state) {
            Err(error) => {
                assert!(vector.expected_view.is_none() && vector.expected_view_root.is_none());
                Err(reject(&error))
            }
            Ok(view) => {
                let view_bytes = canonical_bytes_v1(&view).expect("view must encode");
                let view_value: Value =
                    serde_json::from_slice(&view_bytes).expect("view bytes are JSON");
                assert_eq!(Some(view_value), vector.expected_view, "{name}");
                assert_eq!(
                    Some(view.view_root().expect("view root").as_str().to_owned()),
                    vector.expected_view_root,
                    "{name}"
                );
                require_claimant_backing_v1(&view).map_err(|error| reject(&error))
            }
        };
        assert_outcome(&vector.expected_outcome, actual);
    }
}

#[test]
fn histories_and_mutation_killers_name_recorded_vectors() {
    let fixture = load_fixture();
    for (history, steps) in &fixture.histories {
        assert!(steps.len() >= 2, "{history}");
        for step in steps {
            assert!(fixture.vectors.contains_key(step), "{history}: {step}");
        }
    }
    for (mutation, vector) in &fixture.mutation_killers {
        assert!(fixture.vectors.contains_key(vector), "{mutation}: {vector}");
    }
    assert!(!fixture.unreachable_mutations.is_empty());
}
