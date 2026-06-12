//! 3-way parity: run the SAME boundary table the Tau↔Python differential uses
//! (tests/tau_specs/governance/fixtures/gov_gate_parity_cases.json, generated from
//! gov_parity_cases.py and byte-pinned by test_gov_parity.py) against the Rust
//! kernel, plus the canonical params-digest golden vectors (the cross-language
//! encoder obligation: Rust must reproduce gov_epoch.params_digest byte-for-byte).

use std::collections::BTreeMap;
use std::path::PathBuf;

use zenodex_governance_gate as gate;

fn fixture_path() -> PathBuf {
    // crate dir: rust-runtime/crates/zenodex-governance-gate -> repo root is ../../..
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../../tests/tau_specs/governance/fixtures/gov_gate_parity_cases.json")
}

fn as_u16(v: &serde_json::Value) -> u16 {
    let n = v
        .as_u64()
        .expect("fixture arg must be a non-negative integer");
    u16::try_from(n).expect("fixture arg must fit u16 (in-domain by construction)")
}

fn as_bool(v: &serde_json::Value) -> bool {
    v.as_bool().expect("fixture arg must be a bool")
}

fn dispatch(surface: &str, a: &[serde_json::Value]) -> bool {
    match surface {
        "fee" => gate::fee_revision_ok(
            as_bool(&a[0]),
            as_bool(&a[1]),
            as_u16(&a[2]),
            as_u16(&a[3]),
            as_u16(&a[4]),
            as_u16(&a[5]),
        ),
        "router_split" => gate::router_split_revision_ok(
            as_bool(&a[0]),
            as_bool(&a[1]),
            as_u16(&a[2]),
            as_u16(&a[3]),
            as_u16(&a[4]),
            as_u16(&a[5]),
            as_u16(&a[6]),
            as_u16(&a[7]),
        ),
        "funding" => gate::funding_rate_revision_ok(
            as_bool(&a[0]),
            as_bool(&a[1]),
            as_u16(&a[2]),
            as_u16(&a[3]),
            as_u16(&a[4]),
            as_u16(&a[5]),
        ),
        "collateral" => gate::collateral_ratio_revision_ok(
            as_bool(&a[0]),
            as_bool(&a[1]),
            as_u16(&a[2]),
            as_u16(&a[3]),
            as_u16(&a[4]),
            as_u16(&a[5]),
            as_u16(&a[6]),
            as_u16(&a[7]),
        ),
        "whale" => gate::whale_defense_revision_ok(
            as_bool(&a[0]),
            as_bool(&a[1]),
            as_u16(&a[2]),
            as_u16(&a[3]),
            as_u16(&a[4]),
            as_u16(&a[5]),
        ),
        "action" => gate::action_bound_ok(
            as_bool(&a[0]),
            as_bool(&a[1]),
            as_u16(&a[2]),
            as_u16(&a[3]),
            as_u16(&a[4]),
            as_u16(&a[5]),
            as_u16(&a[6]),
            as_u16(&a[7]),
            as_u16(&a[8]),
            as_u16(&a[9]),
        ),
        "drift" => {
            gate::drift_budget_ok(as_u16(&a[0]), as_u16(&a[1]), as_u16(&a[2]), as_u16(&a[3]))
        }
        "cooldown" => gate::cooldown_ok(as_u16(&a[0]), as_u16(&a[1]), as_u16(&a[2])),
        "charter" => gate::charter_ok(as_bool(&a[0]), as_u16(&a[1]), as_u16(&a[2]), as_u16(&a[3])),
        "epoch_budget" => {
            gate::epoch_budget_ok(as_u16(&a[0]), as_u16(&a[1]), as_u16(&a[2]), as_u16(&a[3]))
        }
        other => panic!("fixture names an unknown surface: {other}"),
    }
}

#[test]
fn rust_matches_shared_boundary_table() {
    let raw = std::fs::read_to_string(fixture_path()).expect("shared parity fixture present");
    let doc: serde_json::Value = serde_json::from_str(&raw).expect("fixture parses");
    let cases = doc["cases"].as_array().expect("cases array");
    assert!(
        cases.len() >= 39,
        "fixture unexpectedly small: {}",
        cases.len()
    );
    for (i, case) in cases.iter().enumerate() {
        let surface = case["surface"].as_str().expect("surface");
        let args = case["args"].as_array().expect("args");
        let expect = case["expect"].as_bool().expect("expect");
        let got = dispatch(surface, args);
        assert_eq!(
            got, expect,
            "case {i} ({surface}, args {args:?}): rust={got}, table expects {expect}",
        );
    }
}

#[test]
fn params_digest_matches_python_golden_vectors() {
    let raw = std::fs::read_to_string(fixture_path()).expect("shared parity fixture present");
    let doc: serde_json::Value = serde_json::from_str(&raw).expect("fixture parses");
    let vectors = doc["params_digest_vectors"].as_array().expect("vectors");
    assert!(!vectors.is_empty());
    for (i, vec) in vectors.iter().enumerate() {
        let params_obj = vec["params"].as_object().expect("params object");
        let expected = vec["sha256_hex"].as_str().expect("sha256_hex");
        let params: BTreeMap<String, u16> = params_obj
            .iter()
            .map(|(k, v)| (k.clone(), as_u16(v)))
            .collect();
        let got = gate::params_digest(&params).expect("plain keys");
        assert_eq!(
            got, expected,
            "digest vector {i}: cross-language encoder drift"
        );
    }
}
