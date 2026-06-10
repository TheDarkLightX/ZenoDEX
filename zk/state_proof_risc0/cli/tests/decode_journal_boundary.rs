//! Boundary teeth for `tau_state_proof_decode_journal` + `tau_state_proof_verifier_identity`.
//!
//! Fail-closed contract under test: NO journal byte is ever echoed unless
//! `receipt.verify(TAU_STATE_PROOF_GUEST_ID)` succeeded first, and the identity
//! probe reports exactly the compiled-in guest id. The happy path over a REAL
//! receipt is covered end-to-end (prove -> decode_journal -> verify) by the Python
//! opt-in e2e tests/integration/test_ws2_refuse_loop_e2e_risc0.py (ZENODEX_WS2_E2E=1),
//! which drives this exact CLI command through the production ReceiptVerifierPort.

use std::io::Write;
use std::process::{Command, Stdio};

use base64::Engine;
use serde_json::{json, Value};

const PROOF_TYPE_PERPS_NP: &str = "risc0.zenodex_perps_np_transition.v1";

fn run_cli(req: &Value) -> (bool, Value, String) {
    let mut child = Command::new(env!("CARGO_BIN_EXE_tau-state-proof-risc0-cli"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn proof cli");
    {
        let stdin = child.stdin.as_mut().expect("stdin");
        stdin
            .write_all(serde_json::to_string(req).expect("json").as_bytes())
            .expect("write request");
    }
    let output = child.wait_with_output().expect("cli exits");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let parsed = serde_json::from_str(&stdout).unwrap_or_else(|_| {
        panic!(
            "cli did not emit JSON; status={:?} stdout={stdout:?} stderr={stderr:?}",
            output.status.code()
        )
    });
    (output.status.success(), parsed, stderr)
}

fn decode_request(proof_b64: &str, proof_type: &str) -> Value {
    json!({
        "schema": "tau_state_proof_decode_journal",
        "schema_version": 1,
        "proof_type": proof_type,
        "proof": proof_b64,
    })
}

fn assert_rejected_without_journal(out: &Value, needle: &str) {
    assert_eq!(out.get("ok"), Some(&Value::Bool(false)), "out={out}");
    assert!(
        out.get("journal").is_none(),
        "rejected decode must not echo a journal: {out}"
    );
    let err = out.get("error").and_then(Value::as_str).unwrap_or("");
    assert!(err.contains(needle), "error {err:?} missing {needle:?}");
}

#[test]
fn identity_probe_reports_compiled_in_guest_id() {
    let (ok, out, _err) = run_cli(&json!({
        "schema": "tau_state_proof_verifier_identity",
        "schema_version": 1,
    }));
    assert!(ok);
    assert_eq!(out.get("ok"), Some(&Value::Bool(true)));
    let words = out
        .get("verifier_image_id_words")
        .and_then(Value::as_array)
        .expect("image id words");
    assert_eq!(words.len(), 8);
    assert!(
        words.iter().any(|w| w.as_u64() != Some(0)),
        "all-zero image id"
    );
    let proof_types = out
        .get("proof_types")
        .and_then(Value::as_array)
        .expect("proof types");
    assert_eq!(proof_types.len(), 3);
}

#[test]
fn rejects_invalid_base64_without_journal() {
    let (ok, out, _err) = run_cli(&decode_request("@@not-base64@@", PROOF_TYPE_PERPS_NP));
    assert!(ok);
    assert_rejected_without_journal(&out, "invalid base64 proof");
}

#[test]
fn rejects_non_receipt_bytes_without_journal() {
    let garbage = base64::engine::general_purpose::STANDARD.encode(b"not a receipt at all");
    let (ok, out, _err) = run_cli(&decode_request(&garbage, PROOF_TYPE_PERPS_NP));
    assert!(ok);
    assert_rejected_without_journal(&out, "invalid receipt bytes");
}

#[test]
fn rejects_missing_proof_type() {
    let (ok, out, _err) = run_cli(&json!({
        "schema": "tau_state_proof_decode_journal",
        "schema_version": 1,
        "proof": "AAAA",
    }));
    assert!(ok);
    assert_rejected_without_journal(&out, "proof_type missing");
}

#[test]
fn rejects_missing_proof_bytes() {
    let (ok, out, _err) = run_cli(&json!({
        "schema": "tau_state_proof_decode_journal",
        "schema_version": 1,
        "proof_type": PROOF_TYPE_PERPS_NP,
    }));
    assert!(ok);
    assert_rejected_without_journal(&out, "proof missing");
}

#[test]
fn rejects_wrong_schema_version() {
    let (ok, out, _err) = run_cli(&json!({
        "schema": "tau_state_proof_decode_journal",
        "schema_version": 2,
        "proof_type": PROOF_TYPE_PERPS_NP,
        "proof": "AAAA",
    }));
    assert!(ok);
    assert_rejected_without_journal(&out, "schema_version");
}
