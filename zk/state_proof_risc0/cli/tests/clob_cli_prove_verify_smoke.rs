//! Public CLOB proof smoke for the RISC0 CLI.
//!
//! This drives the binary through stdin/stdout via the public JSON boundary:
//! `tau_state_proof_request` produces a real receipt, and
//! `tau_state_proof_verify` must accept the honest request while rejecting
//! tampered public bindings. It is ignored by default because `default_prover`
//! is a full STARK path and can be slow; release evidence should run it
//! explicitly with:
//!
//! ```text
//! cargo test --manifest-path zk/state_proof_risc0/Cargo.toml \
//!   -p tau-state-proof-risc0-cli --test clob_cli_prove_verify_smoke \
//!   -- --ignored --nocapture
//! ```

use std::io::Write;
use std::process::{Command, Stdio};

use serde_json::{json, Value};
use tau_state_proof_risc0_shared::clob::{
    execute_clob_transition_v1_unchecked_with_journal, ClobBookV1, ClobOrderV1,
    ClobTransitionInputV1, PROOF_TYPE_CLOB,
};

fn asset(b: &str) -> String {
    "0x".to_string() + &b.repeat(32)
}

fn owner(b: &str) -> String {
    "0x".to_string() + &b.repeat(48)
}

fn oid(n: u64) -> String {
    format!("0x{n:064x}")
}

fn hex32(bytes: &[u8; 32]) -> String {
    hex::encode(bytes)
}

fn hx(byte: u8) -> String {
    hex::encode([byte; 32])
}

fn order_json(side_code: u8, price: u64, qty: u64, sequence: u64, id: u64, who: &str) -> Value {
    json!({
        "side_code": side_code,
        "price_q_per_base": price,
        "base_qty": qty,
        "sequence": sequence,
        "order_id": oid(id),
        "owner": owner(who),
    })
}

fn sample() -> (Value, Value, Value) {
    let pre_book_json = json!({
        "base_asset": asset("11"),
        "quote_asset": asset("22"),
        "orders": [
            order_json(1, 100_000_000, 5, 1, 1, "bb")
        ],
    });
    let taker_json = order_json(0, 100_000_000, 5, 10, 99, "aa");
    let input = ClobTransitionInputV1 {
        state_hash: [7u8; 32],
        chain_id: "devnet".to_string(),
        pre_book: ClobBookV1::new(
            asset("11"),
            asset("22"),
            vec![ClobOrderV1 {
                side_code: 1,
                price_q_per_base: 100_000_000,
                base_qty: 5,
                sequence: 1,
                order_id: oid(1),
                owner: owner("bb"),
            }],
        ),
        taker: ClobOrderV1 {
            side_code: 0,
            price_q_per_base: 100_000_000,
            base_qty: 5,
            sequence: 10,
            order_id: oid(99),
            owner: owner("aa"),
        },
        pre_app_hash_present: false,
        pre_app_hash: [0u8; 32],
        expected_post_app_hash: [0u8; 32],
        // Host-side expected-journal generation only needs a nonzero image id.
        // The CLI prover fills and checks the real embedded image id.
        risc0_image_id: [1u32; 8],
    };
    let (journal, _post_book) =
        execute_clob_transition_v1_unchecked_with_journal(input).expect("host transition");
    let context = json!({
        "chain_id": "devnet",
        "app_hash_pre": "",
        "pre_book_root": hex32(&journal.pre_book_root),
        "operation_hash": hex32(&journal.operation_hash),
        "state_delta_hash": hex32(&journal.state_delta_hash),
        "event_log_root": hex32(&journal.event_log_root),
        "matching_rule_hash": hex32(&journal.matching_rule_hash),
        "fee_rule_hash": hex32(&journal.fee_rule_hash),
        "matching_law_rule_hash": hex32(&journal.matching_law_rule_hash),
    });
    let generate_req = json!({
        "schema": "tau_state_proof_request",
        "schema_version": 1,
        "proof_type": PROOF_TYPE_CLOB,
        "state_hash": hx(7),
        "chain_id": "devnet",
        "tau_state": {"app_hash": hex32(&journal.post_app_hash)},
        "context": context,
        "pre_book": pre_book_json,
        "taker": taker_json,
    });
    (
        generate_req,
        context,
        json!({"app_hash": hex32(&journal.post_app_hash)}),
    )
}

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

fn assert_verify_ok(req: &Value) {
    let (status, out, stderr) = run_cli(req);
    assert!(status, "verify CLI failed: {stderr}");
    assert_eq!(out["ok"], Value::Bool(true), "verify output: {out}");
}

fn assert_verify_err(mut req: Value, mutate: impl FnOnce(&mut Value), expected: &str) {
    mutate(&mut req);
    let (status, out, stderr) = run_cli(&req);
    assert!(status, "verify CLI exited unexpectedly: {stderr}");
    assert_eq!(out["ok"], Value::Bool(false), "tamper accepted: {out}");
    let error = out["error"].as_str().unwrap_or("");
    assert!(
        error.contains(expected),
        "expected error containing {expected:?}, got {error:?}"
    );
}

#[test]
#[ignore = "runs a real RISC0 STARK proof through default_prover"]
fn clob_cli_proves_verifies_and_rejects_tampered_bindings() {
    let (generate_req, context, tau_state) = sample();
    // REVIEW(Codex 2026-06-07, grade A- -> A): the CLOB surface previously had
    // strong kernel/guest tests, but no public prove-and-tamper test through the
    // verifier CLI. That left the riskiest boundary, receipt plus caller JSON
    // binding, covered only by private helpers. This smoke exercises the real
    // binary and mutates each load-bearing public commitment.
    let (status, proof, stderr) = run_cli(&generate_req);
    assert!(status, "generate CLI failed: {stderr}");
    assert_eq!(
        proof["proof_type"],
        Value::String(PROOF_TYPE_CLOB.to_string())
    );

    let verify_req = json!({
        "schema": "tau_state_proof_verify",
        "schema_version": 1,
        "state_hash": hx(7),
        "chain_id": "devnet",
        "proof": proof,
        "tau_state": tau_state,
        "context": context,
        "taker": generate_req["taker"].clone(),
    });
    assert_verify_ok(&verify_req);

    assert_verify_err(
        verify_req.clone(),
        |r| r["state_hash"] = Value::String(hx(8)),
        "journal.state_hash mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["chain_id"] = Value::String("wrong-chain".to_string()),
        "chain_id mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["context"]["chain_id"] = Value::String("wrong-chain".to_string()),
        "context.chain_id mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["tau_state"]["app_hash"] = Value::String(hx(9)),
        "post_app_hash mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["context"]["pre_book_root"] = Value::String(hx(10)),
        "context.pre_book_root mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["context"]["event_log_root"] = Value::String(hx(11)),
        "context.event_log_root mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["context"]["state_delta_hash"] = Value::String(hx(12)),
        "context.state_delta_hash mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["context"]["post_book_root"] = Value::String(hx(15)),
        "context.unknown_field:post_book_root",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["proof"]["meta"]["risc0_image_id"] = Value::String(hx(13)),
        "risc0_image_id mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["proof"]["meta"]["matching_rule_hash"] = Value::String(hx(14)),
        "proof.meta.matching_rule_hash mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["proof"]["meta"]["matching_law_rule_hash"] = Value::String(hx(16)),
        "proof.meta.matching_law_rule_hash mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["context"]["matching_law_rule_hash"] = Value::String(hx(17)),
        "context.matching_law_rule_hash mismatch",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["proof"]["proof_type"] = Value::String("risc0.wrong_surface.v1".to_string()),
        "unsupported proof_type",
    );
    assert_verify_err(
        verify_req.clone(),
        |r| r["taker"]["price_q_per_base"] = Value::Number(serde_json::Number::from(200_000_000)),
        "event_log_root mismatch",
    );
}
