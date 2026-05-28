#![forbid(unsafe_code)]
//! `zenodex-runtime` — shadow/replay driver for the deterministic runtime core.
//!
//! Subcommand:
//!
//! ```text
//! zenodex-runtime replay-fee-trace <trace.json|->
//! ```
//!
//! Reads a golden trace (see `docs/runtime/GOLDEN_TRACE_FORMAT.md`), replays
//! every `tx` through [`zenodex_runtime_core::route_fee`] threading a single
//! [`FeeAccumulator`] from zero, and emits the *computed* per-step results
//! (accept/reject, reason, receipt hash, pre/post state roots) as JSON on
//! stdout. The Python conformance and shadow-replay harnesses compare this
//! output against the values the authoritative Python runtime recorded.
//!
//! The structural validation here mirrors `tools/runtime/golden_trace_lib.py`
//! (`apply_tx`) byte-for-byte so the two runtimes reject identical inputs with
//! identical reason strings.

use std::io::Read;
use std::process::ExitCode;

use serde::Serialize;
use serde_json::Value;
use zenodex_runtime_core::{route_fee, FeeAccumulator, FeeSplitTable};

const TX_FIELDS: [&str; 5] = ["kind", "source", "asset", "amount", "split_table"];
const SPLIT_FIELDS: [&str; 4] = ["buyburn_bps", "stakers_bps", "reserve_bps", "hosts_bps"];

#[derive(Serialize)]
struct StepResult {
    index: usize,
    accept: bool,
    reject_reason: Option<String>,
    receipt_hash: Option<String>,
    pre_state_root: String,
    post_state_root: String,
}

#[derive(Serialize)]
struct ReplayOutput {
    version: u32,
    kernel: String,
    initial_state_root: String,
    final_state_root: String,
    results: Vec<StepResult>,
}

enum Eval {
    Accept {
        receipt_hash: String,
        new_acc: FeeAccumulator,
    },
    Reject(String),
}

/// If `v` is an integer-shaped JSON number, return its literal string (e.g.
/// `"-1"`, `"5192296858534827628530496329220096"`); otherwise `None`. Requires
/// `serde_json`'s `arbitrary_precision` so large integers are not lossily
/// coerced to `f64`.
fn classify_integer(v: &Value) -> Option<String> {
    match v {
        Value::Number(n) => {
            let s = n.to_string();
            let body = s.strip_prefix('-').unwrap_or(&s);
            if !body.is_empty() && body.bytes().all(|b| b.is_ascii_digit()) {
                Some(s)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Parse a bps value: integer-shaped numbers saturate to the `i64` range so
/// out-of-range values are rejected by `route_fee` as `split_component_out_of_range`
/// (matching the Python reference's unbounded-int behavior). Non-integers -> `None`.
fn parse_bps(v: &Value) -> Option<i64> {
    let s = classify_integer(v)?;
    Some(s.parse::<i64>().unwrap_or(if s.starts_with('-') {
        i64::MIN
    } else {
        i64::MAX
    }))
}

fn first_unknown_field<'a>(
    keys: impl Iterator<Item = &'a str>,
    allowed: &[&str],
) -> Option<String> {
    let mut extras: Vec<&str> = keys.filter(|k| !allowed.contains(k)).collect();
    if extras.is_empty() {
        return None;
    }
    extras.sort_unstable();
    Some(format!("unknown_field:{}", extras[0]))
}

fn parse_split_table(v: Option<&Value>) -> Result<FeeSplitTable, String> {
    let obj = match v.and_then(|v| v.as_object()) {
        Some(o) => o,
        None => return Err("malformed_tx".to_string()),
    };
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), &SPLIT_FIELDS) {
        return Err(reason);
    }
    let mut vals = [0i64; 4];
    for (i, field) in SPLIT_FIELDS.iter().enumerate() {
        match obj.get(*field).and_then(parse_bps) {
            Some(x) => vals[i] = x,
            None => return Err("malformed_tx".to_string()),
        }
    }
    Ok(FeeSplitTable {
        buyburn_bps: vals[0],
        stakers_bps: vals[1],
        reserve_bps: vals[2],
        hosts_bps: vals[3],
    })
}

fn eval_tx(acc: &FeeAccumulator, tx: &Value) -> Eval {
    let obj = match tx.as_object() {
        Some(o) => o,
        None => return Eval::Reject("malformed_tx".to_string()),
    };

    // 1) kind
    if obj.get("kind").and_then(Value::as_str) != Some("route_fee") {
        return Eval::Reject("unknown_tx_kind".to_string());
    }
    // 2) no unknown tx fields
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), &TX_FIELDS) {
        return Eval::Reject(reason);
    }
    // 3) source / asset are strings; amount is integer-shaped
    let source = match obj.get("source").and_then(Value::as_str) {
        Some(s) => s,
        None => return Eval::Reject("malformed_tx".to_string()),
    };
    let asset = match obj.get("asset").and_then(Value::as_str) {
        Some(s) => s,
        None => return Eval::Reject("malformed_tx".to_string()),
    };
    let amount_str = match obj.get("amount").and_then(classify_integer) {
        Some(s) => s,
        None => return Eval::Reject("malformed_tx".to_string()),
    };
    // 4) split table (parsed before amount sign/range, mirroring Python order)
    let split = match parse_split_table(obj.get("split_table")) {
        Ok(t) => t,
        Err(reason) => return Eval::Reject(reason),
    };
    // 5) amount sign + u128 fit
    if amount_str.starts_with('-') {
        return Eval::Reject("negative_amount".to_string());
    }
    let amount: u128 = match amount_str.parse::<u128>() {
        Ok(v) => v,
        Err(_) => return Eval::Reject("amount_too_large".to_string()),
    };
    // 6) semantic transition
    match route_fee(source, asset, amount, &split, acc) {
        Ok(accepted) => Eval::Accept {
            receipt_hash: accepted.receipt.receipt_hash(),
            new_acc: accepted.accumulator,
        },
        Err(reason) => Eval::Reject(reason.reason_str()),
    }
}

fn read_input(path: &str) -> std::io::Result<String> {
    if path == "-" {
        let mut s = String::new();
        std::io::stdin().read_to_string(&mut s)?;
        Ok(s)
    } else {
        std::fs::read_to_string(path)
    }
}

fn run(trace: &Value) -> Result<ReplayOutput, String> {
    let steps = trace
        .get("steps")
        .and_then(Value::as_array)
        .ok_or_else(|| "trace has no \"steps\" array".to_string())?;

    let mut acc = FeeAccumulator::default();
    let initial_state_root = acc.state_root();
    let null = Value::Null;
    let mut results = Vec::with_capacity(steps.len());

    for (index, step) in steps.iter().enumerate() {
        let pre_state_root = acc.state_root();
        let tx = step.get("tx").unwrap_or(&null);
        match eval_tx(&acc, tx) {
            Eval::Accept {
                receipt_hash,
                new_acc,
            } => {
                acc = new_acc;
                results.push(StepResult {
                    index,
                    accept: true,
                    reject_reason: None,
                    receipt_hash: Some(receipt_hash),
                    pre_state_root,
                    post_state_root: acc.state_root(),
                });
            }
            Eval::Reject(reason) => {
                // Rejection => state unchanged.
                results.push(StepResult {
                    index,
                    accept: false,
                    reject_reason: Some(reason),
                    receipt_hash: None,
                    pre_state_root: pre_state_root.clone(),
                    post_state_root: pre_state_root,
                });
            }
        }
    }

    Ok(ReplayOutput {
        version: 1,
        kernel: "fee_router".to_string(),
        initial_state_root,
        final_state_root: acc.state_root(),
        results,
    })
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let prog = args
        .first()
        .map(String::as_str)
        .unwrap_or("zenodex-runtime");
    if args.len() != 3 || args[1] != "replay-fee-trace" {
        eprintln!("usage: {prog} replay-fee-trace <trace.json|->");
        return ExitCode::from(2);
    }

    let input = match read_input(&args[2]) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {e}", args[2]);
            return ExitCode::from(2);
        }
    };
    let trace: Value = match serde_json::from_str(&input) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("error: invalid JSON: {e}");
            return ExitCode::from(2);
        }
    };
    match run(&trace) {
        Ok(output) => match serde_json::to_string_pretty(&output) {
            Ok(s) => {
                println!("{s}");
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("error: cannot serialize output: {e}");
                ExitCode::from(2)
            }
        },
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(2)
        }
    }
}
