#![forbid(unsafe_code)]
//! `zenodex-runtime` — shadow/replay driver for the deterministic runtime core.
//!
//! Subcommands:
//!
//! ```text
//! zenodex-runtime replay-fee-trace     <trace.json|->   # kernel = fee_router
//! zenodex-runtime replay-guard-trace   <trace.json|->   # kernel = replay_guard
//! zenodex-runtime replay-balance-trace <trace.json|->   # kernel = balances
//! zenodex-runtime replay-zusd-trace    <trace.json|->   # kernel = zusd
//! ```
//!
//! Each reads a golden trace (see `docs/runtime/GOLDEN_TRACE_FORMAT.md`), replays
//! every `tx` through the matching core transition threading a single state from
//! the empty state, and emits the *computed* per-step results (accept/reject,
//! reason, receipt hash, pre/post state roots) as JSON on stdout. The Python
//! conformance and shadow harnesses compare this against the values the
//! authoritative Python runtime recorded.
//!
//! Structural validation here mirrors the Python trace libraries byte-for-byte
//! so the two runtimes reject identical inputs with identical reason strings.

use std::io::Read;
use std::process::ExitCode;

use serde::Serialize;
use serde_json::Value;
use zenodex_runtime_core::balance_kernel::{
    canonical_asset, canonical_pubkey, credit, transfer, BalanceState, MAX_BALANCE,
};
use zenodex_runtime_core::replay_guard::{admit, canonical_sender, ReplayGuardState, U32_MAX};
use zenodex_runtime_core::zusd::{step as zusd_step, ZusdCommand, ZusdState};
use zenodex_runtime_core::{route_fee, FeeAccumulator, FeeSplitTable};

const TX_FIELDS: [&str; 5] = ["kind", "source", "asset", "amount", "split_table"];
const SPLIT_FIELDS: [&str; 4] = ["buyburn_bps", "stakers_bps", "reserve_bps", "hosts_bps"];
const ADMIT_FIELDS: [&str; 3] = ["kind", "sender", "nonce"];
const CREDIT_FIELDS: [&str; 4] = ["kind", "recipient", "asset", "amount"];
const TRANSFER_FIELDS: [&str; 5] = ["kind", "sender", "recipient", "asset", "amount"];

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

/// A computed per-step outcome that owns the next state, generic over kernel.
enum Eval<S> {
    Accept { receipt_hash: String, next: S },
    Reject(String),
}

// --- Shared JSON helpers ------------------------------------------------------

/// If `v` is an integer-shaped JSON number, return its literal string; else `None`.
/// Requires `serde_json`'s `arbitrary_precision` so large integers are exact.
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

// --- fee_router kernel --------------------------------------------------------

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

fn eval_fee_tx(acc: &FeeAccumulator, tx: &Value) -> Eval<FeeAccumulator> {
    let obj = match tx.as_object() {
        Some(o) => o,
        None => return Eval::Reject("malformed_tx".to_string()),
    };
    if obj.get("kind").and_then(Value::as_str) != Some("route_fee") {
        return Eval::Reject("unknown_tx_kind".to_string());
    }
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), &TX_FIELDS) {
        return Eval::Reject(reason);
    }
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
    let split = match parse_split_table(obj.get("split_table")) {
        Ok(t) => t,
        Err(reason) => return Eval::Reject(reason),
    };
    if amount_str.starts_with('-') {
        return Eval::Reject("negative_amount".to_string());
    }
    let amount: u128 = match amount_str.parse::<u128>() {
        Ok(v) => v,
        Err(_) => return Eval::Reject("amount_too_large".to_string()),
    };
    match route_fee(source, asset, amount, &split, acc) {
        Ok(accepted) => Eval::Accept {
            receipt_hash: accepted.receipt.receipt_hash(),
            next: accepted.accumulator,
        },
        Err(reason) => Eval::Reject(reason.reason_str()),
    }
}

// --- replay_guard kernel ------------------------------------------------------

fn eval_admit_tx(state: &ReplayGuardState, tx: &Value) -> Eval<ReplayGuardState> {
    let obj = match tx.as_object() {
        Some(o) => o,
        None => return Eval::Reject("malformed_tx".to_string()),
    };
    if obj.get("kind").and_then(Value::as_str) != Some("admit") {
        return Eval::Reject("unknown_tx_kind".to_string());
    }
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), &ADMIT_FIELDS) {
        return Eval::Reject(reason);
    }
    if !obj.contains_key("sender") || !obj.contains_key("nonce") {
        return Eval::Reject("malformed_tx".to_string());
    }
    // Sender is validated (format + canonical) before the nonce, mirroring the
    // Python `admit` order: a bad sender wins over a bad nonce.
    let sender = match obj.get("sender").and_then(Value::as_str) {
        Some(s) => s,
        None => return Eval::Reject("invalid_sender".to_string()),
    };
    if canonical_sender(sender).is_none() {
        return Eval::Reject("invalid_sender".to_string());
    }
    let nonce = match obj.get("nonce").and_then(classify_integer) {
        Some(s) => match s.parse::<u64>() {
            Ok(v) if (1..=U32_MAX).contains(&v) => v,
            _ => return Eval::Reject("invalid_nonce".to_string()),
        },
        None => return Eval::Reject("invalid_nonce".to_string()),
    };
    match admit(state, sender, nonce) {
        Ok(accepted) => Eval::Accept {
            receipt_hash: accepted.receipt.receipt_hash(),
            next: accepted.state,
        },
        Err(reason) => Eval::Reject(reason.reason_str()),
    }
}

// --- balance kernel -----------------------------------------------------------

/// Parse a JSON value as a balance amount in `[1, MAX_BALANCE]`, else `None`.
fn parse_amount(v: Option<&Value>) -> Option<u128> {
    let s = v.and_then(classify_integer)?;
    match s.parse::<u128>() {
        Ok(x) if (1..=MAX_BALANCE).contains(&x) => Some(x),
        _ => None,
    }
}

fn eval_balance_tx(state: &BalanceState, tx: &Value) -> Eval<BalanceState> {
    let obj = match tx.as_object() {
        Some(o) => o,
        None => return Eval::Reject("malformed_tx".to_string()),
    };
    match obj.get("kind").and_then(Value::as_str) {
        Some("credit") => {
            if let Some(reason) =
                first_unknown_field(obj.keys().map(String::as_str), &CREDIT_FIELDS)
            {
                return Eval::Reject(reason);
            }
            if !obj.contains_key("recipient")
                || !obj.contains_key("asset")
                || !obj.contains_key("amount")
            {
                return Eval::Reject("malformed_tx".to_string());
            }
            // Field order mirrors the core: recipient, asset, amount.
            let recipient = match obj.get("recipient").and_then(Value::as_str) {
                Some(s) if canonical_pubkey(s).is_some() => s,
                _ => return Eval::Reject("invalid_recipient".to_string()),
            };
            let asset = match obj.get("asset").and_then(Value::as_str) {
                Some(s) if canonical_asset(s).is_some() => s,
                _ => return Eval::Reject("invalid_asset".to_string()),
            };
            let amount = match parse_amount(obj.get("amount")) {
                Some(a) => a,
                None => return Eval::Reject("invalid_amount".to_string()),
            };
            match credit(state, recipient, asset, amount) {
                Ok(acc) => Eval::Accept {
                    receipt_hash: acc.receipt.receipt_hash(),
                    next: acc.state,
                },
                Err(reason) => Eval::Reject(reason.reason_str()),
            }
        }
        Some("transfer") => {
            if let Some(reason) =
                first_unknown_field(obj.keys().map(String::as_str), &TRANSFER_FIELDS)
            {
                return Eval::Reject(reason);
            }
            if !obj.contains_key("sender")
                || !obj.contains_key("recipient")
                || !obj.contains_key("asset")
                || !obj.contains_key("amount")
            {
                return Eval::Reject("malformed_tx".to_string());
            }
            // Field order mirrors the core: sender, recipient, asset, amount.
            let sender = match obj.get("sender").and_then(Value::as_str) {
                Some(s) if canonical_pubkey(s).is_some() => s,
                _ => return Eval::Reject("invalid_sender".to_string()),
            };
            let recipient = match obj.get("recipient").and_then(Value::as_str) {
                Some(s) if canonical_pubkey(s).is_some() => s,
                _ => return Eval::Reject("invalid_recipient".to_string()),
            };
            let asset = match obj.get("asset").and_then(Value::as_str) {
                Some(s) if canonical_asset(s).is_some() => s,
                _ => return Eval::Reject("invalid_asset".to_string()),
            };
            let amount = match parse_amount(obj.get("amount")) {
                Some(a) => a,
                None => return Eval::Reject("invalid_amount".to_string()),
            };
            match transfer(state, sender, recipient, asset, amount) {
                Ok(acc) => Eval::Accept {
                    receipt_hash: acc.receipt.receipt_hash(),
                    next: acc.state,
                },
                Err(reason) => Eval::Reject(reason.reason_str()),
            }
        }
        _ => Eval::Reject("unknown_tx_kind".to_string()),
    }
}

// --- zusd kernel --------------------------------------------------------------

/// Integer-shaped arg as a literal string, else `None` (zUSD `_require_pos_int`
/// validates `> 0` in the core). zUSD ignores unknown fields, like the authority.
fn num_arg(obj: &serde_json::Map<String, Value>, key: &str) -> Option<String> {
    obj.get(key).and_then(classify_integer)
}

fn flag(obj: &serde_json::Map<String, Value>, key: &str) -> bool {
    obj.get(key).and_then(Value::as_bool).unwrap_or(false)
}

fn eval_zusd_tx(state: &ZusdState, tx: &Value) -> Eval<ZusdState> {
    let obj = match tx.as_object() {
        Some(o) => o,
        None => return Eval::Reject("malformed_tx".to_string()),
    };
    let cmd = match obj.get("kind").and_then(Value::as_str).unwrap_or("") {
        "advance_epoch" => ZusdCommand::AdvanceEpoch {
            delta: num_arg(obj, "delta"),
        },
        "bootstrap_oracle" => ZusdCommand::BootstrapOracle {
            auth_ok: flag(obj, "auth_ok"),
            price_e8: num_arg(obj, "price_e8"),
        },
        "oracle_report" => ZusdCommand::OracleReport {
            auth_ok: flag(obj, "auth_ok"),
            price_e8: num_arg(obj, "price_e8"),
        },
        "oracle_commit" => ZusdCommand::OracleCommit {
            auth_ok: flag(obj, "auth_ok"),
        },
        "deposit_collateral" => ZusdCommand::DepositCollateral {
            amount_e8: num_arg(obj, "amount_e8"),
        },
        "withdraw_collateral" => ZusdCommand::WithdrawCollateral {
            amount_e8: num_arg(obj, "amount_e8"),
        },
        "mint_zusd" => ZusdCommand::MintZusd {
            amount_e8: num_arg(obj, "amount_e8"),
        },
        "repay_zusd" => ZusdCommand::RepayZusd {
            amount_e8: num_arg(obj, "amount_e8"),
        },
        "deposit_sp" => ZusdCommand::DepositSp {
            amount_e8: num_arg(obj, "amount_e8"),
        },
        "withdraw_sp" => ZusdCommand::WithdrawSp {
            amount_e8: num_arg(obj, "amount_e8"),
        },
        "redeem_zusd" => ZusdCommand::RedeemZusd {
            amount_e8: num_arg(obj, "amount_e8"),
        },
        "liquidate" => ZusdCommand::Liquidate,
        _ => ZusdCommand::Unknown,
    };
    match zusd_step(state, &cmd) {
        Ok(accepted) => Eval::Accept {
            receipt_hash: accepted.receipt_hash,
            next: accepted.state,
        },
        Err(code) => Eval::Reject(code.to_string()),
    }
}

// --- Generic trace driver -----------------------------------------------------

/// Replay every step, threading `state` from its initial value via `eval`.
fn drive<S, F>(
    trace: &Value,
    kernel: &str,
    initial: S,
    root: fn(&S) -> String,
    eval: F,
) -> Result<ReplayOutput, String>
where
    F: Fn(&S, &Value) -> Eval<S>,
{
    let steps = trace
        .get("steps")
        .and_then(Value::as_array)
        .ok_or_else(|| "trace has no \"steps\" array".to_string())?;

    let mut state = initial;
    let initial_state_root = root(&state);
    let null = Value::Null;
    let mut results = Vec::with_capacity(steps.len());

    for (index, step) in steps.iter().enumerate() {
        let pre_state_root = root(&state);
        let tx = step.get("tx").unwrap_or(&null);
        match eval(&state, tx) {
            Eval::Accept { receipt_hash, next } => {
                state = next;
                results.push(StepResult {
                    index,
                    accept: true,
                    reject_reason: None,
                    receipt_hash: Some(receipt_hash),
                    pre_state_root,
                    post_state_root: root(&state),
                });
            }
            Eval::Reject(reason) => {
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
        kernel: kernel.to_string(),
        initial_state_root,
        final_state_root: root(&state),
        results,
    })
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

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let prog = args
        .first()
        .map(String::as_str)
        .unwrap_or("zenodex-runtime");
    let subcommand = args.get(1).map(String::as_str).unwrap_or("");
    if args.len() != 3
        || !matches!(
            subcommand,
            "replay-fee-trace"
                | "replay-guard-trace"
                | "replay-balance-trace"
                | "replay-zusd-trace"
        )
    {
        eprintln!(
            "usage: {prog} <replay-fee-trace|replay-guard-trace|replay-balance-trace|\
             replay-zusd-trace> <trace.json|->"
        );
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

    let output = match subcommand {
        "replay-fee-trace" => drive(
            &trace,
            "fee_router",
            FeeAccumulator::default(),
            FeeAccumulator::state_root,
            eval_fee_tx,
        ),
        "replay-guard-trace" => drive(
            &trace,
            "replay_guard",
            ReplayGuardState::default(),
            ReplayGuardState::state_root,
            eval_admit_tx,
        ),
        "replay-balance-trace" => drive(
            &trace,
            "balances",
            BalanceState::default(),
            BalanceState::state_root,
            eval_balance_tx,
        ),
        "replay-zusd-trace" => drive(
            &trace,
            "zusd",
            ZusdState::default(),
            ZusdState::state_root,
            eval_zusd_tx,
        ),
        _ => unreachable!(),
    };

    match output {
        Ok(out) => match serde_json::to_string_pretty(&out) {
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
