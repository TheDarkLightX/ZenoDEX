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
//! zenodex-runtime verify-burn-trace    <trace.json|->   # kernel = burn_receipts
//! zenodex-runtime settle-swap-trace    <trace.json|->   # kernel = cpmm_settlement
//! zenodex-runtime canonical-hash       <cases.json|->   # canonical primitive vectors
//! zenodex-runtime verify-state-root    <cases.json|->   # network state-root parity
//! zenodex-runtime perp-math            <cases.json|->   # perp stateless math
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
use zenodex_runtime_core::burn_receipts::{
    rail_receipt_hash, stateless_root, verify_rails, RailInputs,
};
use zenodex_runtime_core::canonical::{
    canonical_json_bytes, domain_sep_bytes, hex_to_bytes_fixed, sha256_hex, CanonicalError,
    JsonValue,
};
use zenodex_runtime_core::cpmm_swap::{
    init_pool, swap_exact_in, swap_exact_out, Pool, BPS_DENOM, DEX_POOL_RESERVE_MAX,
};
use zenodex_runtime_core::perp_math;
use zenodex_runtime_core::replay_guard::{admit, canonical_sender, ReplayGuardState, U32_MAX};
use zenodex_runtime_core::state_root::{
    compute_state_root, BalanceEntry, LpDurationEntry, LpEntry, NonceEntry, PoolEntry, PoolStatus,
    StateInput,
};
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

// --- burn_receipts kernel (stateless rail verifier) ---------------------------

const BURN_RAIL_FIELDS: [&str; 11] = [
    "do_burn",
    "receipt_bound",
    "nullifier_unused",
    "policy_ok",
    "burn_amount",
    "receipt_amount",
    "burn_budget",
    "supply_before",
    "supply_after",
    "batch_burn_sum_before",
    "batch_burn_sum_after",
];

/// Extract an integer rail field, saturating out-of-`i64` integers (the rails
/// reject anything outside `[0, 0xFFFF]` regardless, matching Python's bigint).
fn rail_field(obj: &serde_json::Map<String, Value>, key: &str) -> Option<i64> {
    let s = obj.get(key).and_then(classify_integer)?;
    Some(s.parse::<i64>().unwrap_or(if s.starts_with('-') {
        i64::MIN
    } else {
        i64::MAX
    }))
}

fn burn_state_root(_: &()) -> String {
    stateless_root()
}

fn eval_burn_tx(_state: &(), tx: &Value) -> Eval<()> {
    let obj = match tx.as_object() {
        Some(o) => o,
        None => return Eval::Reject("bad_numeric_field".to_string()),
    };
    let mut vals = [0i64; 11];
    for (i, key) in BURN_RAIL_FIELDS.iter().enumerate() {
        match rail_field(obj, key) {
            Some(v) => vals[i] = v,
            None => return Eval::Reject("bad_numeric_field".to_string()),
        }
    }
    let r = RailInputs {
        do_burn: vals[0],
        receipt_bound: vals[1],
        nullifier_unused: vals[2],
        policy_ok: vals[3],
        burn_amount: vals[4],
        receipt_amount: vals[5],
        burn_budget: vals[6],
        supply_before: vals[7],
        supply_after: vals[8],
        batch_burn_sum_before: vals[9],
        batch_burn_sum_after: vals[10],
    };
    match verify_rails(&r) {
        Ok(()) => Eval::Accept {
            receipt_hash: rail_receipt_hash(&r),
            next: (),
        },
        Err(code) => Eval::Reject(code.to_string()),
    }
}

// --- canonical primitives (cross-language differential) -----------------------

/// Lower a `serde_json::Value` into the core's `JsonValue`, rejecting floats
/// exactly as the Python `canonical_json_bytes` does (non-integer numbers).
fn lower_value(v: &Value) -> Result<JsonValue, CanonicalError> {
    match v {
        Value::Null => Ok(JsonValue::Null),
        Value::Bool(b) => Ok(JsonValue::Bool(*b)),
        Value::Number(_) => match classify_integer(v) {
            Some(s) => JsonValue::int_from_decimal_str(&s).ok_or(CanonicalError::FloatNotAllowed),
            None => Err(CanonicalError::FloatNotAllowed),
        },
        Value::String(s) => Ok(JsonValue::Str(s.clone())),
        Value::Array(items) => {
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                out.push(lower_value(item)?);
            }
            Ok(JsonValue::Array(out))
        }
        Value::Object(map) => {
            let mut out = Vec::with_capacity(map.len());
            for (k, val) in map {
                out.push((k.clone(), lower_value(val)?));
            }
            Ok(JsonValue::Object(out))
        }
    }
}

fn to_hex_0x(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(2 + bytes.len() * 2);
    s.push_str("0x");
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[derive(Serialize)]
struct CanonicalCaseResult {
    index: usize,
    ok: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    bytes: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    hash: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
}

#[derive(Serialize)]
struct CanonicalOutput {
    version: u32,
    results: Vec<CanonicalCaseResult>,
}

fn err_case(index: usize, code: &str) -> CanonicalCaseResult {
    CanonicalCaseResult {
        index,
        ok: false,
        bytes: None,
        hash: None,
        code: Some(code.to_string()),
    }
}

/// Drive a `{ "cases": [ ... ] }` request through the canonical primitives.
/// Each case is `{"op":"json_bytes"|"json_hash","value":<any>}` or
/// `{"op":"hex_to_bytes","hex":"0x..","nbytes":N}`. Output mirrors per-case
/// results so the Python authority can diff `bytes`/`hash`/`code` exactly.
fn run_canonical_cases(req: &Value) -> Result<CanonicalOutput, String> {
    let cases = req
        .get("cases")
        .and_then(Value::as_array)
        .ok_or_else(|| "request has no \"cases\" array".to_string())?;
    let mut results = Vec::with_capacity(cases.len());
    for (index, case) in cases.iter().enumerate() {
        let obj = match case.as_object() {
            Some(o) => o,
            None => {
                results.push(err_case(index, "malformed_case"));
                continue;
            }
        };
        match obj.get("op").and_then(Value::as_str) {
            Some("json_bytes") | Some("json_hash") => {
                let value = obj.get("value").unwrap_or(&Value::Null);
                match lower_value(value) {
                    Ok(jv) => {
                        let bytes = canonical_json_bytes(&jv);
                        results.push(CanonicalCaseResult {
                            index,
                            ok: true,
                            bytes: Some(to_hex_0x(&bytes)),
                            hash: Some(sha256_hex(&bytes)),
                            code: None,
                        });
                    }
                    Err(e) => results.push(err_case(index, e.code())),
                }
            }
            Some("hex_to_bytes") => {
                let hex_str = match obj.get("hex").and_then(Value::as_str) {
                    Some(s) => s,
                    None => {
                        results.push(err_case(index, "malformed_case"));
                        continue;
                    }
                };
                let nbytes = match obj.get("nbytes").and_then(classify_integer) {
                    Some(s) => match s.parse::<usize>() {
                        Ok(n) if n > 0 => n,
                        _ => {
                            results.push(err_case(index, "malformed_case"));
                            continue;
                        }
                    },
                    None => {
                        results.push(err_case(index, "malformed_case"));
                        continue;
                    }
                };
                match hex_to_bytes_fixed(hex_str, nbytes) {
                    Ok(bytes) => results.push(CanonicalCaseResult {
                        index,
                        ok: true,
                        bytes: Some(to_hex_0x(&bytes)),
                        hash: None,
                        code: None,
                    }),
                    Err(e) => results.push(err_case(index, e.code())),
                }
            }
            // sha256(domain_sep(label, version) + canonical_json_bytes(value)) —
            // the shape shared by the DEX intent auth message hash and the burn
            // receipt body hash (Phase F).
            Some("domain_json_hash") => {
                let label = match obj.get("label").and_then(Value::as_str) {
                    Some(s) => s,
                    None => {
                        results.push(err_case(index, "malformed_case"));
                        continue;
                    }
                };
                // domain_sep_bytes in Python rejects empty / non-ASCII / NUL labels.
                if label.is_empty() || !label.is_ascii() || label.contains('\u{0}') {
                    results.push(err_case(index, "bad_domain_label"));
                    continue;
                }
                let version = match obj.get("version") {
                    None => 1u32,
                    Some(v) => match classify_integer(v).and_then(|s| s.parse::<u32>().ok()) {
                        Some(n) if n > 0 => n,
                        _ => {
                            results.push(err_case(index, "bad_domain_version"));
                            continue;
                        }
                    },
                };
                let value = obj.get("value").unwrap_or(&Value::Null);
                match lower_value(value) {
                    Ok(jv) => {
                        let mut msg = domain_sep_bytes(label, version);
                        msg.extend_from_slice(&canonical_json_bytes(&jv));
                        results.push(CanonicalCaseResult {
                            index,
                            ok: true,
                            bytes: None,
                            hash: Some(sha256_hex(&msg)),
                            code: None,
                        });
                    }
                    Err(e) => results.push(err_case(index, e.code())),
                }
            }
            _ => results.push(err_case(index, "unknown_op")),
        }
    }
    Ok(CanonicalOutput {
        version: 1,
        results,
    })
}

// --- cpmm settlement swap kernel ----------------------------------------------

const INIT_FIELDS: [&str; 4] = ["kind", "reserve0", "reserve1", "fee_bps"];
const EXACT_IN_FIELDS: [&str; 4] = ["kind", "zero_for_one", "amount_in", "min_amount_out"];
const EXACT_OUT_FIELDS: [&str; 4] = ["kind", "zero_for_one", "amount_out", "max_amount_in"];

/// Present integer-shaped field as a literal string, else `None` (missing/non-int).
fn int_field(obj: &serde_json::Map<String, Value>, key: &str) -> Option<String> {
    obj.get(key).and_then(classify_integer)
}

/// Parse to u128, saturating negatives/oversized to `u128::MAX` so the kernel's
/// range checks reject them at the same boundary as the Python authority.
fn u128_sat(s: &str) -> u128 {
    s.parse::<u128>().unwrap_or(u128::MAX)
}

fn eval_cpmm_tx(pool: &Pool, tx: &Value) -> Eval<Pool> {
    let obj = match tx.as_object() {
        Some(o) => o,
        None => return Eval::Reject("malformed_tx".to_string()),
    };
    let kind = obj.get("kind").and_then(Value::as_str).unwrap_or("");
    let allowed: &[&str] = match kind {
        "init_pool" => &INIT_FIELDS,
        "swap_exact_in" => &EXACT_IN_FIELDS,
        "swap_exact_out" => &EXACT_OUT_FIELDS,
        _ => return Eval::Reject("unknown_tx_kind".to_string()),
    };
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), allowed) {
        return Eval::Reject(reason);
    }

    let result = match kind {
        "init_pool" => {
            // `already_initialized` precedes field validation (mirrors the harness).
            if pool.initialized {
                return Eval::Reject("already_initialized".to_string());
            }
            let (r0, r1, fee) = match (
                int_field(obj, "reserve0"),
                int_field(obj, "reserve1"),
                int_field(obj, "fee_bps"),
            ) {
                (Some(a), Some(b), Some(c)) => (a, b, c),
                _ => return Eval::Reject("malformed_tx".to_string()),
            };
            // Reserves and fee carry their own out-of-domain reject codes.
            let reserve0 = match r0.parse::<u128>() {
                Ok(v) if (1..=DEX_POOL_RESERVE_MAX).contains(&v) => v,
                _ => return Eval::Reject("invalid_reserve".to_string()),
            };
            let reserve1 = match r1.parse::<u128>() {
                Ok(v) if (1..=DEX_POOL_RESERVE_MAX).contains(&v) => v,
                _ => return Eval::Reject("invalid_reserve".to_string()),
            };
            let fee_bps = match fee.parse::<u128>() {
                Ok(v) if v <= BPS_DENOM => v,
                _ => return Eval::Reject("invalid_fee_bps".to_string()),
            };
            init_pool(pool, reserve0, reserve1, fee_bps)
        }
        "swap_exact_in" => {
            let zero_for_one = match obj.get("zero_for_one").and_then(Value::as_bool) {
                Some(b) => b,
                None => return Eval::Reject("malformed_tx".to_string()),
            };
            let amount_in = match int_field(obj, "amount_in") {
                Some(s) => u128_sat(&s),
                None => return Eval::Reject("malformed_tx".to_string()),
            };
            let min_out = match int_field(obj, "min_amount_out") {
                Some(s) if !s.starts_with('-') => u128_sat(&s),
                _ => return Eval::Reject("malformed_tx".to_string()),
            };
            swap_exact_in(pool, zero_for_one, amount_in, min_out)
        }
        "swap_exact_out" => {
            let zero_for_one = match obj.get("zero_for_one").and_then(Value::as_bool) {
                Some(b) => b,
                None => return Eval::Reject("malformed_tx".to_string()),
            };
            let amount_out = match int_field(obj, "amount_out") {
                Some(s) => u128_sat(&s),
                None => return Eval::Reject("malformed_tx".to_string()),
            };
            let max_in = match int_field(obj, "max_amount_in") {
                Some(s) if !s.starts_with('-') => u128_sat(&s),
                _ => return Eval::Reject("malformed_tx".to_string()),
            };
            swap_exact_out(pool, zero_for_one, amount_out, max_in)
        }
        _ => unreachable!(),
    };

    match result {
        Ok(accepted) => Eval::Accept {
            receipt_hash: accepted.receipt.receipt_hash(),
            next: accepted.pool,
        },
        Err(code) => Eval::Reject(code.to_string()),
    }
}

// --- state-root (cross-language differential) ---------------------------------

fn req_str(obj: &serde_json::Map<String, Value>, key: &str) -> Result<String, String> {
    obj.get(key)
        .and_then(Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| "malformed_state".to_string())
}

/// Required non-negative integer that must fit `u128` (else out of domain).
fn req_u128(obj: &serde_json::Map<String, Value>, key: &str) -> Result<u128, String> {
    let s = obj
        .get(key)
        .and_then(classify_integer)
        .ok_or("malformed_state")?;
    if s.starts_with('-') {
        return Err("malformed_state".to_string());
    }
    s.parse::<u128>()
        .map_err(|_| "amount_out_of_domain".to_string())
}

/// Optional timestamp: missing or JSON null -> None; integer -> Some(u128).
fn opt_u128(obj: &serde_json::Map<String, Value>, key: &str) -> Result<Option<u128>, String> {
    match obj.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(_) => Ok(Some(req_u128(obj, key)?)),
    }
}

fn arr<'a>(state: &'a Value, key: &str) -> Result<&'a Vec<Value>, String> {
    match state.get(key) {
        None | Some(Value::Null) => Err("__empty__".to_string()), // sentinel: treat as []
        Some(Value::Array(a)) => Ok(a),
        Some(_) => Err("malformed_state".to_string()),
    }
}

fn each_obj(state: &Value, key: &str) -> Result<Vec<serde_json::Map<String, Value>>, String> {
    match arr(state, key) {
        Ok(items) => items
            .iter()
            .map(|v| {
                v.as_object()
                    .cloned()
                    .ok_or_else(|| "malformed_state".to_string())
            })
            .collect(),
        Err(s) if s == "__empty__" => Ok(Vec::new()),
        Err(e) => Err(e),
    }
}

fn fee_accumulator_dust(state: &Value) -> Result<u128, String> {
    match state.get("fee_accumulator") {
        None | Some(Value::Null) => Ok(0),
        Some(Value::Object(o)) => match o.get("dust") {
            None | Some(Value::Null) => Ok(0),
            Some(_) => req_u128(o, "dust"),
        },
        Some(_) => Err("malformed_state".to_string()),
    }
}

fn parse_state(state: &Value) -> Result<StateInput, String> {
    if !state.is_object() {
        return Err("malformed_state".to_string());
    }
    let mut input = StateInput {
        fee_accumulator_dust: fee_accumulator_dust(state)?,
        ..Default::default()
    };
    for o in each_obj(state, "balances")? {
        input.balances.push(BalanceEntry {
            pubkey: req_str(&o, "pubkey")?,
            asset: req_str(&o, "asset")?,
            amount: req_u128(&o, "amount")?,
        });
    }
    for o in each_obj(state, "pools")? {
        let status = PoolStatus::from_label(&req_str(&o, "status")?)
            .ok_or_else(|| "unknown_pool_status".to_string())?;
        input.pools.push(PoolEntry {
            pool_id: req_str(&o, "pool_id")?,
            asset0: req_str(&o, "asset0")?,
            asset1: req_str(&o, "asset1")?,
            reserve0: req_u128(&o, "reserve0")?,
            reserve1: req_u128(&o, "reserve1")?,
            fee_bps: req_u128(&o, "fee_bps")?,
            lp_supply: req_u128(&o, "lp_supply")?,
            status,
            created_at: req_u128(&o, "created_at")?,
            curve_tag: req_str(&o, "curve_tag")?,
            curve_params: req_str(&o, "curve_params")?,
        });
    }
    for o in each_obj(state, "lp_balances")? {
        input.lp_balances.push(LpEntry {
            pubkey: req_str(&o, "pubkey")?,
            pool_id: req_str(&o, "pool_id")?,
            amount: req_u128(&o, "amount")?,
        });
    }
    for o in each_obj(state, "lp_duration_risk")? {
        input.lp_duration_risk.push(LpDurationEntry {
            pubkey: req_str(&o, "pubkey")?,
            pool_id: req_str(&o, "pool_id")?,
            last_mint_timestamp: opt_u128(&o, "last_mint_timestamp")?,
            last_remove_timestamp: opt_u128(&o, "last_remove_timestamp")?,
            churn_tier: req_u128(&o, "churn_tier")?,
            last_churn_update_timestamp: opt_u128(&o, "last_churn_update_timestamp")?,
        });
    }
    for o in each_obj(state, "nonces")? {
        input.nonces.push(NonceEntry {
            pubkey: req_str(&o, "pubkey")?,
            last_nonce: req_u128(&o, "last_nonce")?,
        });
    }
    Ok(input)
}

#[derive(Serialize)]
struct StateRootCaseResult {
    index: usize,
    ok: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    state_root: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
}

#[derive(Serialize)]
struct StateRootOutput {
    version: u32,
    results: Vec<StateRootCaseResult>,
}

/// Drive a `{ "cases": [ <state>, ... ] }` request through `compute_state_root`.
fn run_state_root_cases(req: &Value) -> Result<StateRootOutput, String> {
    let cases = req
        .get("cases")
        .and_then(Value::as_array)
        .ok_or_else(|| "request has no \"cases\" array".to_string())?;
    let mut results = Vec::with_capacity(cases.len());
    for (index, case) in cases.iter().enumerate() {
        let result = match parse_state(case) {
            Ok(input) => match compute_state_root(&input) {
                Ok(root) => StateRootCaseResult {
                    index,
                    ok: true,
                    state_root: Some(root),
                    code: None,
                },
                Err(e) => StateRootCaseResult {
                    index,
                    ok: false,
                    state_root: None,
                    code: Some(e.code()),
                },
            },
            Err(code) => StateRootCaseResult {
                index,
                ok: false,
                state_root: None,
                code: Some(code),
            },
        };
        results.push(result);
    }
    Ok(StateRootOutput {
        version: 1,
        results,
    })
}

// --- perp stateless math (cross-language differential) ------------------------

#[derive(Serialize)]
struct PerpMathCaseResult {
    index: usize,
    ok: bool,
    /// Integer-valued result, serialized as a decimal string (values fit i128).
    #[serde(skip_serializing_if = "Option::is_none")]
    value: Option<String>,
    /// Bool-valued result (predicates).
    #[serde(skip_serializing_if = "Option::is_none")]
    flag: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
}

#[derive(Serialize)]
struct PerpMathOutput {
    version: u32,
    results: Vec<PerpMathCaseResult>,
}

fn perp_err(index: usize, code: &str) -> PerpMathCaseResult {
    PerpMathCaseResult {
        index,
        ok: false,
        value: None,
        flag: None,
        code: Some(code.to_string()),
    }
}

fn perp_int(index: usize, v: i128) -> PerpMathCaseResult {
    PerpMathCaseResult {
        index,
        ok: true,
        value: Some(v.to_string()),
        flag: None,
        code: None,
    }
}

fn perp_bool(index: usize, b: bool) -> PerpMathCaseResult {
    PerpMathCaseResult {
        index,
        ok: true,
        value: None,
        flag: Some(b),
        code: None,
    }
}

/// Read a signed integer arg bounded by `±max_abs` (else `Err` reject code).
fn arg_bounded(
    obj: &serde_json::Map<String, Value>,
    key: &str,
    max_abs: i128,
) -> Result<i128, String> {
    let s = obj
        .get(key)
        .and_then(classify_integer)
        .ok_or("malformed_case")?;
    let v = s.parse::<i128>().map_err(|_| "out_of_domain".to_string())?;
    let abs = v.checked_abs().ok_or_else(|| "out_of_domain".to_string())?;
    if abs > max_abs {
        return Err("out_of_domain".to_string());
    }
    Ok(v)
}

fn arg_mag(obj: &serde_json::Map<String, Value>, key: &str) -> Result<i128, String> {
    arg_bounded(obj, key, perp_math::MAX_ABS)
}

fn arg_bps(obj: &serde_json::Map<String, Value>, key: &str) -> Result<i128, String> {
    arg_bounded(obj, key, perp_math::MAX_BPS)
}

fn arg_bool(obj: &serde_json::Map<String, Value>, key: &str) -> Result<bool, String> {
    obj.get(key)
        .and_then(Value::as_bool)
        .ok_or("malformed_case".to_string())
}

fn eval_perp_case(obj: &serde_json::Map<String, Value>) -> Result<PerpMathCaseResult, String> {
    // index is filled by the caller; use 0 here and overwrite.
    let op = obj
        .get("op")
        .and_then(Value::as_str)
        .ok_or("malformed_case")?;
    let r = match op {
        "is_oracle_fresh" => perp_bool(
            0,
            perp_math::is_oracle_fresh(
                arg_mag(obj, "now_epoch")?,
                arg_mag(obj, "oracle_last_update_epoch")?,
                arg_mag(obj, "max_oracle_staleness_epochs")?,
                arg_bool(obj, "oracle_seen")?,
            ),
        ),
        "oracle_move_violated" => perp_bool(
            0,
            perp_math::oracle_move_violated(
                arg_mag(obj, "clearing_price_e8")?,
                arg_mag(obj, "index_price_e8")?,
                arg_bps(obj, "max_oracle_move_bps")?,
                arg_bool(obj, "oracle_seen")?,
            ),
        ),
        "settle_price" => perp_int(
            0,
            perp_math::settle_price(
                arg_mag(obj, "clearing_price_e8")?,
                arg_mag(obj, "index_price_e8")?,
                arg_bps(obj, "max_oracle_move_bps")?,
                arg_bool(obj, "oracle_seen")?,
            ),
        ),
        "notional_quote" => perp_int(
            0,
            perp_math::notional_quote(arg_mag(obj, "position_base")?, arg_mag(obj, "price_e8")?),
        ),
        "maint_margin_req" => perp_int(
            0,
            perp_math::maint_margin_req(
                arg_mag(obj, "position_base")?,
                arg_mag(obj, "price_e8")?,
                arg_bps(obj, "maint_bps")?,
                arg_bps(obj, "depeg_bps")?,
            ),
        ),
        "init_margin_req" => perp_int(
            0,
            perp_math::init_margin_req(
                arg_mag(obj, "position_base")?,
                arg_mag(obj, "price_e8")?,
                arg_bps(obj, "init_bps")?,
            ),
        ),
        "pnl_quote" => perp_int(
            0,
            perp_math::pnl_quote(
                arg_mag(obj, "position_base")?,
                arg_mag(obj, "settle_price_e8")?,
                arg_mag(obj, "index_price_e8")?,
            ),
        ),
        "is_liquidatable" => perp_bool(
            0,
            perp_math::is_liquidatable(
                arg_mag(obj, "position_base")?,
                arg_mag(obj, "collateral_after_pnl")?,
                arg_mag(obj, "settle_price_e8")?,
                arg_bps(obj, "maintenance_margin_bps")?,
                arg_bps(obj, "depeg_buffer_bps")?,
            ),
        ),
        "funding_payment" => perp_int(
            0,
            perp_math::funding_payment(
                arg_mag(obj, "position_base")?,
                arg_mag(obj, "index_price_e8")?,
                arg_bps(obj, "rate_bps")?,
            ),
        ),
        _ => return Err("unknown_op".to_string()),
    };
    Ok(r)
}

fn run_perp_math_cases(req: &Value) -> Result<PerpMathOutput, String> {
    let cases = req
        .get("cases")
        .and_then(Value::as_array)
        .ok_or_else(|| "request has no \"cases\" array".to_string())?;
    let mut results = Vec::with_capacity(cases.len());
    for (index, case) in cases.iter().enumerate() {
        let result = match case.as_object() {
            Some(obj) => match eval_perp_case(obj) {
                Ok(mut r) => {
                    r.index = index;
                    r
                }
                Err(code) => perp_err(index, &code),
            },
            None => perp_err(index, "malformed_case"),
        };
        results.push(result);
    }
    Ok(PerpMathOutput {
        version: 1,
        results,
    })
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
                | "verify-burn-trace"
                | "settle-swap-trace"
                | "canonical-hash"
                | "verify-state-root"
                | "perp-math"
        )
    {
        eprintln!(
            "usage: {prog} <replay-fee-trace|replay-guard-trace|replay-balance-trace|\
             replay-zusd-trace|verify-burn-trace|settle-swap-trace|canonical-hash|\
             verify-state-root|perp-math> <input.json|->"
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

    // The canonical-primitive differential has its own request/response shape
    // (a list of cases, not a state-threaded trace), so handle it separately.
    if subcommand == "canonical-hash" {
        return match run_canonical_cases(&trace) {
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
        };
    }

    if subcommand == "verify-state-root" {
        return match run_state_root_cases(&trace) {
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
        };
    }

    if subcommand == "perp-math" {
        return match run_perp_math_cases(&trace) {
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
        };
    }

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
        "verify-burn-trace" => drive(&trace, "burn_receipts", (), burn_state_root, eval_burn_tx),
        "settle-swap-trace" => drive(
            &trace,
            "cpmm_settlement",
            Pool::default(),
            Pool::state_root,
            eval_cpmm_tx,
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
