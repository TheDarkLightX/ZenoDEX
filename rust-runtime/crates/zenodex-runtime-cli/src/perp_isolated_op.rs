//! Authority-grade **materialized** isolated-perps transition.
//!
//! Unlike the per-op *checker* subcommands (which validate selected fields), this
//! surface emits the **full post-market state** (`quote_asset`, every global key,
//! every account) plus the **exact kernel effect payload**. The Python bridge
//! consumes it as a `rust_shadow` check (full state + effect parity, fail-closed
//! on any mismatch). It is NOT yet an authority *driver*: Rust post-checks
//! Python's transition; true authority (Rust deciding accept/reject from the
//! pre-state and committing the materialized result) is a later step, gated on
//! all ops being materialized and exact effect parity holding everywhere.
//!
//! Design:
//! * `global_state` is carried as a JSON object so unchanged keys pass through
//!   verbatim; an op overwrites only the keys it changes.
//! * Integer fields cross the boundary as decimal strings (exact, no JSON float).
//! * Crypto / external-oracle verification is **not** reimplemented: the request
//!   carries explicit integration facts (`operator_ok`, `sender_bound_ok`,
//!   `oracle_adapter_ok`, `oracle_authorization_ok`, `all_positions_flat`,
//!   `balance_available`) which Rust consumes as upstream assumptions.
//! * A reject never carries a post-state. Reject reasons are stable strings
//!   matching the Python authority.
//!
//! Coverage is incremental (foundation first): actions not yet materialized
//! return `op_not_materialized` so the bridge keeps Python authoritative for them.

use serde_json::{json, Map, Value};

use zenodex_runtime_core::perp_advance_epoch::{advance_epoch, AdvanceEpochInput};
use zenodex_runtime_core::perp_math::is_oracle_fresh;

pub const REJ_BAD_REQUEST: &str = "perp_isolated_op_bad_request";
pub const REJ_OPERATOR: &str = "operator only";
pub const REJ_NOT_MATERIALIZED: &str = "op_not_materialized";
pub const REJ_BAD_SCHEMA: &str = "perp_isolated_op_bad_schema";
pub const REJ_BAD_VERSION: &str = "perp_isolated_op_bad_version";
pub const REJ_MISSING_FACTS: &str = "perp_isolated_op_missing_facts";
pub const REJ_UNKNOWN_OP_FIELD: &str = "perp_isolated_op_unknown_op_field";

/// The authority-grade wire format requires this exact schema + version so the
/// request boundary cannot silently accept a mis-shaped or future payload.
const SCHEMA_ID: &str = "zenodex/perp_isolated_op/v1";
const SCHEMA_VERSION: i64 = 1;

#[derive(Clone, Debug)]
struct Account {
    key: String,
    position_base: i128,
    collateral_quote: i128,
    entry_price_e8: i128,
    funding_paid_cumulative: i128,
    funding_last_applied_epoch: i128,
    liquidated_this_step: bool,
}

struct Facts {
    operator_ok: bool,
    #[allow(dead_code)]
    sender_bound_ok: bool,
    #[allow(dead_code)]
    all_positions_flat: bool,
    #[allow(dead_code)]
    balance_available: i128,
    #[allow(dead_code)]
    oracle_adapter_ok: bool,
    #[allow(dead_code)]
    oracle_authorization_ok: bool,
}

/// Read an i128 from a JSON value that is a decimal string or an integer number.
fn as_i128(v: &Value) -> Result<i128, &'static str> {
    match v {
        Value::String(s) => s.parse::<i128>().map_err(|_| REJ_BAD_REQUEST),
        Value::Number(n) => n
            .as_i64()
            .map(i128::from)
            .ok_or(REJ_BAD_REQUEST)
            .or_else(|_| n.to_string().parse::<i128>().map_err(|_| REJ_BAD_REQUEST)),
        _ => Err(REJ_BAD_REQUEST),
    }
}

fn as_bool(v: &Value) -> Result<bool, &'static str> {
    match v {
        Value::Bool(b) => Ok(*b),
        Value::Number(n) => match n.as_i64() {
            Some(0) => Ok(false),
            Some(1) => Ok(true),
            _ => Err(REJ_BAD_REQUEST),
        },
        _ => Err(REJ_BAD_REQUEST),
    }
}

fn gget(g: &Map<String, Value>, key: &str) -> Result<i128, &'static str> {
    g.get(key).ok_or(REJ_BAD_REQUEST).and_then(as_i128)
}

/// Required fact: missing key is a bad request (NOT a semantic operator failure),
/// so a caller that forgets to populate `facts` fails closed at the boundary.
fn req_fact_bool(facts: &Map<String, Value>, key: &str) -> Result<bool, &'static str> {
    facts.get(key).ok_or(REJ_MISSING_FACTS).and_then(as_bool)
}

fn req_fact_i128(facts: &Map<String, Value>, key: &str) -> Result<i128, &'static str> {
    facts.get(key).ok_or(REJ_MISSING_FACTS).and_then(as_i128)
}

impl Facts {
    /// Parse all required integration facts. Every key is mandatory; a missing
    /// fact rejects as `REJ_MISSING_FACTS` rather than defaulting to false/zero.
    fn parse(facts: &Map<String, Value>) -> Result<Facts, &'static str> {
        Ok(Facts {
            operator_ok: req_fact_bool(facts, "operator_ok")?,
            sender_bound_ok: req_fact_bool(facts, "sender_bound_ok")?,
            all_positions_flat: req_fact_bool(facts, "all_positions_flat")?,
            balance_available: req_fact_i128(facts, "balance_available")?,
            oracle_adapter_ok: req_fact_bool(facts, "oracle_adapter_ok")?,
            oracle_authorization_ok: req_fact_bool(facts, "oracle_authorization_ok")?,
        })
    }
}

fn parse_account(v: &Value) -> Result<Account, &'static str> {
    let o = v.as_object().ok_or(REJ_BAD_REQUEST)?;
    Ok(Account {
        key: o
            .get("key")
            .and_then(Value::as_str)
            .ok_or(REJ_BAD_REQUEST)?
            .to_string(),
        position_base: gget(o, "position_base")?,
        collateral_quote: gget(o, "collateral_quote")?,
        entry_price_e8: gget(o, "entry_price_e8")?,
        funding_paid_cumulative: gget(o, "funding_paid_cumulative")?,
        funding_last_applied_epoch: gget(o, "funding_last_applied_epoch")?,
        liquidated_this_step: o
            .get("liquidated_this_step")
            .map(as_bool)
            .transpose()?
            .unwrap_or(false),
    })
}

fn account_to_json(a: &Account) -> Value {
    json!({
        "key": a.key,
        "position_base": a.position_base.to_string(),
        "collateral_quote": a.collateral_quote.to_string(),
        "entry_price_e8": a.entry_price_e8.to_string(),
        "funding_paid_cumulative": a.funding_paid_cumulative.to_string(),
        "funding_last_applied_epoch": a.funding_last_applied_epoch.to_string(),
        "liquidated_this_step": a.liquidated_this_step,
    })
}

fn reject(reason: &str) -> Value {
    json!({"accept": false, "reject_reason": reason})
}

fn accept(
    quote_asset: &str,
    global: &Map<String, Value>,
    accounts: &[Account],
    effects: Value,
) -> Value {
    json!({
        "accept": true,
        "post": {
            "quote_asset": quote_asset,
            "global_state": Value::Object(global.clone()),
            "accounts": accounts.iter().map(account_to_json).collect::<Vec<_>>(),
        },
        "effects": effects,
    })
}

/// Materialize one isolated-perps op. Returns the response JSON (accept + full
/// post-state, or reject + reason). Never panics on a well-typed request.
pub fn materialize_isolated_op(request: &Value) -> Value {
    let obj = match request.as_object() {
        Some(o) => o,
        None => return reject(REJ_BAD_REQUEST),
    };
    // Authority-grade wire format: pin the exact schema id and version.
    if obj.get("schema").and_then(Value::as_str) != Some(SCHEMA_ID) {
        return reject(REJ_BAD_SCHEMA);
    }
    if obj.get("version").and_then(Value::as_i64) != Some(SCHEMA_VERSION) {
        return reject(REJ_BAD_VERSION);
    }
    let quote_asset = match obj.get("quote_asset").and_then(Value::as_str) {
        Some(s) => s.to_string(),
        None => return reject(REJ_BAD_REQUEST),
    };
    let global = match obj.get("global_state").and_then(Value::as_object) {
        Some(g) => g.clone(),
        None => return reject(REJ_BAD_REQUEST),
    };
    let accounts_val = match obj.get("accounts").and_then(Value::as_array) {
        Some(a) => a,
        None => return reject(REJ_BAD_REQUEST),
    };
    let mut accounts = Vec::with_capacity(accounts_val.len());
    for av in accounts_val {
        match parse_account(av) {
            Ok(a) => accounts.push(a),
            Err(e) => return reject(e),
        }
    }
    let op = match obj.get("op").and_then(Value::as_object) {
        Some(o) => o,
        None => return reject(REJ_BAD_REQUEST),
    };
    let action = match op.get("action").and_then(Value::as_str) {
        Some(s) => s,
        None => return reject(REJ_BAD_REQUEST),
    };
    // The facts object is mandatory and every required fact key must be present.
    let facts_obj = match obj.get("facts").and_then(Value::as_object) {
        Some(f) => f,
        None => return reject(REJ_MISSING_FACTS),
    };
    let facts = match Facts::parse(facts_obj) {
        Ok(f) => f,
        Err(e) => return reject(e),
    };

    match action {
        "advance_epoch" => materialize_advance_epoch(&quote_asset, global, accounts, op, &facts),
        _ => reject(REJ_NOT_MATERIALIZED),
    }
}

/// `advance_epoch`: operator-gated global transition. The kernel checks
/// (oracle-settled gate, delta param-domain, `now+delta<=MAX_EPOCH`) are reused
/// from `perp_advance_epoch`; only `now_epoch` and `epoch_phase` change.
fn materialize_advance_epoch(
    quote_asset: &str,
    mut global: Map<String, Value>,
    accounts: Vec<Account>,
    op: &Map<String, Value>,
    facts: &Facts,
) -> Value {
    // Reject unknown op fields: `advance_epoch` takes only `action` and `delta`.
    for k in op.keys() {
        if k != "action" && k != "delta" {
            return reject(REJ_UNKNOWN_OP_FIELD);
        }
    }
    if !facts.operator_ok {
        return reject(REJ_OPERATOR);
    }
    let now_epoch = match gget(&global, "now_epoch") {
        Ok(v) => v,
        Err(e) => return reject(e),
    };
    let epoch_phase = match gget(&global, "epoch_phase") {
        Ok(v) => v,
        Err(e) => return reject(e),
    };
    let oracle_last = match gget(&global, "oracle_last_update_epoch") {
        Ok(v) => v,
        Err(e) => return reject(e),
    };
    let delta = match op.get("delta").map(as_i128) {
        Some(Ok(v)) => v,
        _ => return reject(REJ_BAD_REQUEST),
    };
    match advance_epoch(&AdvanceEpochInput {
        now_epoch,
        epoch_phase,
        oracle_last_update_epoch: oracle_last,
        delta,
    }) {
        Ok(out) => {
            global.insert("now_epoch".into(), Value::String(out.now_epoch.to_string()));
            global.insert(
                "epoch_phase".into(),
                Value::String(out.epoch_phase.to_string()),
            );
            match advance_effect(&global) {
                Ok(effects) => accept(quote_asset, &global, &accounts, effects),
                Err(code) => reject(code),
            }
        }
        Err(code) => reject(code),
    }
}

/// The exact `advance_epoch` kernel effect payload: the `EpochAdvanced` event plus
/// `_common_effects`, computed on the flat dummy account the Python integration
/// uses for global ops (so the account-derived fields are zero/true/false) and on
/// the *post* global (oracle freshness, margin params, fee/insurance after-values).
/// Int fields cross as decimal strings; the Python shadow emits the same fields and
/// the bridge compares them with int coercion.
fn advance_effect(global: &Map<String, Value>) -> Result<Value, &'static str> {
    let now = gget(global, "now_epoch")?;
    let oracle_last = gget(global, "oracle_last_update_epoch")?;
    let max_stale = gget(global, "max_oracle_staleness_epochs")?;
    let oracle_seen = global
        .get("oracle_seen")
        .ok_or(REJ_BAD_REQUEST)
        .and_then(as_bool)?;
    let maint = gget(global, "maintenance_margin_bps")?;
    let depeg = gget(global, "depeg_buffer_bps")?;
    let fee_pool = gget(global, "fee_pool_quote")?;
    let insurance = gget(global, "insurance_balance")?;
    let oracle_fresh = is_oracle_fresh(now, oracle_last, max_stale, oracle_seen);
    Ok(json!({
        "event": "EpochAdvanced",
        "oracle_fresh": oracle_fresh,
        "notional_quote": "0",
        "effective_maint_bps": (maint + depeg).to_string(),
        "maint_req_quote": "0",
        "init_req_quote": "0",
        "margin_ok": true,
        "liquidated": false,
        "collateral_after": "0",
        "fee_pool_after": fee_pool.to_string(),
        "insurance_after": insurance.to_string(),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn settled_global(now: i128) -> Value {
        json!({
            "now_epoch": now.to_string(), "epoch_phase": "2",
            "oracle_last_update_epoch": now.to_string(), "oracle_seen": true,
            "clearing_price_seen": true, "clearing_price_epoch": now.to_string(),
            "clearing_price_e8": "100000000", "index_price_e8": "100000000",
            "breaker_active": false, "breaker_last_trigger_epoch": "0",
            "max_oracle_staleness_epochs": "100", "max_oracle_move_bps": "500",
            "initial_margin_bps": "1000", "maintenance_margin_bps": "500",
            "depeg_buffer_bps": "100", "liquidation_penalty_bps": "50",
            "max_position_abs": "1000000", "fee_pool_quote": "0",
            "funding_rate_bps": "0", "funding_cap_bps": "1000",
            "insurance_balance": "0", "initial_insurance": "0",
            "fee_income": "0", "claims_paid": "0", "min_notional_for_bounty": "100000000"
        })
    }

    fn req(global: Value, op: Value, operator_ok: bool) -> Value {
        json!({
            "schema": SCHEMA_ID,
            "version": SCHEMA_VERSION,
            "quote_asset": "0x".to_string() + &"41".repeat(32),
            "global_state": global,
            "accounts": [],
            "op": op,
            "facts": {"operator_ok": operator_ok, "sender_bound_ok": true,
                      "all_positions_flat": true, "balance_available": "0",
                      "oracle_adapter_ok": true, "oracle_authorization_ok": true}
        })
    }

    #[test]
    fn advance_from_settled_materializes_full_post_state() {
        let r = materialize_isolated_op(&req(
            settled_global(5),
            json!({"action": "advance_epoch", "delta": "1"}),
            true,
        ));
        assert_eq!(r["accept"], json!(true));
        let pg = &r["post"]["global_state"];
        assert_eq!(pg["now_epoch"], json!("6"));
        assert_eq!(pg["epoch_phase"], json!("0"));
        assert_eq!(pg["max_position_abs"], json!("1000000"));
        assert_eq!(pg["index_price_e8"], json!("100000000"));
        assert!(r["post"]["accounts"].as_array().unwrap().is_empty());
        // Exact kernel effect payload (EpochAdvanced + _common_effects on the
        // flat dummy / post-global), matching the Python integration.
        let fx = &r["effects"];
        assert_eq!(fx["event"], json!("EpochAdvanced"));
        assert_eq!(fx["oracle_fresh"], json!(true));
        assert_eq!(fx["effective_maint_bps"], json!("600"));
        assert_eq!(fx["notional_quote"], json!("0"));
        assert_eq!(fx["maint_req_quote"], json!("0"));
        assert_eq!(fx["init_req_quote"], json!("0"));
        assert_eq!(fx["margin_ok"], json!(true));
        assert_eq!(fx["liquidated"], json!(false));
        assert_eq!(fx["collateral_after"], json!("0"));
        assert_eq!(fx["fee_pool_after"], json!("0"));
        assert_eq!(fx["insurance_after"], json!("0"));
    }

    #[test]
    fn bad_schema_rejects() {
        let mut r = req(
            settled_global(5),
            json!({"action": "advance_epoch", "delta": "1"}),
            true,
        );
        r["schema"] = json!("zenodex/perp_isolated_op/v2");
        let out = materialize_isolated_op(&r);
        assert_eq!(out["accept"], json!(false));
        assert_eq!(out["reject_reason"], json!(REJ_BAD_SCHEMA));
        assert!(out.get("post").is_none());
    }

    #[test]
    fn bad_version_rejects() {
        let mut r = req(
            settled_global(5),
            json!({"action": "advance_epoch", "delta": "1"}),
            true,
        );
        r["version"] = json!(2);
        assert_eq!(
            materialize_isolated_op(&r)["reject_reason"],
            json!(REJ_BAD_VERSION)
        );
    }

    #[test]
    fn missing_facts_rejects_as_bad_request_not_operator() {
        let mut r = req(
            settled_global(5),
            json!({"action": "advance_epoch", "delta": "1"}),
            true,
        );
        r.as_object_mut().unwrap().remove("facts");
        let out = materialize_isolated_op(&r);
        assert_eq!(out["reject_reason"], json!(REJ_MISSING_FACTS));
        // Critically NOT the semantic operator failure.
        assert_ne!(out["reject_reason"], json!(REJ_OPERATOR));
    }

    #[test]
    fn missing_required_fact_key_rejects() {
        let mut r = req(
            settled_global(5),
            json!({"action": "advance_epoch", "delta": "1"}),
            true,
        );
        r["facts"]
            .as_object_mut()
            .unwrap()
            .remove("oracle_adapter_ok");
        assert_eq!(
            materialize_isolated_op(&r)["reject_reason"],
            json!(REJ_MISSING_FACTS)
        );
    }

    #[test]
    fn unknown_op_field_rejects() {
        let r = req(
            settled_global(5),
            json!({"action": "advance_epoch", "delta": "1", "price_e8": "100000000"}),
            true,
        );
        let out = materialize_isolated_op(&r);
        assert_eq!(out["reject_reason"], json!(REJ_UNKNOWN_OP_FIELD));
        assert!(out.get("post").is_none());
    }

    #[test]
    fn advance_operator_gate_rejects() {
        let r = materialize_isolated_op(&req(
            settled_global(5),
            json!({"action": "advance_epoch", "delta": "1"}),
            false,
        ));
        assert_eq!(r["accept"], json!(false));
        assert_eq!(r["reject_reason"], json!(REJ_OPERATOR));
        assert!(
            r.get("post").is_none(),
            "reject must not carry a post-state"
        );
    }

    #[test]
    fn advance_unsettled_rejects_with_kernel_reason() {
        let g = json!({
            "now_epoch": "5", "epoch_phase": "0", "oracle_last_update_epoch": "4",
            "oracle_seen": true, "clearing_price_seen": false, "clearing_price_epoch": "0",
            "clearing_price_e8": "0", "index_price_e8": "100000000", "breaker_active": false,
            "breaker_last_trigger_epoch": "0", "max_oracle_staleness_epochs": "100",
            "max_oracle_move_bps": "500", "initial_margin_bps": "1000",
            "maintenance_margin_bps": "500", "depeg_buffer_bps": "100",
            "liquidation_penalty_bps": "50", "max_position_abs": "1000000",
            "fee_pool_quote": "0", "funding_rate_bps": "0", "funding_cap_bps": "1000",
            "insurance_balance": "0", "initial_insurance": "0", "fee_income": "0",
            "claims_paid": "0", "min_notional_for_bounty": "100000000"
        });
        let r = materialize_isolated_op(&req(
            g,
            json!({"action": "advance_epoch", "delta": "1"}),
            true,
        ));
        assert_eq!(r["accept"], json!(false));
        assert_eq!(r["reject_reason"], json!("epoch_not_settled"));
    }

    #[test]
    fn unmaterialized_action_signals_not_materialized() {
        let r = materialize_isolated_op(&req(
            settled_global(5),
            json!({"action": "settle_epoch"}),
            true,
        ));
        assert_eq!(r["reject_reason"], json!(REJ_NOT_MATERIALIZED));
    }

    #[test]
    fn non_object_request_rejects() {
        assert_eq!(
            materialize_isolated_op(&json!(42))["reject_reason"],
            json!(REJ_BAD_REQUEST)
        );
    }

    #[test]
    fn malformed_after_schema_rejects() {
        // Valid schema/version but missing quote_asset -> bad request (not schema).
        let r = json!({"schema": SCHEMA_ID, "version": SCHEMA_VERSION, "bad": 1});
        assert_eq!(
            materialize_isolated_op(&r)["reject_reason"],
            json!(REJ_BAD_REQUEST)
        );
    }
}
