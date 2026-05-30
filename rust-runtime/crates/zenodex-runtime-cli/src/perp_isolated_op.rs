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

use zenodex_runtime_core::perp_account_ops::{account_op, AccountOpInput};
use zenodex_runtime_core::perp_advance_epoch::{advance_epoch, AdvanceEpochInput};
use zenodex_runtime_core::perp_math::{
    init_margin_req, is_oracle_fresh, maint_margin_req, notional_quote,
};
use zenodex_runtime_core::perp_publish_clearing_price::{
    publish_clearing_price, PublishClearingPriceInput,
};
use zenodex_runtime_core::perp_settle_epoch::{settle_epoch, SettleAccount, SettleEpochInput};

pub const REJ_BAD_REQUEST: &str = "perp_isolated_op_bad_request";
pub const REJ_OPERATOR: &str = "operator only";
pub const REJ_NOT_MATERIALIZED: &str = "op_not_materialized";
pub const REJ_BAD_SCHEMA: &str = "perp_isolated_op_bad_schema";
pub const REJ_BAD_VERSION: &str = "perp_isolated_op_bad_version";
pub const REJ_MISSING_FACTS: &str = "perp_isolated_op_missing_facts";
pub const REJ_UNKNOWN_OP_FIELD: &str = "perp_isolated_op_unknown_op_field";
pub const REJ_ARITHMETIC_OVERFLOW: &str = "perp_isolated_op_arithmetic_overflow";
pub const REJ_SENDER_NOT_BOUND: &str = "sender_not_bound_to_account";

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
    sender_bound_ok: bool,
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

fn bget(g: &Map<String, Value>, key: &str) -> Result<bool, &'static str> {
    g.get(key).ok_or(REJ_BAD_REQUEST).and_then(as_bool)
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
        "publish_clearing_price" => {
            materialize_publish_clearing_price(&quote_asset, global, accounts, op, &facts)
        }
        "settle_epoch" => materialize_settle_epoch(&quote_asset, global, accounts, op, &facts),
        "deposit_collateral" => {
            materialize_deposit_collateral(&quote_asset, global, accounts, op, &facts)
        }
        "withdraw_collateral" => {
            materialize_withdraw_collateral(&quote_asset, global, accounts, op, &facts)
        }
        "set_position" => materialize_set_position(&quote_asset, global, accounts, op, &facts),
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
            match global_op_effect(&global, "EpochAdvanced") {
                Ok(effects) => accept(quote_asset, &global, &accounts, effects),
                Err(code) => reject(code),
            }
        }
        Err(code) => reject(code),
    }
}

/// `publish_clearing_price`: operator-gated global transition. The kernel checks
/// (input domain, state-consistency, price sign/positivity/domain, and the
/// `Open` + `clearing_price_epoch < now` guard) are reused from
/// `perp_publish_clearing_price`; only the clearing-price fields and `epoch_phase`
/// change (`now_epoch` is unchanged).
fn materialize_publish_clearing_price(
    quote_asset: &str,
    mut global: Map<String, Value>,
    accounts: Vec<Account>,
    op: &Map<String, Value>,
    facts: &Facts,
) -> Value {
    // Reject unknown op fields: publish takes only `action` and `price_e8`.
    for k in op.keys() {
        if k != "action" && k != "price_e8" {
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
    let clearing_price_seen = match global
        .get("clearing_price_seen")
        .ok_or(REJ_BAD_REQUEST)
        .and_then(as_bool)
    {
        Ok(v) => v,
        Err(e) => return reject(e),
    };
    let clearing_price_epoch = match gget(&global, "clearing_price_epoch") {
        Ok(v) => v,
        Err(e) => return reject(e),
    };
    let clearing_price_e8 = match gget(&global, "clearing_price_e8") {
        Ok(v) => v,
        Err(e) => return reject(e),
    };
    let oracle_last = match gget(&global, "oracle_last_update_epoch") {
        Ok(v) => v,
        Err(e) => return reject(e),
    };
    let price_e8 = match op.get("price_e8").map(as_i128) {
        Some(Ok(v)) => v,
        _ => return reject(REJ_BAD_REQUEST),
    };
    match publish_clearing_price(&PublishClearingPriceInput {
        now_epoch,
        epoch_phase,
        clearing_price_seen,
        clearing_price_epoch,
        clearing_price_e8,
        oracle_last_update_epoch: oracle_last,
        price_e8,
    }) {
        Ok(out) => {
            global.insert(
                "epoch_phase".into(),
                Value::String(out.epoch_phase.to_string()),
            );
            global.insert(
                "clearing_price_seen".into(),
                Value::Bool(out.clearing_price_seen),
            );
            global.insert(
                "clearing_price_epoch".into(),
                Value::String(out.clearing_price_epoch.to_string()),
            );
            global.insert(
                "clearing_price_e8".into(),
                Value::String(out.clearing_price_e8.to_string()),
            );
            match global_op_effect(&global, "ClearingPricePublished") {
                Ok(effects) => accept(quote_asset, &global, &accounts, effects),
                Err(code) => reject(code),
            }
        }
        Err(code) => reject(code),
    }
}

/// `settle_epoch`: operator-gated whole-market settle. Reuses
/// `perp_settle_epoch::settle_epoch` (input domain, the `PricePublished` guard,
/// per-account P&L / liquidation, penalty accumulation into fee/insurance, and the
/// account-independent global post-epoch update). This is the first account-mutating
/// materialized op: it emits the full settled post-state (the global keys settle
/// changes + every settled account) and the `EpochSettled` effect. Oracle
/// authorization is a Python-verified fact, never re-derived here.
fn materialize_settle_epoch(
    quote_asset: &str,
    global: Map<String, Value>,
    accounts: Vec<Account>,
    op: &Map<String, Value>,
    facts: &Facts,
) -> Value {
    // settle takes no materialized op params (oracle-authorization payloads are
    // consumed Python-side as facts, not forwarded into the Rust request).
    for k in op.keys() {
        if k != "action" {
            return reject(REJ_UNKNOWN_OP_FIELD);
        }
    }
    if !facts.operator_ok {
        return reject(REJ_OPERATOR);
    }
    match settled_market(quote_asset, global, accounts) {
        Ok(v) => v,
        Err(e) => reject(e),
    }
}

/// The settle transition body (uses `?`): build the core input from the global +
/// accounts, run the whole-market settle, then overwrite the global keys settle
/// changes and rebuild accounts (preserving the funding fields settle never touches).
fn settled_market(
    quote_asset: &str,
    mut global: Map<String, Value>,
    accounts: Vec<Account>,
) -> Result<Value, &'static str> {
    // Read the three bool globals up front so no immutable borrow outlives the
    // later mutable inserts.
    let clearing_price_seen = global
        .get("clearing_price_seen")
        .ok_or(REJ_BAD_REQUEST)
        .and_then(as_bool)?;
    let oracle_seen = global
        .get("oracle_seen")
        .ok_or(REJ_BAD_REQUEST)
        .and_then(as_bool)?;
    let breaker_active = global
        .get("breaker_active")
        .ok_or(REJ_BAD_REQUEST)
        .and_then(as_bool)?;
    let input = SettleEpochInput {
        now_epoch: gget(&global, "now_epoch")?,
        epoch_phase: gget(&global, "epoch_phase")?,
        clearing_price_seen,
        clearing_price_epoch: gget(&global, "clearing_price_epoch")?,
        clearing_price_e8: gget(&global, "clearing_price_e8")?,
        oracle_last_update_epoch: gget(&global, "oracle_last_update_epoch")?,
        oracle_seen,
        index_price_e8: gget(&global, "index_price_e8")?,
        max_oracle_move_bps: gget(&global, "max_oracle_move_bps")?,
        maintenance_margin_bps: gget(&global, "maintenance_margin_bps")?,
        depeg_buffer_bps: gget(&global, "depeg_buffer_bps")?,
        liquidation_penalty_bps: gget(&global, "liquidation_penalty_bps")?,
        min_notional_for_bounty: gget(&global, "min_notional_for_bounty")?,
        fee_pool_quote: gget(&global, "fee_pool_quote")?,
        fee_income: gget(&global, "fee_income")?,
        initial_insurance: gget(&global, "initial_insurance")?,
        claims_paid: gget(&global, "claims_paid")?,
        breaker_active,
        breaker_last_trigger_epoch: gget(&global, "breaker_last_trigger_epoch")?,
        accounts: accounts
            .iter()
            .map(|a| SettleAccount {
                key: a.key.clone(),
                position_base: a.position_base,
                collateral_quote: a.collateral_quote,
                entry_price_e8: a.entry_price_e8,
                liquidated_this_step: a.liquidated_this_step,
            })
            .collect(),
    };
    let out = settle_epoch(&input)?;
    // Build the Python kernel effect before applying the accumulated liquidation
    // penalties. The Python integration records `res0.effects` from the flat
    // dummy settle; the outer integration effect carries `fee_pool_delta`
    // separately. Shadow parity must mirror that existing receipt shape exactly.
    let mut effect_global = global.clone();
    effect_global.insert(
        "epoch_phase".into(),
        Value::String(out.epoch_phase.to_string()),
    );
    effect_global.insert(
        "oracle_last_update_epoch".into(),
        Value::String(out.oracle_last_update_epoch.to_string()),
    );
    effect_global.insert("oracle_seen".into(), Value::Bool(out.oracle_seen));
    effect_global.insert(
        "index_price_e8".into(),
        Value::String(out.index_price_e8.to_string()),
    );
    effect_global.insert("breaker_active".into(), Value::Bool(out.breaker_active));
    effect_global.insert(
        "breaker_last_trigger_epoch".into(),
        Value::String(out.breaker_last_trigger_epoch.to_string()),
    );
    let no_penalty_insurance = input
        .initial_insurance
        .checked_add(input.fee_income)
        .and_then(|v| v.checked_sub(input.claims_paid))
        .ok_or(REJ_ARITHMETIC_OVERFLOW)?;
    effect_global.insert(
        "insurance_balance".into(),
        Value::String(no_penalty_insurance.to_string()),
    );
    let effects = global_op_effect(&effect_global, "EpochSettled")?;

    // Overwrite exactly the global keys settle changes (others carry through).
    global.insert(
        "epoch_phase".into(),
        Value::String(out.epoch_phase.to_string()),
    );
    global.insert(
        "oracle_last_update_epoch".into(),
        Value::String(out.oracle_last_update_epoch.to_string()),
    );
    global.insert("oracle_seen".into(), Value::Bool(out.oracle_seen));
    global.insert(
        "index_price_e8".into(),
        Value::String(out.index_price_e8.to_string()),
    );
    global.insert("breaker_active".into(), Value::Bool(out.breaker_active));
    global.insert(
        "breaker_last_trigger_epoch".into(),
        Value::String(out.breaker_last_trigger_epoch.to_string()),
    );
    global.insert(
        "fee_pool_quote".into(),
        Value::String(out.fee_pool_quote.to_string()),
    );
    global.insert(
        "fee_income".into(),
        Value::String(out.fee_income.to_string()),
    );
    global.insert(
        "insurance_balance".into(),
        Value::String(out.insurance_balance.to_string()),
    );
    // Rebuild full accounts: settle gives 5 fields; keep the two funding fields
    // (funding_paid_cumulative, funding_last_applied_epoch) from the pre-account.
    let mut post_accounts: Vec<Account> = Vec::with_capacity(out.accounts.len());
    for sa in &out.accounts {
        let pre = accounts
            .iter()
            .find(|a| a.key == sa.key)
            .ok_or(REJ_BAD_REQUEST)?;
        post_accounts.push(Account {
            key: sa.key.clone(),
            position_base: sa.position_base,
            collateral_quote: sa.collateral_quote,
            entry_price_e8: sa.entry_price_e8,
            funding_paid_cumulative: pre.funding_paid_cumulative,
            funding_last_applied_epoch: pre.funding_last_applied_epoch,
            liquidated_this_step: sa.liquidated_this_step,
        });
    }
    Ok(accept(quote_asset, &global, &post_accounts, effects))
}

/// The exact kernel effect payload for a **global** op (one that runs on the flat
/// dummy account the Python integration uses): `event` (`EpochAdvanced` for
/// `advance_epoch`, `ClearingPricePublished` for `publish_clearing_price`) plus
/// `_common_effects`. Account-derived fields are zero/true/false (flat dummy); the
/// rest come from the *post* global (oracle freshness, margin params, fee/insurance
/// after-values). Int fields cross as decimal strings; the Python shadow emits the
/// same fields and the bridge compares them with int coercion.
fn global_op_effect(global: &Map<String, Value>, event: &str) -> Result<Value, &'static str> {
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
    // Checked: margin bps are carried verbatim and are not bounded by the op gate,
    // so a degenerate global must reject (fail-closed), never panic/wrap.
    let effective_maint_bps = maint.checked_add(depeg).ok_or(REJ_ARITHMETIC_OVERFLOW)?;
    let oracle_fresh = is_oracle_fresh(now, oracle_last, max_stale, oracle_seen);
    Ok(json!({
        "event": event,
        "oracle_fresh": oracle_fresh,
        "notional_quote": "0",
        "effective_maint_bps": effective_maint_bps.to_string(),
        "maint_req_quote": "0",
        "init_req_quote": "0",
        "margin_ok": true,
        "liquidated": false,
        "collateral_after": "0",
        "fee_pool_after": fee_pool.to_string(),
        "insurance_after": insurance.to_string(),
    }))
}

/// The exact kernel effect for an op whose `_common_effects` is computed on a
/// specific account (the `account_op` ops). Unlike `global_op_effect` (flat dummy),
/// the margin/notional/`collateral_after` fields reflect the affected account; the
/// oracle-freshness and fee/insurance after-values come from the post-global.
fn account_effect(
    global: &Map<String, Value>,
    account: &Account,
    event: &str,
) -> Result<Value, &'static str> {
    let now = gget(global, "now_epoch")?;
    let oracle_last = gget(global, "oracle_last_update_epoch")?;
    let max_stale = gget(global, "max_oracle_staleness_epochs")?;
    let oracle_seen = bget(global, "oracle_seen")?;
    let index_price = gget(global, "index_price_e8")?;
    let maint = gget(global, "maintenance_margin_bps")?;
    let depeg = gget(global, "depeg_buffer_bps")?;
    let init = gget(global, "initial_margin_bps")?;
    let fee_pool = gget(global, "fee_pool_quote")?;
    let insurance = gget(global, "insurance_balance")?;
    let effective_maint_bps = maint.checked_add(depeg).ok_or(REJ_ARITHMETIC_OVERFLOW)?;
    let pos = account.position_base;
    let coll = account.collateral_quote;
    let maint_req = maint_margin_req(pos, index_price, maint, depeg);
    let margin_ok = pos == 0 || coll >= maint_req;
    let oracle_fresh = is_oracle_fresh(now, oracle_last, max_stale, oracle_seen);
    Ok(json!({
        "event": event,
        "oracle_fresh": oracle_fresh,
        "notional_quote": notional_quote(pos, index_price).to_string(),
        "effective_maint_bps": effective_maint_bps.to_string(),
        "maint_req_quote": maint_req.to_string(),
        "init_req_quote": init_margin_req(pos, index_price, init).to_string(),
        "margin_ok": margin_ok,
        "liquidated": account.liquidated_this_step,
        "collateral_after": coll.to_string(),
        "fee_pool_after": fee_pool.to_string(),
        "insurance_after": insurance.to_string(),
    }))
}

/// Shared body for the `account_op`-based single-account ops (deposit / withdraw /
/// set_position). Find-or-create the target account (a missing pubkey is a flat
/// new account, mirroring `_kernel_initial_account_state()` on first deposit), run
/// the core op, write the account back (preserving the funding fields the op never
/// touches) and any global breaker flip, then emit the account effect.
#[allow(clippy::too_many_arguments)]
fn materialize_account_op(
    quote_asset: &str,
    mut global: Map<String, Value>,
    mut accounts: Vec<Account>,
    account_pubkey: &str,
    amount: i128,
    new_position_base: i128,
    all_positions_flat: bool,
    op_str: &str,
    event: &str,
) -> Result<Value, &'static str> {
    let idx = accounts.iter().position(|a| a.key == account_pubkey);
    let pre = match idx {
        Some(i) => accounts[i].clone(),
        None => Account {
            key: account_pubkey.to_string(),
            position_base: 0,
            collateral_quote: 0,
            entry_price_e8: 0,
            funding_paid_cumulative: 0,
            funding_last_applied_epoch: 0,
            liquidated_this_step: false,
        },
    };
    let input = AccountOpInput {
        now_epoch: gget(&global, "now_epoch")?,
        epoch_phase: gget(&global, "epoch_phase")?,
        oracle_last_update_epoch: gget(&global, "oracle_last_update_epoch")?,
        max_oracle_staleness_epochs: gget(&global, "max_oracle_staleness_epochs")?,
        oracle_seen: bget(&global, "oracle_seen")?,
        index_price_e8: gget(&global, "index_price_e8")?,
        position_base: pre.position_base,
        collateral_quote: pre.collateral_quote,
        entry_price_e8: pre.entry_price_e8,
        maintenance_margin_bps: gget(&global, "maintenance_margin_bps")?,
        depeg_buffer_bps: gget(&global, "depeg_buffer_bps")?,
        initial_margin_bps: gget(&global, "initial_margin_bps")?,
        max_position_abs: gget(&global, "max_position_abs")?,
        breaker_active: bget(&global, "breaker_active")?,
        breaker_last_trigger_epoch: gget(&global, "breaker_last_trigger_epoch")?,
        amount,
        new_position_base,
        all_positions_flat,
    };
    let out = account_op(op_str, &input)?;
    let post = Account {
        key: account_pubkey.to_string(),
        position_base: out.position_base,
        collateral_quote: out.collateral_quote,
        entry_price_e8: out.entry_price_e8,
        funding_paid_cumulative: pre.funding_paid_cumulative,
        funding_last_applied_epoch: pre.funding_last_applied_epoch,
        // Every account_op kernel update (deposit/withdraw/set_position/clear_breaker)
        // unconditionally resets liquidated_this_step to false (see
        // perp_v2/updates.py). A liquidation flag set in a prior settle persists
        // through advance_epoch (which copies real accounts verbatim), so carrying
        // pre.liquidated_this_step here would diverge from Python and false-reject.
        liquidated_this_step: false,
    };
    match idx {
        Some(i) => accounts[i] = post.clone(),
        None => accounts.push(post.clone()),
    }
    // Account ops may flip the global breaker (the output carries both fields).
    global.insert("breaker_active".into(), Value::Bool(out.breaker_active));
    global.insert(
        "breaker_last_trigger_epoch".into(),
        Value::String(out.breaker_last_trigger_epoch.to_string()),
    );
    let effects = account_effect(&global, &post, event)?;
    Ok(accept(quote_asset, &global, &accounts, effects))
}

/// `deposit_collateral`: sender-gated single-account op (the sender owns the
/// account). Reuses `perp_account_ops::account_op`; the wallet-balance check is a
/// Python-verified fact, never re-derived here.
fn materialize_deposit_collateral(
    quote_asset: &str,
    global: Map<String, Value>,
    accounts: Vec<Account>,
    op: &Map<String, Value>,
    facts: &Facts,
) -> Value {
    for k in op.keys() {
        if k != "action" && k != "account_pubkey" && k != "amount" {
            return reject(REJ_UNKNOWN_OP_FIELD);
        }
    }
    if !facts.sender_bound_ok {
        return reject(REJ_SENDER_NOT_BOUND);
    }
    let account_pubkey = match op.get("account_pubkey").and_then(Value::as_str) {
        Some(s) => s,
        None => return reject(REJ_BAD_REQUEST),
    };
    let amount = match op.get("amount").map(as_i128) {
        Some(Ok(v)) => v,
        _ => return reject(REJ_BAD_REQUEST),
    };
    match materialize_account_op(
        quote_asset,
        global,
        accounts,
        account_pubkey,
        amount,
        0,
        facts.all_positions_flat,
        "deposit_collateral",
        "CollateralDeposited",
    ) {
        Ok(v) => v,
        Err(e) => reject(e),
    }
}

/// `withdraw_collateral`: sender-gated single-account op. Same shape as deposit
/// (op fields {action, account_pubkey, amount}); the core `withdraw_collateral`
/// rejects an over-withdraw OR a post-state that breaches maintenance margin —
/// both fold into the single `withdraw_collateral_guard` reason (REJ_MAINT_MARGIN
/// is `set_position`-only, not emitted here).
fn materialize_withdraw_collateral(
    quote_asset: &str,
    global: Map<String, Value>,
    accounts: Vec<Account>,
    op: &Map<String, Value>,
    facts: &Facts,
) -> Value {
    for k in op.keys() {
        if k != "action" && k != "account_pubkey" && k != "amount" {
            return reject(REJ_UNKNOWN_OP_FIELD);
        }
    }
    if !facts.sender_bound_ok {
        return reject(REJ_SENDER_NOT_BOUND);
    }
    let account_pubkey = match op.get("account_pubkey").and_then(Value::as_str) {
        Some(s) => s,
        None => return reject(REJ_BAD_REQUEST),
    };
    let amount = match op.get("amount").map(as_i128) {
        Some(Ok(v)) => v,
        _ => return reject(REJ_BAD_REQUEST),
    };
    match materialize_account_op(
        quote_asset,
        global,
        accounts,
        account_pubkey,
        amount,
        0,
        facts.all_positions_flat,
        "withdraw_collateral",
        "CollateralWithdrawn",
    ) {
        Ok(v) => v,
        Err(e) => reject(e),
    }
}

/// `set_position`: sender-gated single-account op. Op fields
/// {action, account_pubkey, new_position_base}; `new_position_base` is SIGNED
/// (a short is negative). The core `set_position` sets `position_base` to the
/// requested value and `entry_price_e8` to the index (or 0 when flat), rejecting
/// with `param_domain_new_position_base` (out of param range),
/// `set_position_guard` (phase/oracle/max-position/initial-margin, or the
/// breaker reduce-only rules), or `invariant_maint_margin` (a breaker reduce-only
/// that still leaves the remaining position below maintenance — the only
/// account_op that emits REJ_MAINT_MARGIN).
fn materialize_set_position(
    quote_asset: &str,
    global: Map<String, Value>,
    accounts: Vec<Account>,
    op: &Map<String, Value>,
    facts: &Facts,
) -> Value {
    for k in op.keys() {
        if k != "action" && k != "account_pubkey" && k != "new_position_base" {
            return reject(REJ_UNKNOWN_OP_FIELD);
        }
    }
    if !facts.sender_bound_ok {
        return reject(REJ_SENDER_NOT_BOUND);
    }
    let account_pubkey = match op.get("account_pubkey").and_then(Value::as_str) {
        Some(s) => s,
        None => return reject(REJ_BAD_REQUEST),
    };
    let new_position_base = match op.get("new_position_base").map(as_i128) {
        Some(Ok(v)) => v,
        _ => return reject(REJ_BAD_REQUEST),
    };
    match materialize_account_op(
        quote_asset,
        global,
        accounts,
        account_pubkey,
        0,
        new_position_base,
        facts.all_positions_flat,
        "set_position",
        "PositionSet",
    ) {
        Ok(v) => v,
        Err(e) => reject(e),
    }
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

    fn open_global(now: i128) -> Value {
        // A consistent Open state: clearing price unseen, oracle stale (oracle != now).
        json!({
            "now_epoch": now.to_string(), "epoch_phase": "0",
            "oracle_last_update_epoch": (now - 1).to_string(), "oracle_seen": true,
            "clearing_price_seen": false, "clearing_price_epoch": "0",
            "clearing_price_e8": "0", "index_price_e8": "100000000",
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

    fn price_published_global(now: i128) -> Value {
        // Consistent PricePublished at `now`: clearing seen this epoch, oracle stale.
        json!({
            "now_epoch": now.to_string(), "epoch_phase": "1",
            "oracle_last_update_epoch": (now - 1).to_string(), "oracle_seen": true,
            "clearing_price_seen": true, "clearing_price_epoch": now.to_string(),
            "clearing_price_e8": "101000000", "index_price_e8": "100000000",
            "breaker_active": false, "breaker_last_trigger_epoch": "0",
            "max_oracle_staleness_epochs": "100", "max_oracle_move_bps": "500",
            "initial_margin_bps": "1000", "maintenance_margin_bps": "500",
            "depeg_buffer_bps": "100", "liquidation_penalty_bps": "200",
            "max_position_abs": "1000000", "fee_pool_quote": "0",
            "funding_rate_bps": "0", "funding_cap_bps": "1000",
            "insurance_balance": "0", "initial_insurance": "0",
            "fee_income": "0", "claims_paid": "0", "min_notional_for_bounty": "0"
        })
    }

    fn acct_json(key: &str, pos: i128, coll: i128, entry: i128) -> Value {
        json!({
            "key": key, "position_base": pos.to_string(),
            "collateral_quote": coll.to_string(), "entry_price_e8": entry.to_string(),
            "funding_paid_cumulative": "7", "funding_last_applied_epoch": "2",
            "liquidated_this_step": false
        })
    }

    fn req_accts(global: Value, op: Value, accounts: Value, operator_ok: bool) -> Value {
        json!({
            "schema": SCHEMA_ID, "version": SCHEMA_VERSION,
            "quote_asset": "0x".to_string() + &"41".repeat(32),
            "global_state": global, "accounts": accounts, "op": op,
            "facts": {"operator_ok": operator_ok, "sender_bound_ok": true,
                      "all_positions_flat": false, "balance_available": "0",
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
    fn effect_arithmetic_overflow_rejects_without_panic() {
        // maintenance_margin_bps + depeg_buffer_bps must not panic (debug) or wrap
        // (release) on a degenerate global; it fails closed instead.
        let mut g = settled_global(5);
        g["maintenance_margin_bps"] = json!(i128::MAX.to_string());
        g["depeg_buffer_bps"] = json!("1");
        let out = materialize_isolated_op(&req(
            g,
            json!({"action": "advance_epoch", "delta": "1"}),
            true,
        ));
        assert_eq!(out["accept"], json!(false));
        assert_eq!(out["reject_reason"], json!(REJ_ARITHMETIC_OVERFLOW));
        assert!(out.get("post").is_none());
    }

    #[test]
    fn publish_from_open_materializes_full_post_state() {
        let r = materialize_isolated_op(&req(
            open_global(5),
            json!({"action": "publish_clearing_price", "price_e8": "101000000"}),
            true,
        ));
        assert_eq!(r["accept"], json!(true));
        let pg = &r["post"]["global_state"];
        // Changed by publish: phase Open->PricePublished, clearing-price fields set.
        assert_eq!(pg["epoch_phase"], json!("1"));
        assert_eq!(pg["clearing_price_seen"], json!(true));
        assert_eq!(pg["clearing_price_epoch"], json!("5"));
        assert_eq!(pg["clearing_price_e8"], json!("101000000"));
        // Carried verbatim: now_epoch and unrelated keys are unchanged.
        assert_eq!(pg["now_epoch"], json!("5"));
        assert_eq!(pg["index_price_e8"], json!("100000000"));
        assert_eq!(pg["max_position_abs"], json!("1000000"));
        // Exact effect payload (ClearingPricePublished + _common_effects, flat dummy).
        let fx = &r["effects"];
        assert_eq!(fx["event"], json!("ClearingPricePublished"));
        assert_eq!(fx["oracle_fresh"], json!(true));
        assert_eq!(fx["effective_maint_bps"], json!("600"));
        assert_eq!(fx["notional_quote"], json!("0"));
        assert_eq!(fx["margin_ok"], json!(true));
        assert_eq!(fx["fee_pool_after"], json!("0"));
        assert_eq!(fx["insurance_after"], json!("0"));
    }

    #[test]
    fn publish_operator_gate_rejects() {
        let r = materialize_isolated_op(&req(
            open_global(5),
            json!({"action": "publish_clearing_price", "price_e8": "101000000"}),
            false,
        ));
        assert_eq!(r["reject_reason"], json!(REJ_OPERATOR));
        assert!(r.get("post").is_none());
    }

    #[test]
    fn publish_unknown_op_field_rejects() {
        let r = materialize_isolated_op(&req(
            open_global(5),
            json!({"action": "publish_clearing_price", "price_e8": "101000000", "delta": "1"}),
            true,
        ));
        assert_eq!(r["reject_reason"], json!(REJ_UNKNOWN_OP_FIELD));
    }

    #[test]
    fn publish_wrong_phase_rejects_with_kernel_reason() {
        // settled_global is phase Settled; publish needs Open -> kernel guard rejects.
        let r = materialize_isolated_op(&req(
            settled_global(5),
            json!({"action": "publish_clearing_price", "price_e8": "101000000"}),
            true,
        ));
        assert_eq!(r["accept"], json!(false));
        assert_eq!(
            r["reject_reason"],
            json!(zenodex_runtime_core::perp_publish_clearing_price::REJ_GUARD)
        );
        assert!(r.get("post").is_none());
    }

    #[test]
    fn publish_negative_price_rejects_with_kernel_reason() {
        let r = materialize_isolated_op(&req(
            open_global(5),
            json!({"action": "publish_clearing_price", "price_e8": "-1"}),
            true,
        ));
        assert_eq!(
            r["reject_reason"],
            json!(zenodex_runtime_core::perp_publish_clearing_price::REJ_PRICE_NEGATIVE)
        );
    }

    #[test]
    fn settle_two_accounts_materializes_pnl_global_and_effect() {
        let accounts = json!([
            acct_json("aa", 300_000, 1_000_000, 100_000_000),
            acct_json("bb", -300_000, 1_000_000, 100_000_000),
        ]);
        let r = materialize_isolated_op(&req_accts(
            price_published_global(5),
            json!({"action": "settle_epoch"}),
            accounts,
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let pg = &r["post"]["global_state"];
        assert_eq!(pg["epoch_phase"], json!("2"));
        assert_eq!(pg["oracle_last_update_epoch"], json!("5"));
        assert_eq!(pg["oracle_seen"], json!(true));
        assert_eq!(pg["index_price_e8"], json!("101000000")); // settle price
        assert_eq!(pg["fee_pool_quote"], json!("0")); // no liquidation penalty
        assert_eq!(pg["insurance_balance"], json!("0"));
        assert_eq!(pg["now_epoch"], json!("5")); // unchanged
        let accts = r["post"]["accounts"].as_array().unwrap();
        let a = accts.iter().find(|x| x["key"] == "aa").unwrap();
        assert_eq!(a["collateral_quote"], json!("1003000")); // +3000 P&L
        assert_eq!(a["entry_price_e8"], json!("101000000")); // reset to settle price
        assert_eq!(a["position_base"], json!("300000"));
        // Funding fields settle never touches are carried verbatim from the pre-account.
        assert_eq!(a["funding_paid_cumulative"], json!("7"));
        assert_eq!(a["funding_last_applied_epoch"], json!("2"));
        let b = accts.iter().find(|x| x["key"] == "bb").unwrap();
        assert_eq!(b["collateral_quote"], json!("997000")); // -3000 P&L
        let fx = &r["effects"];
        assert_eq!(fx["event"], json!("EpochSettled"));
        assert_eq!(fx["oracle_fresh"], json!(true));
        assert_eq!(fx["effective_maint_bps"], json!("600"));
        assert_eq!(fx["fee_pool_after"], json!("0"));
    }

    #[test]
    fn settle_liquidation_routes_penalty_to_fee_and_insurance() {
        // A large position with tiny collateral is liquidatable after mark-to-market;
        // the penalty must flow to the global fee pool + insurance, and the effect's
        // after-values must match the post-state.
        let accounts = json!([acct_json("aa", 1_000_000, 1_000, 100_000_000)]);
        let r = materialize_isolated_op(&req_accts(
            price_published_global(5),
            json!({"action": "settle_epoch"}),
            accounts,
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let accts = r["post"]["accounts"].as_array().unwrap();
        let a = accts.iter().find(|x| x["key"] == "aa").unwrap();
        assert_eq!(a["position_base"], json!("0")); // liquidated -> flat
        assert_eq!(a["liquidated_this_step"], json!(true));
        assert_eq!(a["entry_price_e8"], json!("0"));
        let pg = &r["post"]["global_state"];
        let fee_pool: i128 = pg["fee_pool_quote"].as_str().unwrap().parse().unwrap();
        let insurance: i128 = pg["insurance_balance"].as_str().unwrap().parse().unwrap();
        assert!(fee_pool > 0, "liquidation penalty should flow to fee pool");
        assert!(
            insurance > 0,
            "liquidation penalty should flow to insurance"
        );
        // The Python integration records the flat-dummy settle kernel effect here;
        // the outer integration effect carries the accumulated fee_pool_delta.
        assert_eq!(r["effects"]["fee_pool_after"], json!("0"));
        assert_eq!(r["effects"]["insurance_after"], json!("0"));
    }

    #[test]
    fn settle_wrong_phase_rejects_with_kernel_reason() {
        // Open phase; settle needs PricePublished -> kernel guard rejects.
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "settle_epoch"}),
            json!([]),
            true,
        ));
        assert_eq!(r["accept"], json!(false));
        assert_eq!(
            r["reject_reason"],
            json!(zenodex_runtime_core::perp_settle_epoch::REJ_GUARD)
        );
        assert!(r.get("post").is_none());
    }

    #[test]
    fn settle_operator_gate_rejects() {
        let r = materialize_isolated_op(&req_accts(
            price_published_global(5),
            json!({"action": "settle_epoch"}),
            json!([]),
            false,
        ));
        assert_eq!(r["reject_reason"], json!(REJ_OPERATOR));
        assert!(r.get("post").is_none());
    }

    #[test]
    fn settle_unknown_op_field_rejects() {
        let r = materialize_isolated_op(&req_accts(
            price_published_global(5),
            json!({"action": "settle_epoch", "price_e8": "1"}),
            json!([]),
            true,
        ));
        assert_eq!(r["reject_reason"], json!(REJ_UNKNOWN_OP_FIELD));
    }

    #[test]
    fn deposit_existing_account_materializes_collateral_and_effect() {
        // Account with a position -> the effect's notional/maint are NONZERO (account
        // context, not flat dummy), and collateral_after is the new collateral.
        let accounts = json!([acct_json("aa", 300_000, 1_000_000, 100_000_000)]);
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "deposit_collateral", "account_pubkey": "aa", "amount": "50000"}),
            accounts,
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let accts = r["post"]["accounts"].as_array().unwrap();
        let a = accts.iter().find(|x| x["key"] == "aa").unwrap();
        assert_eq!(a["collateral_quote"], json!("1050000"));
        assert_eq!(a["position_base"], json!("300000")); // unchanged
        assert_eq!(a["funding_paid_cumulative"], json!("7")); // preserved
        let fx = &r["effects"];
        assert_eq!(fx["event"], json!("CollateralDeposited"));
        assert_eq!(fx["notional_quote"], json!("300000")); // account-derived, nonzero
        assert_eq!(fx["maint_req_quote"], json!("18000"));
        assert_eq!(fx["init_req_quote"], json!("30000"));
        assert_eq!(fx["collateral_after"], json!("1050000"));
        assert_eq!(fx["margin_ok"], json!(true));
    }

    #[test]
    fn deposit_creates_new_account() {
        // account_pubkey absent from the request accounts -> created flat (first deposit).
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "deposit_collateral", "account_pubkey": "newkey", "amount": "50000"}),
            json!([]),
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let accts = r["post"]["accounts"].as_array().unwrap();
        assert_eq!(accts.len(), 1);
        assert_eq!(accts[0]["key"], json!("newkey"));
        assert_eq!(accts[0]["collateral_quote"], json!("50000"));
        assert_eq!(accts[0]["position_base"], json!("0"));
        assert_eq!(accts[0]["funding_paid_cumulative"], json!("0"));
        assert_eq!(r["effects"]["notional_quote"], json!("0")); // flat new account
        assert_eq!(r["effects"]["collateral_after"], json!("50000"));
    }

    #[test]
    fn deposit_sender_gate_rejects() {
        let mut r = req_accts(
            open_global(5),
            json!({"action": "deposit_collateral", "account_pubkey": "aa", "amount": "50000"}),
            json!([acct_json("aa", 0, 1000, 0)]),
            true,
        );
        r["facts"]["sender_bound_ok"] = json!(false);
        let out = materialize_isolated_op(&r);
        assert_eq!(out["reject_reason"], json!(REJ_SENDER_NOT_BOUND));
        assert!(out.get("post").is_none());
    }

    #[test]
    fn deposit_missing_sender_fact_is_boundary_error() {
        let mut r = req_accts(
            open_global(5),
            json!({"action": "deposit_collateral", "account_pubkey": "aa", "amount": "50000"}),
            json!([acct_json("aa", 0, 1000, 0)]),
            true,
        );
        r["facts"]
            .as_object_mut()
            .unwrap()
            .remove("sender_bound_ok");
        // Missing required fact is a boundary error, NOT the semantic sender reject.
        assert_eq!(
            materialize_isolated_op(&r)["reject_reason"],
            json!(REJ_MISSING_FACTS)
        );
    }

    #[test]
    fn deposit_unknown_op_field_rejects() {
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "deposit_collateral", "account_pubkey": "aa", "amount": "50000", "delta": "1"}),
            json!([acct_json("aa", 0, 1000, 0)]),
            true,
        ));
        assert_eq!(r["reject_reason"], json!(REJ_UNKNOWN_OP_FIELD));
    }

    #[test]
    fn deposit_overflow_rejects_without_panic() {
        // Depositing near i128::MAX must fail closed (kernel domain/guard), never panic.
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "deposit_collateral", "account_pubkey": "aa", "amount": i128::MAX.to_string()}),
            json!([acct_json("aa", 0, 1000, 0)]),
            true,
        ));
        assert_eq!(r["accept"], json!(false));
        assert!(r.get("post").is_none());
    }

    #[test]
    fn deposit_resets_liquidated_flag() {
        // A liquidation flag set in a prior settle persists through advance_epoch;
        // apply_deposit_collateral forces liquidated_this_step=false, so the
        // materializer must reset it too (NOT preserve the pre-value).
        let accounts = json!([{
            "key": "aa", "position_base": "0", "collateral_quote": "1000",
            "entry_price_e8": "0", "funding_paid_cumulative": "0",
            "funding_last_applied_epoch": "0", "liquidated_this_step": true
        }]);
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "deposit_collateral", "account_pubkey": "aa", "amount": "50000"}),
            accounts,
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let accts = r["post"]["accounts"].as_array().unwrap();
        let a = accts.iter().find(|x| x["key"] == "aa").unwrap();
        assert_eq!(a["liquidated_this_step"], json!(false)); // reset, not preserved
        assert_eq!(r["effects"]["liquidated"], json!(false));
    }

    #[test]
    fn withdraw_existing_account_materializes_collateral_and_effect() {
        let accounts = json!([acct_json("aa", 300_000, 1_000_000, 100_000_000)]);
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "withdraw_collateral", "account_pubkey": "aa", "amount": "10000"}),
            accounts,
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let accts = r["post"]["accounts"].as_array().unwrap();
        let a = accts.iter().find(|x| x["key"] == "aa").unwrap();
        assert_eq!(a["collateral_quote"], json!("990000")); // 1_000_000 - 10_000
        assert_eq!(a["position_base"], json!("300000")); // unchanged
        assert_eq!(a["funding_paid_cumulative"], json!("7")); // preserved
        assert_eq!(a["funding_last_applied_epoch"], json!("2")); // preserved
        let fx = &r["effects"];
        assert_eq!(fx["event"], json!("CollateralWithdrawn"));
        assert_eq!(fx["notional_quote"], json!("300000")); // account-derived, nonzero
        assert_eq!(fx["maint_req_quote"], json!("18000"));
        assert_eq!(fx["collateral_after"], json!("990000"));
        assert_eq!(fx["margin_ok"], json!(true));
    }

    #[test]
    fn withdraw_breaching_maint_margin_rejects() {
        // Withdraw most collateral while holding a position -> remaining < maint_req.
        // The core folds this post-margin check into the withdraw guard (it does NOT
        // emit the set_position-only REJ_MAINT_MARGIN), so the stable reason is
        // withdraw_collateral_guard. In rust_shadow Python rejects first ("guard"),
        // so the materializer is never invoked on this path; this asserts the core's
        // own reason for direct/authority use.
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "withdraw_collateral", "account_pubkey": "aa", "amount": "999000"}),
            json!([acct_json("aa", 300_000, 1_000_000, 100_000_000)]),
            true,
        ));
        assert_eq!(r["accept"], json!(false));
        assert_eq!(
            r["reject_reason"],
            json!(zenodex_runtime_core::perp_account_ops::REJ_WITHDRAW_GUARD)
        );
        assert!(r.get("post").is_none());
    }

    #[test]
    fn withdraw_over_collateral_rejects() {
        // amount > collateral -> negative balance -> withdraw guard (not margin).
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "withdraw_collateral", "account_pubkey": "aa", "amount": "2000000"}),
            json!([acct_json("aa", 0, 1_000_000, 0)]),
            true,
        ));
        assert_eq!(r["accept"], json!(false));
        assert_eq!(
            r["reject_reason"],
            json!(zenodex_runtime_core::perp_account_ops::REJ_WITHDRAW_GUARD)
        );
    }

    #[test]
    fn withdraw_resets_liquidated_flag_and_preserves_funding() {
        let accounts = json!([{
            "key": "aa", "position_base": "0", "collateral_quote": "1000",
            "entry_price_e8": "0", "funding_paid_cumulative": "99",
            "funding_last_applied_epoch": "3", "liquidated_this_step": true
        }]);
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "withdraw_collateral", "account_pubkey": "aa", "amount": "100"}),
            accounts,
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let accts = r["post"]["accounts"].as_array().unwrap();
        let a = accts.iter().find(|x| x["key"] == "aa").unwrap();
        assert_eq!(a["liquidated_this_step"], json!(false)); // reset
        assert_eq!(a["funding_paid_cumulative"], json!("99")); // preserved
        assert_eq!(a["funding_last_applied_epoch"], json!("3")); // preserved
        assert_eq!(a["collateral_quote"], json!("900"));
        assert_eq!(r["effects"]["liquidated"], json!(false));
    }

    #[test]
    fn withdraw_sender_gate_and_missing_fact() {
        // Sender-gated: false sender fact -> semantic reject; missing fact -> boundary.
        let mut r = req_accts(
            open_global(5),
            json!({"action": "withdraw_collateral", "account_pubkey": "aa", "amount": "100"}),
            json!([acct_json("aa", 0, 1000, 0)]),
            true,
        );
        r["facts"]["sender_bound_ok"] = json!(false);
        assert_eq!(
            materialize_isolated_op(&r)["reject_reason"],
            json!(REJ_SENDER_NOT_BOUND)
        );
        let mut r2 = req_accts(
            open_global(5),
            json!({"action": "withdraw_collateral", "account_pubkey": "aa", "amount": "100"}),
            json!([acct_json("aa", 0, 1000, 0)]),
            true,
        );
        r2["facts"]
            .as_object_mut()
            .unwrap()
            .remove("sender_bound_ok");
        assert_eq!(
            materialize_isolated_op(&r2)["reject_reason"],
            json!(REJ_MISSING_FACTS)
        );
    }

    #[test]
    fn withdraw_unknown_op_field_rejects() {
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "withdraw_collateral", "account_pubkey": "aa", "amount": "100", "delta": "1"}),
            json!([acct_json("aa", 0, 1000, 0)]),
            true,
        ));
        assert_eq!(r["reject_reason"], json!(REJ_UNKNOWN_OP_FIELD));
    }

    #[test]
    fn set_position_long_materializes_position_entry_and_effect() {
        // Open, oracle fresh, ample collateral -> set a long; entry := index price,
        // and the PositionSet effect is account-derived (nonzero notional/maint/init).
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": "500000"}),
            json!([acct_json("aa", 300_000, 1_000_000, 100_000_000)]),
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let accts = r["post"]["accounts"].as_array().unwrap();
        let a = accts.iter().find(|x| x["key"] == "aa").unwrap();
        assert_eq!(a["position_base"], json!("500000"));
        assert_eq!(a["entry_price_e8"], json!("100000000")); // := index
        assert_eq!(a["collateral_quote"], json!("1000000")); // unchanged
        assert_eq!(a["funding_paid_cumulative"], json!("7")); // preserved
        let fx = &r["effects"];
        assert_eq!(fx["event"], json!("PositionSet"));
        assert_eq!(fx["notional_quote"], json!("500000"));
        assert_eq!(fx["maint_req_quote"], json!("30000")); // 500000 * 6% / scale
        assert_eq!(fx["init_req_quote"], json!("50000")); // 500000 * 10%
        assert_eq!(fx["margin_ok"], json!(true));
    }

    #[test]
    fn set_position_short_sets_negative_and_abs_notional() {
        // new_position_base is SIGNED; a short is negative. Notional uses |position|.
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": "-200000"}),
            json!([acct_json("aa", 300_000, 1_000_000, 100_000_000)]),
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let a = r["post"]["accounts"].as_array().unwrap()[0].clone();
        assert_eq!(a["position_base"], json!("-200000"));
        assert_eq!(a["entry_price_e8"], json!("100000000"));
        assert_eq!(r["effects"]["notional_quote"], json!("200000")); // |−200000|
        assert_eq!(r["effects"]["maint_req_quote"], json!("12000"));
    }

    #[test]
    fn set_position_exact_param_boundaries_accept_when_margin_sufficient() {
        for pos in ["1000000", "-1000000"] {
            let r = materialize_isolated_op(&req_accts(
                open_global(5),
                json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": pos}),
                json!([acct_json("aa", 0, 1_000_000, 0)]),
                true,
            ));
            assert_eq!(r["accept"], json!(true), "pos={pos} response={r}");
            let a = r["post"]["accounts"].as_array().unwrap()[0].clone();
            assert_eq!(a["position_base"], json!(pos));
            assert_eq!(a["entry_price_e8"], json!("100000000"));
            assert_eq!(r["effects"]["notional_quote"], json!("1000000"));
        }
    }

    #[test]
    fn set_position_zero_creates_new_flat_account() {
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "set_position", "account_pubkey": "newkey", "new_position_base": "0"}),
            json!([]),
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let accts = r["post"]["accounts"].as_array().unwrap();
        let a = accts.iter().find(|x| x["key"] == "newkey").unwrap();
        assert_eq!(a["position_base"], json!("0"));
        assert_eq!(a["entry_price_e8"], json!("0"));
        assert_eq!(a["collateral_quote"], json!("0"));
        assert_eq!(r["effects"]["event"], json!("PositionSet"));
    }

    #[test]
    fn set_position_flat_zeroes_entry() {
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": "0"}),
            json!([acct_json("aa", 300_000, 1_000_000, 100_000_000)]),
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let a = r["post"]["accounts"].as_array().unwrap()[0].clone();
        assert_eq!(a["position_base"], json!("0"));
        assert_eq!(a["entry_price_e8"], json!("0")); // flat -> entry zeroed
        assert_eq!(r["effects"]["notional_quote"], json!("0"));
    }

    #[test]
    fn set_position_insufficient_initial_margin_is_guard() {
        // new long needs initial margin (10%); collateral 10_000 < 100_000 -> guard.
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": "1000000"}),
            json!([acct_json("aa", 0, 10_000, 0)]),
            true,
        ));
        assert_eq!(r["accept"], json!(false));
        assert_eq!(
            r["reject_reason"],
            json!(zenodex_runtime_core::perp_account_ops::REJ_SET_POSITION_GUARD)
        );
        assert!(r.get("post").is_none());
    }

    #[test]
    fn set_position_over_param_max_is_param_reject() {
        // |new_position_base| beyond the param domain -> param reject (before guard).
        let huge = "100000000000000000000000000000000000000"; // > POSITION_PARAM_MAX
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": huge}),
            json!([acct_json("aa", 0, 1_000_000, 0)]),
            true,
        ));
        assert_eq!(r["accept"], json!(false));
        assert_eq!(
            r["reject_reason"],
            json!(zenodex_runtime_core::perp_account_ops::REJ_PARAM_NEW_POSITION)
        );
    }

    #[test]
    fn set_position_breaker_reduce_only_below_maint_is_invariant() {
        // The distinguishing case: under breaker, reduce-only passes the guard, but
        // the remaining position is below maintenance -> REJ_MAINT_MARGIN (the only
        // account_op that emits it; withdraw folds margin into its guard instead).
        let mut g = open_global(5);
        g["breaker_active"] = json!(true);
        g["breaker_last_trigger_epoch"] = json!("5");
        // pos 300000 -> reduce to 200000; maint(200000 @ 1e8, 6%) = 12000 > coll 10000.
        let r = materialize_isolated_op(&req_accts(
            g,
            json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": "200000"}),
            json!([acct_json("aa", 300_000, 10_000, 100_000_000)]),
            true,
        ));
        assert_eq!(r["accept"], json!(false));
        assert_eq!(
            r["reject_reason"],
            json!(zenodex_runtime_core::perp_account_ops::REJ_MAINT_MARGIN)
        );
        assert!(r.get("post").is_none());
    }

    #[test]
    fn set_position_resets_liquidated_flag_and_preserves_funding() {
        let accounts = json!([{
            "key": "aa", "position_base": "300000", "collateral_quote": "1000000",
            "entry_price_e8": "100000000", "funding_paid_cumulative": "55",
            "funding_last_applied_epoch": "6", "liquidated_this_step": true
        }]);
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": "400000"}),
            accounts,
            true,
        ));
        assert_eq!(r["accept"], json!(true), "{r}");
        let a = r["post"]["accounts"].as_array().unwrap()[0].clone();
        assert_eq!(a["liquidated_this_step"], json!(false)); // reset
        assert_eq!(a["funding_paid_cumulative"], json!("55")); // preserved
        assert_eq!(a["funding_last_applied_epoch"], json!("6"));
        assert_eq!(a["position_base"], json!("400000"));
        assert_eq!(r["effects"]["liquidated"], json!(false));
    }

    #[test]
    fn set_position_sender_gate_and_missing_fact() {
        let mut r = req_accts(
            open_global(5),
            json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": "100000"}),
            json!([acct_json("aa", 0, 1_000_000, 0)]),
            true,
        );
        r["facts"]["sender_bound_ok"] = json!(false);
        assert_eq!(
            materialize_isolated_op(&r)["reject_reason"],
            json!(REJ_SENDER_NOT_BOUND)
        );
        let mut r2 = req_accts(
            open_global(5),
            json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": "100000"}),
            json!([acct_json("aa", 0, 1_000_000, 0)]),
            true,
        );
        r2["facts"]
            .as_object_mut()
            .unwrap()
            .remove("sender_bound_ok");
        assert_eq!(
            materialize_isolated_op(&r2)["reject_reason"],
            json!(REJ_MISSING_FACTS)
        );
    }

    #[test]
    fn set_position_unknown_op_field_rejects() {
        let r = materialize_isolated_op(&req_accts(
            open_global(5),
            json!({"action": "set_position", "account_pubkey": "aa", "new_position_base": "100000", "amount": "1"}),
            json!([acct_json("aa", 0, 1_000_000, 0)]),
            true,
        ));
        assert_eq!(r["reject_reason"], json!(REJ_UNKNOWN_OP_FIELD));
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
        // apply_funding_auto is not yet materialized -> the bridge keeps Python authoritative.
        let r = materialize_isolated_op(&req(
            settled_global(5),
            json!({"action": "apply_funding_auto"}),
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
