#![forbid(unsafe_code)]
//! `zenodex-runtime` — shadow/replay driver for the deterministic runtime core.
//!
//! Subcommands:
//!
//! ```text
//! zenodex-runtime replay-fee-trace     <trace.json|->   # kernel = fee_router
//! zenodex-runtime fee-route            <request.json|-> # one fee_router transition
//! zenodex-runtime replay-guard-trace   <trace.json|->   # kernel = replay_guard
//! zenodex-runtime replay-guard-admit   <request.json|-> # one replay_guard transition
//! zenodex-runtime replay-balance-trace <trace.json|->   # kernel = balances
//! zenodex-runtime balance-op           <request.json|-> # one balances transition
//! zenodex-runtime replay-zusd-trace    <trace.json|->   # kernel = zusd
//! zenodex-runtime zusd-op              <request.json|-> # one zUSD transition
//! zenodex-runtime verify-burn-trace    <trace.json|->   # kernel = burn_receipts
//! zenodex-runtime settle-swap-trace    <trace.json|->   # kernel = cpmm_settlement
//! zenodex-runtime cpmm-op              <request.json|-> # one cpmm_settlement transition
//! zenodex-runtime canonical-hash       <cases.json|->   # canonical primitive vectors
//! zenodex-runtime verify-state-root    <cases.json|->   # network state-root parity
//! zenodex-runtime perp-math            <cases.json|->   # perp stateless math
//! zenodex-runtime advance-epoch        <cases.json|->   # perps E2 advance_epoch
//! zenodex-runtime funding-auto         <cases.json|->   # perps E2 apply_funding_auto
//! zenodex-runtime publish-clearing-price <cases.json|-> # perps E2 publish_clearing_price
//! zenodex-runtime settle-epoch         <cases.json|->   # perps E2 settle_epoch
//! zenodex-runtime partial-liquidate    <cases.json|->   # perps E2 partial_liquidate
//! zenodex-runtime account-op           <cases.json|->   # perps E2 deposit/withdraw/set_position/clear_breaker
//! zenodex-runtime set-market-params    <cases.json|->   # perps E2 set_market_params
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

mod perp_isolated_op;

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
    canonical_json_bytes, encode_bytes, encode_uvarint, hex_to_bytes_fixed, sha256_hex,
    try_domain_sep_bytes, CanonicalError, JsonValue,
};
use zenodex_runtime_core::cpmm_swap::{
    init_pool, swap_exact_in, swap_exact_out_with_max_gap_bps, Pool, SwapReceipt, BPS_DENOM,
    CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT, DEX_POOL_RESERVE_MAX,
};
use zenodex_runtime_core::fee_router::{AssetAmount, DustEntry};
use zenodex_runtime_core::perp_account_ops::{account_op, AccountOpInput};
use zenodex_runtime_core::perp_advance_epoch::{advance_epoch, AdvanceEpochInput};
use zenodex_runtime_core::perp_funding_auto::{
    apply_funding_auto, FundingAccount, FundingAutoInput,
};
use zenodex_runtime_core::perp_math;
use zenodex_runtime_core::perp_partial_liquidate::{partial_liquidate, PartialLiquidateInput};
use zenodex_runtime_core::perp_publish_clearing_price::{
    publish_clearing_price, PublishClearingPriceInput,
};
use zenodex_runtime_core::perp_set_market_params::{
    set_market_params, MarketParamsAccount, SetMarketParamsInput,
};
use zenodex_runtime_core::perp_settle_epoch::{settle_epoch, SettleAccount, SettleEpochInput};
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

#[derive(Serialize)]
struct FeeAssetAmountOut {
    asset: String,
    amount: String,
}

#[derive(Serialize)]
struct FeeDustEntryOut {
    source: String,
    asset: String,
    amount: String,
    buyburn_remainder: String,
    stakers_remainder: String,
    reserve_remainder: String,
    hosts_remainder: String,
}

#[derive(Serialize)]
struct FeeAccumulatorOut {
    dust_by_stream: Vec<FeeDustEntryOut>,
    cum_buyburn: Vec<FeeAssetAmountOut>,
    cum_stakers: Vec<FeeAssetAmountOut>,
    cum_reserve: Vec<FeeAssetAmountOut>,
    cum_hosts: Vec<FeeAssetAmountOut>,
}

#[derive(Serialize)]
struct FeeReceiptOut {
    source: String,
    asset: String,
    amount: String,
    buyburn: String,
    stakers: String,
    reserve: String,
    hosts: String,
    dust: String,
}

#[derive(Serialize)]
struct FeeRouteOutput {
    version: u32,
    kernel: String,
    accept: bool,
    reject_reason: Option<String>,
    receipt_hash: Option<String>,
    receipt: Option<FeeReceiptOut>,
    pre_state_root: String,
    post_state_root: String,
    post_accumulator: FeeAccumulatorOut,
}

#[derive(Serialize)]
struct ReplayGuardStateEntryOut {
    sender: String,
    last_nonce: u64,
}

#[derive(Serialize)]
struct ReplayGuardReceiptOut {
    sender: String,
    nonce: u64,
    prev_nonce: u64,
}

#[derive(Serialize)]
struct ReplayGuardAdmitOutput {
    version: u32,
    kernel: String,
    accept: bool,
    reject_reason: Option<String>,
    receipt_hash: Option<String>,
    receipt: Option<ReplayGuardReceiptOut>,
    pre_state_root: String,
    post_state_root: String,
    post_state_entries: Vec<ReplayGuardStateEntryOut>,
}

#[derive(Serialize)]
struct BalanceStateEntryOut {
    pubkey: String,
    asset: String,
    amount: String,
}

#[derive(Serialize)]
struct BalanceReceiptOut {
    kind: String,
    sender: Option<String>,
    recipient: String,
    asset: String,
    amount: String,
}

#[derive(Serialize)]
struct BalanceOpOutput {
    version: u32,
    kernel: String,
    accept: bool,
    reject_reason: Option<String>,
    receipt_hash: Option<String>,
    receipt: Option<BalanceReceiptOut>,
    pre_state_root: String,
    post_state_root: String,
    post_state_entries: Vec<BalanceStateEntryOut>,
}

#[derive(Serialize)]
struct ZusdStateOut {
    now_epoch: String,
    oracle_seen: bool,
    oracle_last_update_epoch: String,
    price_e8: String,
    price_pending_e8: String,
    max_oracle_staleness_epochs: String,
    collateral_e8: String,
    debt_e8: String,
    free_debt_e8: String,
    sp_debt_e8: String,
    sp_coll_e8: String,
    protocol_collateral_e8: String,
    protocol_revenue_zusd_cum_e8: String,
    liquidator_compensation_collateral_cum_e8: String,
    mcr_bps: String,
    ccr_bps: String,
    min_debt_open_e8: String,
    max_debt_e8: String,
    max_debt_supply_e8: String,
    max_sp_coll_e8: String,
    max_protocol_coll_e8: String,
    base_rate_bps: String,
    base_rate_last_epoch: String,
    base_rate_decay_per_epoch_bps: String,
    base_rate_borrow_bump_bps: String,
    base_rate_redeem_bump_bps: String,
    borrow_fee_floor_bps: String,
    borrow_fee_max_bps: String,
    redemption_fee_floor_bps: String,
    redemption_fee_max_bps: String,
    liquidation_gas_comp_fixed_collateral_e8: String,
    liquidation_gas_comp_bps: String,
}

#[derive(Serialize)]
struct ZusdReceiptOut {
    tag: String,
}

#[derive(Serialize)]
struct ZusdOpOutput {
    version: u32,
    kernel: String,
    accept: bool,
    reject_reason: Option<String>,
    receipt_hash: Option<String>,
    receipt: Option<ZusdReceiptOut>,
    pre_state_root: String,
    post_state_root: String,
    post_state: ZusdStateOut,
}

#[derive(Serialize)]
struct CpmmPoolOut {
    initialized: bool,
    reserve0: String,
    reserve1: String,
    fee_bps: String,
}

#[derive(Serialize)]
struct CpmmReceiptOut {
    kind: String,
    zero_for_one: bool,
    amount_in: String,
    amount_out: String,
    fee_total: String,
    amount_out_quote: String,
    overdelivery_gap: String,
    gap_bps: String,
    new_reserve0: String,
    new_reserve1: String,
}

#[derive(Serialize)]
struct CpmmOpOutput {
    version: u32,
    kernel: String,
    accept: bool,
    reject_reason: Option<String>,
    receipt_hash: Option<String>,
    receipt: Option<CpmmReceiptOut>,
    pre_state_root: String,
    post_state_root: String,
    post_pool: CpmmPoolOut,
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

fn cases_array(req: &Value) -> Result<&Vec<Value>, String> {
    let obj = req
        .as_object()
        .ok_or_else(|| "request must be an object".to_string())?;
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), &["cases"]) {
        return Err(reason);
    }
    obj.get("cases")
        .and_then(Value::as_array)
        .ok_or_else(|| "request has no \"cases\" array".to_string())
}

// --- fee_router kernel --------------------------------------------------------

struct FeeRouteParts {
    source: String,
    asset: String,
    amount_str: String,
    split: FeeSplitTable,
}

fn fee_asset_out(asset: &str, amount: u128) -> FeeAssetAmountOut {
    FeeAssetAmountOut {
        asset: asset.to_string(),
        amount: amount.to_string(),
    }
}

fn fee_accumulator_out(acc: &FeeAccumulator) -> FeeAccumulatorOut {
    FeeAccumulatorOut {
        dust_by_stream: acc
            .dust_entries_full()
            .map(|entry| FeeDustEntryOut {
                source: entry.source.to_string(),
                asset: entry.asset.to_string(),
                amount: entry.amount.to_string(),
                buyburn_remainder: entry.buyburn_remainder.to_string(),
                stakers_remainder: entry.stakers_remainder.to_string(),
                reserve_remainder: entry.reserve_remainder.to_string(),
                hosts_remainder: entry.hosts_remainder.to_string(),
            })
            .collect(),
        cum_buyburn: acc
            .buyburn_entries()
            .map(|(asset, amount)| fee_asset_out(asset, amount))
            .collect(),
        cum_stakers: acc
            .stakers_entries()
            .map(|(asset, amount)| fee_asset_out(asset, amount))
            .collect(),
        cum_reserve: acc
            .reserve_entries()
            .map(|(asset, amount)| fee_asset_out(asset, amount))
            .collect(),
        cum_hosts: acc
            .hosts_entries()
            .map(|(asset, amount)| fee_asset_out(asset, amount))
            .collect(),
    }
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

fn parse_fee_route_parts(tx: &Value) -> Result<FeeRouteParts, String> {
    let obj = match tx.as_object() {
        Some(o) => o,
        None => return Err("malformed_tx".to_string()),
    };
    if obj.get("kind").and_then(Value::as_str) != Some("route_fee") {
        return Err("unknown_tx_kind".to_string());
    }
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), &TX_FIELDS) {
        return Err(reason);
    }
    let source = match obj.get("source").and_then(Value::as_str) {
        Some(s) => s,
        None => return Err("malformed_tx".to_string()),
    };
    let asset = match obj.get("asset").and_then(Value::as_str) {
        Some(s) => s,
        None => return Err("malformed_tx".to_string()),
    };
    let amount_str = match obj.get("amount").and_then(classify_integer) {
        Some(s) => s,
        None => return Err("malformed_tx".to_string()),
    };
    let split = parse_split_table(obj.get("split_table"))?;
    Ok(FeeRouteParts {
        source: source.to_string(),
        asset: asset.to_string(),
        amount_str,
        split,
    })
}

fn eval_fee_tx(acc: &FeeAccumulator, tx: &Value) -> Eval<FeeAccumulator> {
    let parts = match parse_fee_route_parts(tx) {
        Ok(parts) => parts,
        Err(reason) => return Eval::Reject(reason),
    };
    let source = parts.source.as_str();
    let asset = parts.asset.as_str();
    let amount_str = parts.amount_str;
    let split = parts.split;
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

fn parse_fee_state_amount(v: &Value, label: &str) -> Result<u128, String> {
    let amount = match classify_integer(v) {
        Some(s) => s,
        None => return Err(format!("{label} invalid_accumulator_amount")),
    };
    amount
        .parse::<u128>()
        .map_err(|_| format!("{label} invalid_accumulator_amount"))
}

fn parse_fee_asset_entries(v: &Value, label: &str) -> Result<Vec<AssetAmount>, String> {
    let entries = v
        .as_array()
        .ok_or_else(|| format!("{label} must be an array"))?;
    let mut parsed = Vec::with_capacity(entries.len());
    for (index, entry) in entries.iter().enumerate() {
        let obj = entry
            .as_object()
            .ok_or_else(|| format!("{label}[{index}] must be an object"))?;
        if let Some(reason) =
            first_unknown_field(obj.keys().map(String::as_str), &["asset", "amount"])
        {
            return Err(format!("{label}[{index}]:{reason}"));
        }
        let asset = obj
            .get("asset")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{label}[{index}].asset must be a string"))?;
        let amount = parse_fee_state_amount(
            obj.get("amount")
                .ok_or_else(|| format!("{label}[{index}].amount invalid_accumulator_amount"))?,
            &format!("{label}[{index}].amount"),
        )?;
        parsed.push(AssetAmount {
            asset: asset.to_string(),
            amount,
        });
    }
    Ok(parsed)
}

fn parse_fee_dust_entries(v: &Value) -> Result<Vec<DustEntry>, String> {
    let entries = v
        .as_array()
        .ok_or_else(|| "dust_by_stream must be an array".to_string())?;
    let mut parsed = Vec::with_capacity(entries.len());
    for (index, entry) in entries.iter().enumerate() {
        let obj = entry
            .as_object()
            .ok_or_else(|| format!("dust_by_stream[{index}] must be an object"))?;
        if let Some(reason) = first_unknown_field(
            obj.keys().map(String::as_str),
            &[
                "source",
                "asset",
                "amount",
                "buyburn_remainder",
                "stakers_remainder",
                "reserve_remainder",
                "hosts_remainder",
            ],
        ) {
            return Err(format!("dust_by_stream[{index}]:{reason}"));
        }
        let source = obj
            .get("source")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("dust_by_stream[{index}].source must be a string"))?;
        let asset = obj
            .get("asset")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("dust_by_stream[{index}].asset must be a string"))?;
        let amount = parse_fee_state_amount(
            obj.get("amount").ok_or_else(|| {
                format!("dust_by_stream[{index}].amount invalid_accumulator_amount")
            })?,
            &format!("dust_by_stream[{index}].amount"),
        )?;
        let buyburn_remainder = parse_fee_state_amount(
            obj.get("buyburn_remainder")
                .unwrap_or(&Value::String("0".to_string())),
            &format!("dust_by_stream[{index}].buyburn_remainder"),
        )?;
        let stakers_remainder = parse_fee_state_amount(
            obj.get("stakers_remainder")
                .unwrap_or(&Value::String("0".to_string())),
            &format!("dust_by_stream[{index}].stakers_remainder"),
        )?;
        let reserve_remainder = parse_fee_state_amount(
            obj.get("reserve_remainder")
                .unwrap_or(&Value::String("0".to_string())),
            &format!("dust_by_stream[{index}].reserve_remainder"),
        )?;
        let hosts_remainder = parse_fee_state_amount(
            obj.get("hosts_remainder")
                .unwrap_or(&Value::String("0".to_string())),
            &format!("dust_by_stream[{index}].hosts_remainder"),
        )?;
        parsed.push(DustEntry {
            source: source.to_string(),
            asset: asset.to_string(),
            amount,
            buyburn_remainder,
            stakers_remainder,
            reserve_remainder,
            hosts_remainder,
        });
    }
    Ok(parsed)
}

fn fee_accumulator_from_request(v: &Value) -> Result<FeeAccumulator, String> {
    let obj = v
        .get("accumulator")
        .and_then(Value::as_object)
        .ok_or_else(|| "accumulator must be an object".to_string())?;
    let fields = [
        "dust_by_stream",
        "cum_buyburn",
        "cum_stakers",
        "cum_reserve",
        "cum_hosts",
    ];
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), &fields) {
        return Err(reason);
    }
    let empty = Value::Array(Vec::new());
    let dust = parse_fee_dust_entries(obj.get("dust_by_stream").unwrap_or(&empty))?;
    let buyburn = parse_fee_asset_entries(obj.get("cum_buyburn").unwrap_or(&empty), "cum_buyburn")?;
    let stakers = parse_fee_asset_entries(obj.get("cum_stakers").unwrap_or(&empty), "cum_stakers")?;
    let reserve = parse_fee_asset_entries(obj.get("cum_reserve").unwrap_or(&empty), "cum_reserve")?;
    let hosts = parse_fee_asset_entries(obj.get("cum_hosts").unwrap_or(&empty), "cum_hosts")?;
    FeeAccumulator::from_parts(dust, buyburn, stakers, reserve, hosts)
        .map_err(|reason| format!("invalid fee accumulator: {reason}"))
}

fn fee_receipt_out(r: &zenodex_runtime_core::FeeReceipt) -> FeeReceiptOut {
    FeeReceiptOut {
        source: r.source.clone(),
        asset: r.asset.clone(),
        amount: r.amount.to_string(),
        buyburn: r.buyburn.to_string(),
        stakers: r.stakers.to_string(),
        reserve: r.reserve.to_string(),
        hosts: r.hosts.to_string(),
        dust: r.dust.to_string(),
    }
}

fn rejected_fee_output(
    acc: &FeeAccumulator,
    pre_state_root: String,
    reason: String,
) -> FeeRouteOutput {
    FeeRouteOutput {
        version: 1,
        kernel: "fee_router".to_string(),
        accept: false,
        reject_reason: Some(reason),
        receipt_hash: None,
        receipt: None,
        pre_state_root: pre_state_root.clone(),
        post_state_root: pre_state_root,
        post_accumulator: fee_accumulator_out(acc),
    }
}

fn run_fee_route(request: &Value) -> Result<FeeRouteOutput, String> {
    let obj = request
        .as_object()
        .ok_or_else(|| "request must be an object".to_string())?;
    if let Some(reason) = first_unknown_field(
        obj.keys().map(String::as_str),
        &["version", "accumulator", "tx"],
    ) {
        return Err(reason);
    }
    if request.get("version").and_then(Value::as_u64).unwrap_or(1) != 1 {
        return Err("unsupported request version".to_string());
    }
    let acc = fee_accumulator_from_request(request)?;
    let pre_state_root = acc.state_root();
    let tx = request
        .get("tx")
        .ok_or_else(|| "tx is required".to_string())?;
    let parts = match parse_fee_route_parts(tx) {
        Ok(parts) => parts,
        Err(reason) => return Ok(rejected_fee_output(&acc, pre_state_root, reason)),
    };
    if parts.amount_str.starts_with('-') {
        return Ok(rejected_fee_output(
            &acc,
            pre_state_root,
            "negative_amount".to_string(),
        ));
    }
    let amount: u128 = match parts.amount_str.parse::<u128>() {
        Ok(v) => v,
        Err(_) => {
            return Ok(rejected_fee_output(
                &acc,
                pre_state_root,
                "amount_too_large".to_string(),
            ))
        }
    };
    match route_fee(
        parts.source.as_str(),
        parts.asset.as_str(),
        amount,
        &parts.split,
        &acc,
    ) {
        Ok(accepted) => {
            let receipt_hash = accepted.receipt.receipt_hash();
            Ok(FeeRouteOutput {
                version: 1,
                kernel: "fee_router".to_string(),
                accept: true,
                reject_reason: None,
                receipt_hash: Some(receipt_hash),
                receipt: Some(fee_receipt_out(&accepted.receipt)),
                pre_state_root,
                post_state_root: accepted.accumulator.state_root(),
                post_accumulator: fee_accumulator_out(&accepted.accumulator),
            })
        }
        Err(reason) => Ok(rejected_fee_output(
            &acc,
            pre_state_root,
            reason.reason_str(),
        )),
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

fn replay_guard_entries_out(state: &ReplayGuardState) -> Vec<ReplayGuardStateEntryOut> {
    state
        .entries()
        .map(|(sender, last_nonce)| ReplayGuardStateEntryOut {
            sender: sender.to_string(),
            last_nonce,
        })
        .collect()
}

fn replay_guard_state_from_request(v: &Value) -> Result<ReplayGuardState, String> {
    let entries = v
        .get("state_entries")
        .and_then(Value::as_array)
        .ok_or_else(|| "state_entries must be an array".to_string())?;
    let mut parsed = Vec::with_capacity(entries.len());
    for (index, entry) in entries.iter().enumerate() {
        let obj = entry
            .as_object()
            .ok_or_else(|| format!("state_entries[{index}] must be an object"))?;
        if let Some(reason) =
            first_unknown_field(obj.keys().map(String::as_str), &["sender", "last_nonce"])
        {
            return Err(format!("state_entries[{index}]:{reason}"));
        }
        let sender = obj
            .get("sender")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("state_entries[{index}].sender must be a string"))?;
        let last_nonce = match obj.get("last_nonce").and_then(classify_integer) {
            Some(s) => match s.parse::<u64>() {
                Ok(v) => v,
                Err(_) => return Err(format!("state_entries[{index}].last_nonce invalid_nonce")),
            },
            None => return Err(format!("state_entries[{index}].last_nonce invalid_nonce")),
        };
        parsed.push((sender.to_string(), last_nonce));
    }
    ReplayGuardState::from_entries(parsed)
        .map_err(|reason| format!("invalid replay_guard state: {}", reason.reason_str()))
}

fn run_replay_guard_admit(request: &Value) -> Result<ReplayGuardAdmitOutput, String> {
    let obj = request
        .as_object()
        .ok_or_else(|| "request must be an object".to_string())?;
    if let Some(reason) = first_unknown_field(
        obj.keys().map(String::as_str),
        &["version", "state_entries", "tx"],
    ) {
        return Err(reason);
    }
    if request.get("version").and_then(Value::as_u64).unwrap_or(1) != 1 {
        return Err("unsupported request version".to_string());
    }
    let state = replay_guard_state_from_request(request)?;
    let pre_state_root = state.state_root();
    let tx = request
        .get("tx")
        .ok_or_else(|| "tx is required".to_string())?;
    match eval_admit_tx(&state, tx) {
        Eval::Accept { receipt_hash, next } => {
            let sender = tx
                .get("sender")
                .and_then(Value::as_str)
                .and_then(canonical_sender)
                .ok_or_else(|| "accepted replay_guard tx had no canonical sender".to_string())?;
            let nonce = tx
                .get("nonce")
                .and_then(classify_integer)
                .and_then(|s| s.parse::<u64>().ok())
                .ok_or_else(|| "accepted replay_guard tx had no nonce".to_string())?;
            let prev_nonce = state.last_for(&sender);
            Ok(ReplayGuardAdmitOutput {
                version: 1,
                kernel: "replay_guard".to_string(),
                accept: true,
                reject_reason: None,
                receipt_hash: Some(receipt_hash),
                receipt: Some(ReplayGuardReceiptOut {
                    sender,
                    nonce,
                    prev_nonce,
                }),
                pre_state_root,
                post_state_root: next.state_root(),
                post_state_entries: replay_guard_entries_out(&next),
            })
        }
        Eval::Reject(reason) => Ok(ReplayGuardAdmitOutput {
            version: 1,
            kernel: "replay_guard".to_string(),
            accept: false,
            reject_reason: Some(reason),
            receipt_hash: None,
            receipt: None,
            pre_state_root: pre_state_root.clone(),
            post_state_root: pre_state_root,
            post_state_entries: replay_guard_entries_out(&state),
        }),
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

fn balance_entries_out(state: &BalanceState) -> Vec<BalanceStateEntryOut> {
    state
        .entries()
        .map(|(pubkey, asset, amount)| BalanceStateEntryOut {
            pubkey: pubkey.to_string(),
            asset: asset.to_string(),
            amount: amount.to_string(),
        })
        .collect()
}

fn balance_state_from_request(v: &Value) -> Result<BalanceState, String> {
    let entries = v
        .get("state_entries")
        .and_then(Value::as_array)
        .ok_or_else(|| "state_entries must be an array".to_string())?;
    let mut parsed = Vec::with_capacity(entries.len());
    for (index, entry) in entries.iter().enumerate() {
        let obj = entry
            .as_object()
            .ok_or_else(|| format!("state_entries[{index}] must be an object"))?;
        if let Some(reason) = first_unknown_field(
            obj.keys().map(String::as_str),
            &["pubkey", "asset", "amount"],
        ) {
            return Err(format!("state_entries[{index}]:{reason}"));
        }
        let pubkey = obj
            .get("pubkey")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("state_entries[{index}].pubkey must be a string"))?;
        let asset = obj
            .get("asset")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("state_entries[{index}].asset must be a string"))?;
        let amount = match obj.get("amount").and_then(classify_integer) {
            Some(s) => match s.parse::<u128>() {
                Ok(v) => v,
                Err(_) => return Err(format!("state_entries[{index}].amount invalid_amount")),
            },
            None => return Err(format!("state_entries[{index}].amount invalid_amount")),
        };
        parsed.push((pubkey.to_string(), asset.to_string(), amount));
    }
    BalanceState::from_entries(parsed).map_err(|reason| format!("invalid balance state: {reason}"))
}

fn accepted_balance_receipt(tx: &Value) -> Result<BalanceReceiptOut, String> {
    let obj = tx
        .as_object()
        .ok_or_else(|| "accepted balance tx must be an object".to_string())?;
    let kind = obj
        .get("kind")
        .and_then(Value::as_str)
        .ok_or_else(|| "accepted balance tx missing kind".to_string())?;
    let asset = obj
        .get("asset")
        .and_then(Value::as_str)
        .and_then(canonical_asset)
        .ok_or_else(|| "accepted balance tx missing canonical asset".to_string())?;
    let amount = obj
        .get("amount")
        .and_then(classify_integer)
        .and_then(|s| s.parse::<u128>().ok())
        .ok_or_else(|| "accepted balance tx missing amount".to_string())?;
    if kind == "credit" {
        let recipient = obj
            .get("recipient")
            .and_then(Value::as_str)
            .and_then(canonical_pubkey)
            .ok_or_else(|| "accepted credit missing canonical recipient".to_string())?;
        return Ok(BalanceReceiptOut {
            kind: "credit".to_string(),
            sender: None,
            recipient,
            asset,
            amount: amount.to_string(),
        });
    }
    if kind == "transfer" {
        let sender = obj
            .get("sender")
            .and_then(Value::as_str)
            .and_then(canonical_pubkey)
            .ok_or_else(|| "accepted transfer missing canonical sender".to_string())?;
        let recipient = obj
            .get("recipient")
            .and_then(Value::as_str)
            .and_then(canonical_pubkey)
            .ok_or_else(|| "accepted transfer missing canonical recipient".to_string())?;
        return Ok(BalanceReceiptOut {
            kind: "transfer".to_string(),
            sender: Some(sender),
            recipient,
            asset,
            amount: amount.to_string(),
        });
    }
    Err("accepted balance tx had unknown kind".to_string())
}

fn run_balance_op(request: &Value) -> Result<BalanceOpOutput, String> {
    let obj = request
        .as_object()
        .ok_or_else(|| "request must be an object".to_string())?;
    if let Some(reason) = first_unknown_field(
        obj.keys().map(String::as_str),
        &["version", "state_entries", "tx"],
    ) {
        return Err(reason);
    }
    if request.get("version").and_then(Value::as_u64).unwrap_or(1) != 1 {
        return Err("unsupported request version".to_string());
    }
    let state = balance_state_from_request(request)?;
    let pre_state_root = state.state_root();
    let tx = request
        .get("tx")
        .ok_or_else(|| "tx is required".to_string())?;
    match eval_balance_tx(&state, tx) {
        Eval::Accept { receipt_hash, next } => Ok(BalanceOpOutput {
            version: 1,
            kernel: "balances".to_string(),
            accept: true,
            reject_reason: None,
            receipt_hash: Some(receipt_hash),
            receipt: Some(accepted_balance_receipt(tx)?),
            pre_state_root,
            post_state_root: next.state_root(),
            post_state_entries: balance_entries_out(&next),
        }),
        Eval::Reject(reason) => Ok(BalanceOpOutput {
            version: 1,
            kernel: "balances".to_string(),
            accept: false,
            reject_reason: Some(reason),
            receipt_hash: None,
            receipt: None,
            pre_state_root: pre_state_root.clone(),
            post_state_root: pre_state_root,
            post_state_entries: balance_entries_out(&state),
        }),
    }
}

// --- zusd kernel --------------------------------------------------------------

const ZUSD_STATE_FIELDS: [&str; 32] = [
    "now_epoch",
    "oracle_seen",
    "oracle_last_update_epoch",
    "price_e8",
    "price_pending_e8",
    "max_oracle_staleness_epochs",
    "collateral_e8",
    "debt_e8",
    "free_debt_e8",
    "sp_debt_e8",
    "sp_coll_e8",
    "protocol_collateral_e8",
    "protocol_revenue_zusd_cum_e8",
    "liquidator_compensation_collateral_cum_e8",
    "mcr_bps",
    "ccr_bps",
    "min_debt_open_e8",
    "max_debt_e8",
    "max_debt_supply_e8",
    "max_sp_coll_e8",
    "max_protocol_coll_e8",
    "base_rate_bps",
    "base_rate_last_epoch",
    "base_rate_decay_per_epoch_bps",
    "base_rate_borrow_bump_bps",
    "base_rate_redeem_bump_bps",
    "borrow_fee_floor_bps",
    "borrow_fee_max_bps",
    "redemption_fee_floor_bps",
    "redemption_fee_max_bps",
    "liquidation_gas_comp_fixed_collateral_e8",
    "liquidation_gas_comp_bps",
];
const ZUSD_OP_TOP_LEVEL_FIELDS: [&str; 5] = [
    "version",
    "state",
    "tx",
    "facts",
    "require_oracle_authorization",
];
const ZUSD_ORACLE_COLLATERAL_QUERY_ID: &str =
    "sha256:aab2e1b26ac1a1a5069664959c129fa29a63107b949b777480bf0e3928eeaec1";

fn zusd_u128(obj: &serde_json::Map<String, Value>, key: &str) -> Result<u128, String> {
    obj.get(key)
        .and_then(classify_integer)
        .and_then(|s| s.parse::<u128>().ok())
        .ok_or_else(|| format!("bad_state_field:{key}"))
}

fn zusd_state_from_value(value: &Value) -> Result<ZusdState, String> {
    let obj = value
        .as_object()
        .ok_or_else(|| "state must be an object".to_string())?;
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), &ZUSD_STATE_FIELDS) {
        return Err(reason);
    }
    let oracle_seen = obj
        .get("oracle_seen")
        .and_then(Value::as_bool)
        .ok_or_else(|| "bad_state_field:oracle_seen".to_string())?;
    Ok(ZusdState {
        now_epoch: zusd_u128(obj, "now_epoch")?,
        oracle_seen,
        oracle_last_update_epoch: zusd_u128(obj, "oracle_last_update_epoch")?,
        price_e8: zusd_u128(obj, "price_e8")?,
        price_pending_e8: zusd_u128(obj, "price_pending_e8")?,
        max_oracle_staleness_epochs: zusd_u128(obj, "max_oracle_staleness_epochs")?,
        collateral_e8: zusd_u128(obj, "collateral_e8")?,
        debt_e8: zusd_u128(obj, "debt_e8")?,
        free_debt_e8: zusd_u128(obj, "free_debt_e8")?,
        sp_debt_e8: zusd_u128(obj, "sp_debt_e8")?,
        sp_coll_e8: zusd_u128(obj, "sp_coll_e8")?,
        protocol_collateral_e8: zusd_u128(obj, "protocol_collateral_e8")?,
        protocol_revenue_zusd_cum_e8: zusd_u128(obj, "protocol_revenue_zusd_cum_e8")?,
        liquidator_compensation_collateral_cum_e8: zusd_u128(
            obj,
            "liquidator_compensation_collateral_cum_e8",
        )?,
        mcr_bps: zusd_u128(obj, "mcr_bps")?,
        ccr_bps: zusd_u128(obj, "ccr_bps")?,
        min_debt_open_e8: zusd_u128(obj, "min_debt_open_e8")?,
        max_debt_e8: zusd_u128(obj, "max_debt_e8")?,
        max_debt_supply_e8: zusd_u128(obj, "max_debt_supply_e8")?,
        max_sp_coll_e8: zusd_u128(obj, "max_sp_coll_e8")?,
        max_protocol_coll_e8: zusd_u128(obj, "max_protocol_coll_e8")?,
        base_rate_bps: zusd_u128(obj, "base_rate_bps")?,
        base_rate_last_epoch: zusd_u128(obj, "base_rate_last_epoch")?,
        base_rate_decay_per_epoch_bps: zusd_u128(obj, "base_rate_decay_per_epoch_bps")?,
        base_rate_borrow_bump_bps: zusd_u128(obj, "base_rate_borrow_bump_bps")?,
        base_rate_redeem_bump_bps: zusd_u128(obj, "base_rate_redeem_bump_bps")?,
        borrow_fee_floor_bps: zusd_u128(obj, "borrow_fee_floor_bps")?,
        borrow_fee_max_bps: zusd_u128(obj, "borrow_fee_max_bps")?,
        redemption_fee_floor_bps: zusd_u128(obj, "redemption_fee_floor_bps")?,
        redemption_fee_max_bps: zusd_u128(obj, "redemption_fee_max_bps")?,
        liquidation_gas_comp_fixed_collateral_e8: zusd_u128(
            obj,
            "liquidation_gas_comp_fixed_collateral_e8",
        )?,
        liquidation_gas_comp_bps: zusd_u128(obj, "liquidation_gas_comp_bps")?,
    })
}

fn zusd_state_out(state: &ZusdState) -> ZusdStateOut {
    ZusdStateOut {
        now_epoch: state.now_epoch.to_string(),
        oracle_seen: state.oracle_seen,
        oracle_last_update_epoch: state.oracle_last_update_epoch.to_string(),
        price_e8: state.price_e8.to_string(),
        price_pending_e8: state.price_pending_e8.to_string(),
        max_oracle_staleness_epochs: state.max_oracle_staleness_epochs.to_string(),
        collateral_e8: state.collateral_e8.to_string(),
        debt_e8: state.debt_e8.to_string(),
        free_debt_e8: state.free_debt_e8.to_string(),
        sp_debt_e8: state.sp_debt_e8.to_string(),
        sp_coll_e8: state.sp_coll_e8.to_string(),
        protocol_collateral_e8: state.protocol_collateral_e8.to_string(),
        protocol_revenue_zusd_cum_e8: state.protocol_revenue_zusd_cum_e8.to_string(),
        liquidator_compensation_collateral_cum_e8: state
            .liquidator_compensation_collateral_cum_e8
            .to_string(),
        mcr_bps: state.mcr_bps.to_string(),
        ccr_bps: state.ccr_bps.to_string(),
        min_debt_open_e8: state.min_debt_open_e8.to_string(),
        max_debt_e8: state.max_debt_e8.to_string(),
        max_debt_supply_e8: state.max_debt_supply_e8.to_string(),
        max_sp_coll_e8: state.max_sp_coll_e8.to_string(),
        max_protocol_coll_e8: state.max_protocol_coll_e8.to_string(),
        base_rate_bps: state.base_rate_bps.to_string(),
        base_rate_last_epoch: state.base_rate_last_epoch.to_string(),
        base_rate_decay_per_epoch_bps: state.base_rate_decay_per_epoch_bps.to_string(),
        base_rate_borrow_bump_bps: state.base_rate_borrow_bump_bps.to_string(),
        base_rate_redeem_bump_bps: state.base_rate_redeem_bump_bps.to_string(),
        borrow_fee_floor_bps: state.borrow_fee_floor_bps.to_string(),
        borrow_fee_max_bps: state.borrow_fee_max_bps.to_string(),
        redemption_fee_floor_bps: state.redemption_fee_floor_bps.to_string(),
        redemption_fee_max_bps: state.redemption_fee_max_bps.to_string(),
        liquidation_gas_comp_fixed_collateral_e8: state
            .liquidation_gas_comp_fixed_collateral_e8
            .to_string(),
        liquidation_gas_comp_bps: state.liquidation_gas_comp_bps.to_string(),
    }
}

fn run_zusd_op(request: &Value) -> Result<ZusdOpOutput, String> {
    let obj = request
        .as_object()
        .ok_or_else(|| "request must be an object".to_string())?;
    if let Some(reason) =
        first_unknown_field(obj.keys().map(String::as_str), &ZUSD_OP_TOP_LEVEL_FIELDS)
    {
        return Err(reason);
    }
    if request.get("version").and_then(Value::as_u64).unwrap_or(1) != 1 {
        return Err("unsupported request version".to_string());
    }
    let require_oracle_authorization = match request.get("require_oracle_authorization") {
        Some(Value::Bool(v)) => *v,
        Some(_) => return Err("require_oracle_authorization must be a bool".to_string()),
        None => false,
    };
    let state = zusd_state_from_value(
        request
            .get("state")
            .ok_or_else(|| "state is required".to_string())?,
    )?;
    let tx = request
        .get("tx")
        .ok_or_else(|| "tx is required".to_string())?;
    let pre_state_root = state.state_root();
    if let Some(reason) = zusd_oracle_gate(
        &state,
        tx,
        request.get("facts"),
        require_oracle_authorization,
    ) {
        return Ok(zusd_reject_output(state, pre_state_root, reason));
    }
    match eval_zusd_tx(&state, tx) {
        Eval::Accept { receipt_hash, next } => Ok(ZusdOpOutput {
            version: 1,
            kernel: "zusd".to_string(),
            accept: true,
            reject_reason: None,
            receipt_hash: Some(receipt_hash),
            receipt: Some(ZusdReceiptOut {
                tag: tx
                    .get("kind")
                    .and_then(Value::as_str)
                    .unwrap_or("")
                    .to_string(),
            }),
            pre_state_root,
            post_state_root: next.state_root(),
            post_state: zusd_state_out(&next),
        }),
        Eval::Reject(reason) => Ok(zusd_reject_output(state, pre_state_root, reason)),
    }
}

fn zusd_reject_output(state: ZusdState, pre_state_root: String, reason: String) -> ZusdOpOutput {
    ZusdOpOutput {
        version: 1,
        kernel: "zusd".to_string(),
        accept: false,
        reject_reason: Some(reason),
        receipt_hash: None,
        receipt: None,
        pre_state_root: pre_state_root.clone(),
        post_state_root: pre_state_root,
        post_state: zusd_state_out(&state),
    }
}

/// Integer-shaped arg as a literal string, else `None` (zUSD `_require_pos_int`
/// validates `> 0` in the core). zUSD ignores unknown fields, like the authority.
fn num_arg(obj: &serde_json::Map<String, Value>, key: &str) -> Option<String> {
    obj.get(key).and_then(classify_integer)
}

fn flag(obj: &serde_json::Map<String, Value>, key: &str) -> bool {
    obj.get(key).and_then(Value::as_bool).unwrap_or(false)
}

fn zusd_critical_oracle_action_kind(kind: &str) -> Option<&'static str> {
    match kind {
        "bootstrap_oracle" => Some("bootstrap_oracle"),
        "oracle_report" => Some("oracle_report"),
        "oracle_commit" => Some("oracle_commit"),
        "mint_zusd" => Some("mint"),
        "liquidate" => Some("liquidate_vault"),
        _ => None,
    }
}

fn zusd_oracle_gate(
    state: &ZusdState,
    tx: &Value,
    facts: Option<&Value>,
    require_oracle_authorization: bool,
) -> Option<String> {
    if !require_oracle_authorization {
        return None;
    }
    let tx_obj = match tx.as_object() {
        Some(obj) => obj,
        None => return None,
    };
    let kind = tx_obj.get("kind").and_then(Value::as_str).unwrap_or("");
    let expected_action_kind = zusd_critical_oracle_action_kind(kind)?;
    if facts.and_then(Value::as_object).is_none() {
        return Some("oracle_facts_required".to_string());
    }
    let _ = state;
    let _ = expected_action_kind;
    Some("oracle_authorization_external_required".to_string())
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

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn decode_even_hex_body(body: &str) -> Result<Vec<u8>, CanonicalError> {
    if body.len() % 2 != 0 {
        return Err(CanonicalError::BadHexFormat);
    }
    let bytes = body.as_bytes();
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for chunk in bytes.chunks_exact(2) {
        let hi = hex_nibble(chunk[0]).ok_or(CanonicalError::BadHexChars)?;
        let lo = hex_nibble(chunk[1]).ok_or(CanonicalError::BadHexChars)?;
        out.push((hi << 4) | lo);
    }
    Ok(out)
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
/// Each case is `{"op":"json_bytes"|"json_hash","value":<any>}`,
/// `{"op":"hex_to_bytes","hex":"0x..","nbytes":N}`, `{"op":"uvarint","value":N}`,
/// or `{"op":"encode_bytes","hex":"0x.."}`. Output mirrors per-case results so
/// the Python authority can diff `bytes`/`hash`/`code` exactly.
fn run_canonical_cases(req: &Value) -> Result<CanonicalOutput, String> {
    let cases = cases_array(req)?;
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
                if let Some(reason) =
                    first_unknown_field(obj.keys().map(String::as_str), &["op", "value"])
                {
                    results.push(err_case(index, &reason));
                    continue;
                }
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
                if let Some(reason) =
                    first_unknown_field(obj.keys().map(String::as_str), &["op", "hex", "nbytes"])
                {
                    results.push(err_case(index, &reason));
                    continue;
                }
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
            Some("uvarint") => {
                if let Some(reason) =
                    first_unknown_field(obj.keys().map(String::as_str), &["op", "value"])
                {
                    results.push(err_case(index, &reason));
                    continue;
                }
                let value = match obj.get("value").and_then(classify_integer) {
                    Some(s) => match s.parse::<u128>() {
                        Ok(n) => n,
                        Err(_) => {
                            results.push(err_case(index, "uvarint_out_of_range"));
                            continue;
                        }
                    },
                    None => {
                        results.push(err_case(index, "malformed_case"));
                        continue;
                    }
                };
                results.push(CanonicalCaseResult {
                    index,
                    ok: true,
                    bytes: Some(to_hex_0x(&encode_uvarint(value))),
                    hash: None,
                    code: None,
                });
            }
            Some("encode_bytes") => {
                if let Some(reason) =
                    first_unknown_field(obj.keys().map(String::as_str), &["op", "hex"])
                {
                    results.push(err_case(index, &reason));
                    continue;
                }
                let hex_str = match obj.get("hex").and_then(Value::as_str) {
                    Some(s) => s,
                    None => {
                        results.push(err_case(index, "malformed_case"));
                        continue;
                    }
                };
                let body = match hex_str.strip_prefix("0x") {
                    Some(body) if body.len() % 2 == 0 => body,
                    _ => {
                        results.push(err_case(index, "bad_hex_format"));
                        continue;
                    }
                };
                match decode_even_hex_body(body) {
                    Ok(bytes) => results.push(CanonicalCaseResult {
                        index,
                        ok: true,
                        bytes: Some(to_hex_0x(&encode_bytes(&bytes))),
                        hash: None,
                        code: None,
                    }),
                    Err(_) => results.push(err_case(index, "bad_hex_chars")),
                }
            }
            // sha256(domain_sep(label, version) + canonical_json_bytes(value)) —
            // the shape shared by the DEX intent auth message hash and the burn
            // receipt body hash (Phase F).
            Some("domain_json_hash") => {
                if let Some(reason) = first_unknown_field(
                    obj.keys().map(String::as_str),
                    &["op", "label", "version", "value"],
                ) {
                    results.push(err_case(index, &reason));
                    continue;
                }
                let label = match obj.get("label").and_then(Value::as_str) {
                    Some(s) => s,
                    None => {
                        results.push(err_case(index, "malformed_case"));
                        continue;
                    }
                };
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
                let mut msg = match try_domain_sep_bytes(label, version) {
                    Ok(msg) => msg,
                    Err(e) => {
                        results.push(err_case(index, e.code()));
                        continue;
                    }
                };
                let value = obj.get("value").unwrap_or(&Value::Null);
                match lower_value(value) {
                    Ok(jv) => {
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
const EXACT_OUT_FIELDS: [&str; 5] = [
    "kind",
    "zero_for_one",
    "amount_out",
    "max_amount_in",
    "max_overdelivery_gap_bps",
];
const CPMM_POOL_FIELDS: [&str; 4] = ["initialized", "reserve0", "reserve1", "fee_bps"];

/// Present integer-shaped field as a literal string, else `None` (missing/non-int).
fn int_field(obj: &serde_json::Map<String, Value>, key: &str) -> Option<String> {
    obj.get(key).and_then(classify_integer)
}

/// Parse to u128, saturating negatives/oversized to `u128::MAX` so the kernel's
/// range checks reject them at the same boundary as the Python authority.
fn u128_sat(s: &str) -> u128 {
    s.parse::<u128>().unwrap_or(u128::MAX)
}

fn apply_cpmm_tx(
    pool: &Pool,
    tx: &Value,
) -> Result<zenodex_runtime_core::cpmm_swap::Accepted, String> {
    let obj = match tx.as_object() {
        Some(o) => o,
        None => return Err("malformed_tx".to_string()),
    };
    let kind = obj.get("kind").and_then(Value::as_str).unwrap_or("");
    let allowed: &[&str] = match kind {
        "init_pool" => &INIT_FIELDS,
        "swap_exact_in" => &EXACT_IN_FIELDS,
        "swap_exact_out" => &EXACT_OUT_FIELDS,
        _ => return Err("unknown_tx_kind".to_string()),
    };
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), allowed) {
        return Err(reason);
    }

    let result = match kind {
        "init_pool" => {
            // `already_initialized` precedes field validation (mirrors the harness).
            if pool.initialized {
                return Err("already_initialized".to_string());
            }
            let (r0, r1, fee) = match (
                int_field(obj, "reserve0"),
                int_field(obj, "reserve1"),
                int_field(obj, "fee_bps"),
            ) {
                (Some(a), Some(b), Some(c)) => (a, b, c),
                _ => return Err("malformed_tx".to_string()),
            };
            // Reserves and fee carry their own out-of-domain reject codes.
            let reserve0 = match r0.parse::<u128>() {
                Ok(v) if (1..=DEX_POOL_RESERVE_MAX).contains(&v) => v,
                _ => return Err("invalid_reserve".to_string()),
            };
            let reserve1 = match r1.parse::<u128>() {
                Ok(v) if (1..=DEX_POOL_RESERVE_MAX).contains(&v) => v,
                _ => return Err("invalid_reserve".to_string()),
            };
            let fee_bps = match fee.parse::<u128>() {
                Ok(v) if v <= BPS_DENOM => v,
                _ => return Err("invalid_fee_bps".to_string()),
            };
            init_pool(pool, reserve0, reserve1, fee_bps)
        }
        "swap_exact_in" => {
            let zero_for_one = match obj.get("zero_for_one").and_then(Value::as_bool) {
                Some(b) => b,
                None => return Err("malformed_tx".to_string()),
            };
            let amount_in = match int_field(obj, "amount_in") {
                Some(s) => u128_sat(&s),
                None => return Err("malformed_tx".to_string()),
            };
            let min_out = match int_field(obj, "min_amount_out") {
                Some(s) if !s.starts_with('-') => u128_sat(&s),
                _ => return Err("malformed_tx".to_string()),
            };
            swap_exact_in(pool, zero_for_one, amount_in, min_out)
        }
        "swap_exact_out" => {
            let zero_for_one = match obj.get("zero_for_one").and_then(Value::as_bool) {
                Some(b) => b,
                None => return Err("malformed_tx".to_string()),
            };
            let amount_out = match int_field(obj, "amount_out") {
                Some(s) => u128_sat(&s),
                None => return Err("malformed_tx".to_string()),
            };
            let max_in = match int_field(obj, "max_amount_in") {
                Some(s) if !s.starts_with('-') => u128_sat(&s),
                _ => return Err("malformed_tx".to_string()),
            };
            let max_gap_bps = match int_field(obj, "max_overdelivery_gap_bps") {
                Some(s) if !s.starts_with('-') => u128_sat(&s),
                None => CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
                _ => return Err("malformed_tx".to_string()),
            };
            swap_exact_out_with_max_gap_bps(pool, zero_for_one, amount_out, max_in, max_gap_bps)
        }
        _ => unreachable!(),
    };

    result.map_err(str::to_string)
}

fn eval_cpmm_tx(pool: &Pool, tx: &Value) -> Eval<Pool> {
    let result = apply_cpmm_tx(pool, tx);
    match result {
        Ok(accepted) => Eval::Accept {
            receipt_hash: accepted.receipt.receipt_hash(),
            next: accepted.pool,
        },
        Err(code) => Eval::Reject(code),
    }
}

fn cpmm_pool_out(pool: &Pool) -> CpmmPoolOut {
    CpmmPoolOut {
        initialized: pool.initialized,
        reserve0: pool.reserve0.to_string(),
        reserve1: pool.reserve1.to_string(),
        fee_bps: pool.fee_bps.to_string(),
    }
}

fn cpmm_receipt_out(r: &SwapReceipt) -> CpmmReceiptOut {
    let kind = match r.kind {
        zenodex_runtime_core::cpmm_swap::SwapKind::InitPool => "init_pool",
        zenodex_runtime_core::cpmm_swap::SwapKind::ExactIn => "swap_exact_in",
        zenodex_runtime_core::cpmm_swap::SwapKind::ExactOut => "swap_exact_out",
    };
    CpmmReceiptOut {
        kind: kind.to_string(),
        zero_for_one: r.zero_for_one,
        amount_in: r.amount_in.to_string(),
        amount_out: r.amount_out.to_string(),
        fee_total: r.fee_total.to_string(),
        amount_out_quote: r.amount_out_quote.to_string(),
        overdelivery_gap: r.overdelivery_gap.to_string(),
        gap_bps: r.gap_bps.to_string(),
        new_reserve0: r.new_reserve0.to_string(),
        new_reserve1: r.new_reserve1.to_string(),
    }
}

fn cpmm_pool_from_request(v: &Value) -> Result<Pool, String> {
    let obj = v
        .get("pool")
        .and_then(Value::as_object)
        .ok_or_else(|| "pool must be an object".to_string())?;
    if let Some(reason) = first_unknown_field(obj.keys().map(String::as_str), &CPMM_POOL_FIELDS) {
        return Err(reason);
    }
    let initialized = obj
        .get("initialized")
        .and_then(Value::as_bool)
        .ok_or_else(|| "pool.initialized must be a bool".to_string())?;
    let reserve0 = match obj.get("reserve0").and_then(classify_integer) {
        Some(s) if !s.starts_with('-') => s
            .parse::<u128>()
            .map_err(|_| "pool.reserve0 invalid_reserve".to_string())?,
        _ => return Err("pool.reserve0 invalid_reserve".to_string()),
    };
    let reserve1 = match obj.get("reserve1").and_then(classify_integer) {
        Some(s) if !s.starts_with('-') => s
            .parse::<u128>()
            .map_err(|_| "pool.reserve1 invalid_reserve".to_string())?,
        _ => return Err("pool.reserve1 invalid_reserve".to_string()),
    };
    let fee_bps = match obj.get("fee_bps").and_then(classify_integer) {
        Some(s) if !s.starts_with('-') => s
            .parse::<u128>()
            .map_err(|_| "pool.fee_bps invalid_fee_bps".to_string())?,
        _ => return Err("pool.fee_bps invalid_fee_bps".to_string()),
    };
    if initialized {
        if !(1..=DEX_POOL_RESERVE_MAX).contains(&reserve0)
            || !(1..=DEX_POOL_RESERVE_MAX).contains(&reserve1)
        {
            return Err("pool.reserve invalid_reserve".to_string());
        }
        if fee_bps > BPS_DENOM {
            return Err("pool.fee_bps invalid_fee_bps".to_string());
        }
    } else if reserve0 != 0 || reserve1 != 0 || fee_bps != 0 {
        return Err("pool.uninitialized_nonzero".to_string());
    }
    Ok(Pool {
        initialized,
        reserve0,
        reserve1,
        fee_bps,
    })
}

fn rejected_cpmm_output(pool: &Pool, pre_state_root: String, reason: String) -> CpmmOpOutput {
    CpmmOpOutput {
        version: 1,
        kernel: "cpmm_settlement".to_string(),
        accept: false,
        reject_reason: Some(reason),
        receipt_hash: None,
        receipt: None,
        pre_state_root: pre_state_root.clone(),
        post_state_root: pre_state_root,
        post_pool: cpmm_pool_out(pool),
    }
}

fn run_cpmm_op(request: &Value) -> Result<CpmmOpOutput, String> {
    let obj = request
        .as_object()
        .ok_or_else(|| "request must be an object".to_string())?;
    if let Some(reason) =
        first_unknown_field(obj.keys().map(String::as_str), &["version", "pool", "tx"])
    {
        return Err(reason);
    }
    if request.get("version").and_then(Value::as_u64).unwrap_or(1) != 1 {
        return Err("unsupported request version".to_string());
    }
    let pool = cpmm_pool_from_request(request)?;
    let pre_state_root = pool.state_root();
    let tx = request
        .get("tx")
        .ok_or_else(|| "tx is required".to_string())?;
    match apply_cpmm_tx(&pool, tx) {
        Ok(accepted) => {
            let receipt_hash = accepted.receipt.receipt_hash();
            Ok(CpmmOpOutput {
                version: 1,
                kernel: "cpmm_settlement".to_string(),
                accept: true,
                reject_reason: None,
                receipt_hash: Some(receipt_hash),
                receipt: Some(cpmm_receipt_out(&accepted.receipt)),
                pre_state_root,
                post_state_root: accepted.pool.state_root(),
                post_pool: cpmm_pool_out(&accepted.pool),
            })
        }
        Err(reason) => Ok(rejected_cpmm_output(&pool, pre_state_root, reason)),
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
    let cases = cases_array(req)?;
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

/// Optional magnitude: `None` if the key is absent, else the parsed `arg_mag`.
fn arg_mag_opt(obj: &serde_json::Map<String, Value>, key: &str) -> Result<Option<i128>, String> {
    if obj.contains_key(key) {
        Ok(Some(arg_mag(obj, key)?))
    } else {
        Ok(None)
    }
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
    let cases = cases_array(req)?;
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

// --- advance_epoch shadow (stateful perps E2 slice) ---------------------------

#[derive(Serialize)]
struct AdvanceEpochCaseResult {
    index: usize,
    ok: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    now_epoch: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    epoch_phase: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    oracle_last_update_epoch: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
}

#[derive(Serialize)]
struct AdvanceEpochOutputDoc {
    version: u32,
    results: Vec<AdvanceEpochCaseResult>,
}

fn advance_epoch_err(index: usize, code: &str) -> AdvanceEpochCaseResult {
    AdvanceEpochCaseResult {
        index,
        ok: false,
        now_epoch: None,
        epoch_phase: None,
        oracle_last_update_epoch: None,
        code: Some(code.to_string()),
    }
}

fn eval_advance_epoch_case(
    obj: &serde_json::Map<String, Value>,
) -> Result<AdvanceEpochCaseResult, String> {
    let input = AdvanceEpochInput {
        now_epoch: arg_mag(obj, "now_epoch")?,
        epoch_phase: arg_mag(obj, "epoch_phase")?,
        oracle_last_update_epoch: arg_mag(obj, "oracle_last_update_epoch")?,
        delta: arg_mag(obj, "delta")?,
    };
    match advance_epoch(&input) {
        Ok(out) => Ok(AdvanceEpochCaseResult {
            index: 0,
            ok: true,
            now_epoch: Some(out.now_epoch.to_string()),
            epoch_phase: Some(out.epoch_phase.to_string()),
            oracle_last_update_epoch: Some(out.oracle_last_update_epoch.to_string()),
            code: None,
        }),
        Err(code) => Ok(advance_epoch_err(0, code)),
    }
}

fn run_advance_epoch_cases(req: &Value) -> Result<AdvanceEpochOutputDoc, String> {
    let cases = cases_array(req)?;
    let mut results = Vec::with_capacity(cases.len());
    for (index, case) in cases.iter().enumerate() {
        let result = match case.as_object() {
            Some(obj) => match eval_advance_epoch_case(obj) {
                Ok(mut r) => {
                    r.index = index;
                    r
                }
                Err(code) => advance_epoch_err(index, &code),
            },
            None => advance_epoch_err(index, "malformed_case"),
        };
        results.push(result);
    }
    Ok(AdvanceEpochOutputDoc {
        version: 1,
        results,
    })
}

// --- publish_clearing_price shadow (stateful perps E2 slice) ------------------

#[derive(Serialize)]
struct PublishClearingPriceCaseResult {
    index: usize,
    ok: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    now_epoch: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    epoch_phase: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    clearing_price_seen: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    clearing_price_epoch: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    clearing_price_e8: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
}

#[derive(Serialize)]
struct PublishClearingPriceOutputDoc {
    version: u32,
    results: Vec<PublishClearingPriceCaseResult>,
}

fn publish_clearing_price_err(index: usize, code: &str) -> PublishClearingPriceCaseResult {
    PublishClearingPriceCaseResult {
        index,
        ok: false,
        now_epoch: None,
        epoch_phase: None,
        clearing_price_seen: None,
        clearing_price_epoch: None,
        clearing_price_e8: None,
        code: Some(code.to_string()),
    }
}

fn eval_publish_clearing_price_case(
    obj: &serde_json::Map<String, Value>,
) -> Result<PublishClearingPriceCaseResult, String> {
    let input = PublishClearingPriceInput {
        now_epoch: arg_mag(obj, "now_epoch")?,
        epoch_phase: arg_mag(obj, "epoch_phase")?,
        clearing_price_seen: arg_bool(obj, "clearing_price_seen")?,
        clearing_price_epoch: arg_mag(obj, "clearing_price_epoch")?,
        clearing_price_e8: arg_mag(obj, "clearing_price_e8")?,
        oracle_last_update_epoch: arg_mag(obj, "oracle_last_update_epoch")?,
        price_e8: arg_mag(obj, "price_e8")?,
    };
    match publish_clearing_price(&input) {
        Ok(out) => Ok(PublishClearingPriceCaseResult {
            index: 0,
            ok: true,
            now_epoch: Some(out.now_epoch.to_string()),
            epoch_phase: Some(out.epoch_phase.to_string()),
            clearing_price_seen: Some(out.clearing_price_seen),
            clearing_price_epoch: Some(out.clearing_price_epoch.to_string()),
            clearing_price_e8: Some(out.clearing_price_e8.to_string()),
            code: None,
        }),
        Err(code) => Ok(publish_clearing_price_err(0, code)),
    }
}

fn run_publish_clearing_price_cases(req: &Value) -> Result<PublishClearingPriceOutputDoc, String> {
    let cases = cases_array(req)?;
    let mut results = Vec::with_capacity(cases.len());
    for (index, case) in cases.iter().enumerate() {
        let result = match case.as_object() {
            Some(obj) => match eval_publish_clearing_price_case(obj) {
                Ok(mut r) => {
                    r.index = index;
                    r
                }
                Err(code) => publish_clearing_price_err(index, &code),
            },
            None => publish_clearing_price_err(index, "malformed_case"),
        };
        results.push(result);
    }
    Ok(PublishClearingPriceOutputDoc {
        version: 1,
        results,
    })
}

// --- settle_epoch shadow (stateful perps E2 slice) ----------------------------

#[derive(Serialize)]
struct SettleAccountOut {
    key: String,
    position_base: String,
    collateral_quote: String,
    entry_price_e8: String,
    liquidated_this_step: bool,
}

#[derive(Serialize)]
struct SettleEpochCaseResult {
    index: usize,
    ok: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    epoch_phase: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    oracle_last_update_epoch: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    oracle_seen: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    index_price_e8: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    breaker_active: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    breaker_last_trigger_epoch: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    fee_pool_quote: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    fee_income: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    insurance_balance: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    accounts: Option<Vec<SettleAccountOut>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
}

#[derive(Serialize)]
struct SettleEpochOutputDoc {
    version: u32,
    results: Vec<SettleEpochCaseResult>,
}

fn settle_epoch_err(index: usize, code: &str) -> SettleEpochCaseResult {
    SettleEpochCaseResult {
        index,
        ok: false,
        epoch_phase: None,
        oracle_last_update_epoch: None,
        oracle_seen: None,
        index_price_e8: None,
        breaker_active: None,
        breaker_last_trigger_epoch: None,
        fee_pool_quote: None,
        fee_income: None,
        insurance_balance: None,
        accounts: None,
        code: Some(code.to_string()),
    }
}

fn eval_settle_epoch_case(
    obj: &serde_json::Map<String, Value>,
) -> Result<SettleEpochCaseResult, String> {
    let accounts_val = obj
        .get("accounts")
        .and_then(Value::as_array)
        .ok_or("malformed_case")?;
    let mut accounts = Vec::with_capacity(accounts_val.len());
    for av in accounts_val {
        let ao = av.as_object().ok_or("malformed_case")?;
        let key = ao
            .get("key")
            .and_then(Value::as_str)
            .ok_or("malformed_case")?
            .to_string();
        accounts.push(SettleAccount {
            key,
            position_base: arg_mag(ao, "position_base")?,
            collateral_quote: arg_mag(ao, "collateral_quote")?,
            entry_price_e8: arg_mag(ao, "entry_price_e8")?,
            liquidated_this_step: arg_bool(ao, "liquidated_this_step")?,
        });
    }

    let input = SettleEpochInput {
        now_epoch: arg_mag(obj, "now_epoch")?,
        epoch_phase: arg_mag(obj, "epoch_phase")?,
        clearing_price_seen: arg_bool(obj, "clearing_price_seen")?,
        clearing_price_epoch: arg_mag(obj, "clearing_price_epoch")?,
        clearing_price_e8: arg_mag(obj, "clearing_price_e8")?,
        oracle_last_update_epoch: arg_mag(obj, "oracle_last_update_epoch")?,
        oracle_seen: arg_bool(obj, "oracle_seen")?,
        index_price_e8: arg_mag(obj, "index_price_e8")?,
        max_oracle_move_bps: arg_bps(obj, "max_oracle_move_bps")?,
        maintenance_margin_bps: arg_bps(obj, "maintenance_margin_bps")?,
        depeg_buffer_bps: arg_bps(obj, "depeg_buffer_bps")?,
        liquidation_penalty_bps: arg_bps(obj, "liquidation_penalty_bps")?,
        min_notional_for_bounty: arg_mag(obj, "min_notional_for_bounty")?,
        fee_pool_quote: arg_mag(obj, "fee_pool_quote")?,
        fee_income: arg_mag(obj, "fee_income")?,
        initial_insurance: arg_mag(obj, "initial_insurance")?,
        claims_paid: arg_mag(obj, "claims_paid")?,
        breaker_active: arg_bool(obj, "breaker_active")?,
        breaker_last_trigger_epoch: arg_mag(obj, "breaker_last_trigger_epoch")?,
        accounts,
    };

    match settle_epoch(&input) {
        Ok(out) => Ok(SettleEpochCaseResult {
            index: 0,
            ok: true,
            epoch_phase: Some(out.epoch_phase.to_string()),
            oracle_last_update_epoch: Some(out.oracle_last_update_epoch.to_string()),
            oracle_seen: Some(out.oracle_seen),
            index_price_e8: Some(out.index_price_e8.to_string()),
            breaker_active: Some(out.breaker_active),
            breaker_last_trigger_epoch: Some(out.breaker_last_trigger_epoch.to_string()),
            fee_pool_quote: Some(out.fee_pool_quote.to_string()),
            fee_income: Some(out.fee_income.to_string()),
            insurance_balance: Some(out.insurance_balance.to_string()),
            accounts: Some(
                out.accounts
                    .iter()
                    .map(|a| SettleAccountOut {
                        key: a.key.clone(),
                        position_base: a.position_base.to_string(),
                        collateral_quote: a.collateral_quote.to_string(),
                        entry_price_e8: a.entry_price_e8.to_string(),
                        liquidated_this_step: a.liquidated_this_step,
                    })
                    .collect(),
            ),
            code: None,
        }),
        Err(code) => Ok(settle_epoch_err(0, code)),
    }
}

fn run_settle_epoch_cases(req: &Value) -> Result<SettleEpochOutputDoc, String> {
    let cases = cases_array(req)?;
    let mut results = Vec::with_capacity(cases.len());
    for (index, case) in cases.iter().enumerate() {
        let result = match case.as_object() {
            Some(obj) => match eval_settle_epoch_case(obj) {
                Ok(mut r) => {
                    r.index = index;
                    r
                }
                Err(code) => settle_epoch_err(index, &code),
            },
            None => settle_epoch_err(index, "malformed_case"),
        };
        results.push(result);
    }
    Ok(SettleEpochOutputDoc {
        version: 1,
        results,
    })
}

// --- partial_liquidate shadow (stateful perps E2 slice) -----------------------

#[derive(Serialize)]
struct PartialLiquidateCaseResult {
    index: usize,
    ok: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    position_base: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    entry_price_e8: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    collateral_quote: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    fee_pool_quote: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    fee_income: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    insurance_balance: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    liquidated_this_step: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
}

#[derive(Serialize)]
struct PartialLiquidateOutputDoc {
    version: u32,
    results: Vec<PartialLiquidateCaseResult>,
}

fn partial_liquidate_err(index: usize, code: &str) -> PartialLiquidateCaseResult {
    PartialLiquidateCaseResult {
        index,
        ok: false,
        position_base: None,
        entry_price_e8: None,
        collateral_quote: None,
        fee_pool_quote: None,
        fee_income: None,
        insurance_balance: None,
        liquidated_this_step: None,
        code: Some(code.to_string()),
    }
}

fn eval_partial_liquidate_case(
    obj: &serde_json::Map<String, Value>,
) -> Result<PartialLiquidateCaseResult, String> {
    let input = PartialLiquidateInput {
        now_epoch: arg_mag(obj, "now_epoch")?,
        epoch_phase: arg_mag(obj, "epoch_phase")?,
        oracle_last_update_epoch: arg_mag(obj, "oracle_last_update_epoch")?,
        max_oracle_staleness_epochs: arg_mag(obj, "max_oracle_staleness_epochs")?,
        oracle_seen: arg_bool(obj, "oracle_seen")?,
        index_price_e8: arg_mag(obj, "index_price_e8")?,
        position_base: arg_mag(obj, "position_base")?,
        collateral_quote: arg_mag(obj, "collateral_quote")?,
        entry_price_e8: arg_mag(obj, "entry_price_e8")?,
        maintenance_margin_bps: arg_bps(obj, "maintenance_margin_bps")?,
        depeg_buffer_bps: arg_bps(obj, "depeg_buffer_bps")?,
        liquidation_penalty_bps: arg_bps(obj, "liquidation_penalty_bps")?,
        min_notional_for_bounty: arg_mag(obj, "min_notional_for_bounty")?,
        fee_pool_quote: arg_mag(obj, "fee_pool_quote")?,
        fee_income: arg_mag(obj, "fee_income")?,
        initial_insurance: arg_mag(obj, "initial_insurance")?,
        claims_paid: arg_mag(obj, "claims_paid")?,
        fraction_bps: arg_mag(obj, "fraction_bps")?,
    };
    match partial_liquidate(&input) {
        Ok(out) => Ok(PartialLiquidateCaseResult {
            index: 0,
            ok: true,
            position_base: Some(out.position_base.to_string()),
            entry_price_e8: Some(out.entry_price_e8.to_string()),
            collateral_quote: Some(out.collateral_quote.to_string()),
            fee_pool_quote: Some(out.fee_pool_quote.to_string()),
            fee_income: Some(out.fee_income.to_string()),
            insurance_balance: Some(out.insurance_balance.to_string()),
            liquidated_this_step: Some(out.liquidated_this_step),
            code: None,
        }),
        Err(code) => Ok(partial_liquidate_err(0, code)),
    }
}

fn run_partial_liquidate_cases(req: &Value) -> Result<PartialLiquidateOutputDoc, String> {
    let cases = cases_array(req)?;
    let mut results = Vec::with_capacity(cases.len());
    for (index, case) in cases.iter().enumerate() {
        let result = match case.as_object() {
            Some(obj) => match eval_partial_liquidate_case(obj) {
                Ok(mut r) => {
                    r.index = index;
                    r
                }
                Err(code) => partial_liquidate_err(index, &code),
            },
            None => partial_liquidate_err(index, "malformed_case"),
        };
        results.push(result);
    }
    Ok(PartialLiquidateOutputDoc {
        version: 1,
        results,
    })
}

// --- account-management ops shadow (stateful perps E2 slice) ------------------

#[derive(Serialize)]
struct AccountOpCaseResult {
    index: usize,
    ok: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    position_base: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    entry_price_e8: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    collateral_quote: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    breaker_active: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    breaker_last_trigger_epoch: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
}

#[derive(Serialize)]
struct AccountOpOutputDoc {
    version: u32,
    results: Vec<AccountOpCaseResult>,
}

fn account_op_err(index: usize, code: &str) -> AccountOpCaseResult {
    AccountOpCaseResult {
        index,
        ok: false,
        position_base: None,
        entry_price_e8: None,
        collateral_quote: None,
        breaker_active: None,
        breaker_last_trigger_epoch: None,
        code: Some(code.to_string()),
    }
}

fn eval_account_op_case(
    obj: &serde_json::Map<String, Value>,
) -> Result<AccountOpCaseResult, String> {
    let op = obj
        .get("op")
        .and_then(Value::as_str)
        .ok_or("malformed_case")?
        .to_string();
    let input = AccountOpInput {
        now_epoch: arg_mag(obj, "now_epoch")?,
        epoch_phase: arg_mag(obj, "epoch_phase")?,
        oracle_last_update_epoch: arg_mag(obj, "oracle_last_update_epoch")?,
        max_oracle_staleness_epochs: arg_mag(obj, "max_oracle_staleness_epochs")?,
        oracle_seen: arg_bool(obj, "oracle_seen")?,
        index_price_e8: arg_mag(obj, "index_price_e8")?,
        position_base: arg_mag(obj, "position_base")?,
        collateral_quote: arg_mag(obj, "collateral_quote")?,
        entry_price_e8: arg_mag(obj, "entry_price_e8")?,
        maintenance_margin_bps: arg_bps(obj, "maintenance_margin_bps")?,
        depeg_buffer_bps: arg_bps(obj, "depeg_buffer_bps")?,
        initial_margin_bps: arg_bps(obj, "initial_margin_bps")?,
        max_position_abs: arg_mag(obj, "max_position_abs")?,
        breaker_active: arg_bool(obj, "breaker_active")?,
        breaker_last_trigger_epoch: arg_mag(obj, "breaker_last_trigger_epoch")?,
        amount: arg_mag(obj, "amount")?,
        new_position_base: arg_mag(obj, "new_position_base")?,
        all_positions_flat: arg_bool(obj, "all_positions_flat")?,
    };
    match account_op(&op, &input) {
        Ok(out) => Ok(AccountOpCaseResult {
            index: 0,
            ok: true,
            position_base: Some(out.position_base.to_string()),
            entry_price_e8: Some(out.entry_price_e8.to_string()),
            collateral_quote: Some(out.collateral_quote.to_string()),
            breaker_active: Some(out.breaker_active),
            breaker_last_trigger_epoch: Some(out.breaker_last_trigger_epoch.to_string()),
            code: None,
        }),
        Err(code) => Ok(account_op_err(0, code)),
    }
}

fn run_account_op_cases(req: &Value) -> Result<AccountOpOutputDoc, String> {
    let cases = cases_array(req)?;
    let mut results = Vec::with_capacity(cases.len());
    for (index, case) in cases.iter().enumerate() {
        let result = match case.as_object() {
            Some(obj) => match eval_account_op_case(obj) {
                Ok(mut r) => {
                    r.index = index;
                    r
                }
                Err(code) => account_op_err(index, &code),
            },
            None => account_op_err(index, "malformed_case"),
        };
        results.push(result);
    }
    Ok(AccountOpOutputDoc {
        version: 1,
        results,
    })
}

// --- set_market_params shadow (stateful perps E2 slice) -----------------------

#[derive(Serialize)]
struct SetMarketParamsCaseResult {
    index: usize,
    ok: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    max_oracle_staleness_epochs: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    max_oracle_move_bps: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    initial_margin_bps: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    maintenance_margin_bps: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    depeg_buffer_bps: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    liquidation_penalty_bps: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    max_position_abs: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    funding_cap_bps: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    min_notional_for_bounty: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    funding_rate_bps: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
}

#[derive(Serialize)]
struct SetMarketParamsOutputDoc {
    version: u32,
    results: Vec<SetMarketParamsCaseResult>,
}

fn set_market_params_err(index: usize, code: &str) -> SetMarketParamsCaseResult {
    SetMarketParamsCaseResult {
        index,
        ok: false,
        max_oracle_staleness_epochs: None,
        max_oracle_move_bps: None,
        initial_margin_bps: None,
        maintenance_margin_bps: None,
        depeg_buffer_bps: None,
        liquidation_penalty_bps: None,
        max_position_abs: None,
        funding_cap_bps: None,
        min_notional_for_bounty: None,
        funding_rate_bps: None,
        code: Some(code.to_string()),
    }
}

fn eval_set_market_params_case(
    obj: &serde_json::Map<String, Value>,
) -> Result<SetMarketParamsCaseResult, String> {
    let accounts_val = obj
        .get("accounts")
        .and_then(Value::as_array)
        .ok_or("malformed_case")?;
    let mut accounts = Vec::with_capacity(accounts_val.len());
    for av in accounts_val {
        let ao = av.as_object().ok_or("malformed_case")?;
        accounts.push(MarketParamsAccount {
            position_base: arg_mag(ao, "position_base")?,
            collateral_quote: arg_mag(ao, "collateral_quote")?,
        });
    }
    let input = SetMarketParamsInput {
        cur_max_oracle_staleness_epochs: arg_mag(obj, "cur_max_oracle_staleness_epochs")?,
        cur_max_oracle_move_bps: arg_mag(obj, "cur_max_oracle_move_bps")?,
        cur_initial_margin_bps: arg_mag(obj, "cur_initial_margin_bps")?,
        cur_maintenance_margin_bps: arg_mag(obj, "cur_maintenance_margin_bps")?,
        cur_depeg_buffer_bps: arg_mag(obj, "cur_depeg_buffer_bps")?,
        cur_liquidation_penalty_bps: arg_mag(obj, "cur_liquidation_penalty_bps")?,
        cur_max_position_abs: arg_mag(obj, "cur_max_position_abs")?,
        cur_funding_cap_bps: arg_mag(obj, "cur_funding_cap_bps")?,
        cur_min_notional_for_bounty: arg_mag(obj, "cur_min_notional_for_bounty")?,
        cur_funding_rate_bps: arg_mag(obj, "cur_funding_rate_bps")?,
        index_price_e8: arg_mag(obj, "index_price_e8")?,
        min_collectible_liquidation_penalty_quote: arg_mag(
            obj,
            "min_collectible_liquidation_penalty_quote",
        )?,
        upd_max_oracle_staleness_epochs: arg_mag_opt(obj, "upd_max_oracle_staleness_epochs")?,
        upd_max_oracle_move_bps: arg_mag_opt(obj, "upd_max_oracle_move_bps")?,
        upd_initial_margin_bps: arg_mag_opt(obj, "upd_initial_margin_bps")?,
        upd_maintenance_margin_bps: arg_mag_opt(obj, "upd_maintenance_margin_bps")?,
        upd_depeg_buffer_bps: arg_mag_opt(obj, "upd_depeg_buffer_bps")?,
        upd_liquidation_penalty_bps: arg_mag_opt(obj, "upd_liquidation_penalty_bps")?,
        upd_max_position_abs: arg_mag_opt(obj, "upd_max_position_abs")?,
        upd_funding_cap_bps: arg_mag_opt(obj, "upd_funding_cap_bps")?,
        upd_min_notional_for_bounty: arg_mag_opt(obj, "upd_min_notional_for_bounty")?,
        accounts,
    };
    match set_market_params(&input) {
        Ok(out) => Ok(SetMarketParamsCaseResult {
            index: 0,
            ok: true,
            max_oracle_staleness_epochs: Some(out.max_oracle_staleness_epochs.to_string()),
            max_oracle_move_bps: Some(out.max_oracle_move_bps.to_string()),
            initial_margin_bps: Some(out.initial_margin_bps.to_string()),
            maintenance_margin_bps: Some(out.maintenance_margin_bps.to_string()),
            depeg_buffer_bps: Some(out.depeg_buffer_bps.to_string()),
            liquidation_penalty_bps: Some(out.liquidation_penalty_bps.to_string()),
            max_position_abs: Some(out.max_position_abs.to_string()),
            funding_cap_bps: Some(out.funding_cap_bps.to_string()),
            min_notional_for_bounty: Some(out.min_notional_for_bounty.to_string()),
            funding_rate_bps: Some(out.funding_rate_bps.to_string()),
            code: None,
        }),
        Err(code) => Ok(set_market_params_err(0, code)),
    }
}

fn run_set_market_params_cases(req: &Value) -> Result<SetMarketParamsOutputDoc, String> {
    let cases = cases_array(req)?;
    let mut results = Vec::with_capacity(cases.len());
    for (index, case) in cases.iter().enumerate() {
        let result = match case.as_object() {
            Some(obj) => match eval_set_market_params_case(obj) {
                Ok(mut r) => {
                    r.index = index;
                    r
                }
                Err(code) => set_market_params_err(index, &code),
            },
            None => set_market_params_err(index, "malformed_case"),
        };
        results.push(result);
    }
    Ok(SetMarketParamsOutputDoc {
        version: 1,
        results,
    })
}

// --- funding-auto settlement shadow (stateful perps E2 slice) ----------------

#[derive(Serialize)]
struct FundingAutoAccountOut {
    key: String,
    position_base: String,
    collateral_quote: String,
    funding_paid_cumulative: String,
    funding_last_applied_epoch: String,
}

#[derive(Serialize)]
struct FundingAutoCaseResult {
    index: usize,
    ok: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    accounts: Option<Vec<FundingAutoAccountOut>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    funding_rate_bps: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    fee_pool_quote: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    fee_income: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    insurance_balance: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    projected_net: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    code: Option<String>,
}

#[derive(Serialize)]
struct FundingAutoOutputDoc {
    version: u32,
    results: Vec<FundingAutoCaseResult>,
}

fn funding_err(index: usize, code: &str) -> FundingAutoCaseResult {
    FundingAutoCaseResult {
        index,
        ok: false,
        accounts: None,
        funding_rate_bps: None,
        fee_pool_quote: None,
        fee_income: None,
        insurance_balance: None,
        projected_net: None,
        code: Some(code.to_string()),
    }
}

fn eval_funding_auto_case(
    obj: &serde_json::Map<String, Value>,
) -> Result<FundingAutoCaseResult, String> {
    let now_epoch = arg_mag(obj, "now_epoch")?;
    let rate_bps = arg_bps(obj, "rate_bps")?;
    let index_price_e8 = arg_mag(obj, "index_price_e8")?;
    let maintenance_margin_bps = arg_bps(obj, "maintenance_margin_bps")?;
    let depeg_buffer_bps = arg_bps(obj, "depeg_buffer_bps")?;
    let fee_pool_quote = arg_mag(obj, "fee_pool_quote")?;
    let fee_income = arg_mag(obj, "fee_income")?;
    let insurance_balance = arg_mag(obj, "insurance_balance")?;

    let accounts_val = obj
        .get("accounts")
        .and_then(Value::as_array)
        .ok_or("malformed_case")?;
    let mut accounts = Vec::with_capacity(accounts_val.len());
    for av in accounts_val {
        let ao = av.as_object().ok_or("malformed_case")?;
        let key = ao
            .get("key")
            .and_then(Value::as_str)
            .ok_or("malformed_case")?
            .to_string();
        accounts.push(FundingAccount {
            key,
            position_base: arg_mag(ao, "position_base")?,
            collateral_quote: arg_mag(ao, "collateral_quote")?,
            funding_paid_cumulative: arg_mag(ao, "funding_paid_cumulative")?,
            funding_last_applied_epoch: arg_mag(ao, "funding_last_applied_epoch")?,
        });
    }

    let input = FundingAutoInput {
        accounts,
        now_epoch,
        rate_bps,
        index_price_e8,
        maintenance_margin_bps,
        depeg_buffer_bps,
        fee_pool_quote,
        fee_income,
        insurance_balance,
    };

    match apply_funding_auto(&input) {
        Ok(out) => Ok(FundingAutoCaseResult {
            index: 0,
            ok: true,
            accounts: Some(
                out.accounts
                    .iter()
                    .map(|a| FundingAutoAccountOut {
                        key: a.key.clone(),
                        position_base: a.position_base.to_string(),
                        collateral_quote: a.collateral_quote.to_string(),
                        funding_paid_cumulative: a.funding_paid_cumulative.to_string(),
                        funding_last_applied_epoch: a.funding_last_applied_epoch.to_string(),
                    })
                    .collect(),
            ),
            funding_rate_bps: Some(out.funding_rate_bps.to_string()),
            fee_pool_quote: Some(out.fee_pool_quote.to_string()),
            fee_income: Some(out.fee_income.to_string()),
            insurance_balance: Some(out.insurance_balance.to_string()),
            projected_net: Some(out.projected_net.to_string()),
            code: None,
        }),
        Err(code) => Ok(funding_err(0, code)),
    }
}

fn run_funding_auto_cases(req: &Value) -> Result<FundingAutoOutputDoc, String> {
    let cases = cases_array(req)?;
    let mut results = Vec::with_capacity(cases.len());
    for (index, case) in cases.iter().enumerate() {
        let result = match case.as_object() {
            Some(obj) => match eval_funding_auto_case(obj) {
                Ok(mut r) => {
                    r.index = index;
                    r
                }
                Err(code) => funding_err(index, &code),
            },
            None => funding_err(index, "malformed_case"),
        };
        results.push(result);
    }
    Ok(FundingAutoOutputDoc {
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
                | "fee-route"
                | "replay-guard-trace"
                | "replay-guard-admit"
                | "replay-balance-trace"
                | "balance-op"
                | "replay-zusd-trace"
                | "zusd-op"
                | "verify-burn-trace"
                | "settle-swap-trace"
                | "cpmm-op"
                | "canonical-hash"
                | "verify-state-root"
                | "perp-math"
                | "advance-epoch"
                | "funding-auto"
                | "publish-clearing-price"
                | "settle-epoch"
                | "partial-liquidate"
                | "account-op"
                | "set-market-params"
                | "perp-isolated-op"
        )
    {
        eprintln!(
            "usage: {prog} <replay-fee-trace|replay-guard-trace|replay-guard-admit|\
             fee-route|replay-balance-trace|balance-op|\
             replay-zusd-trace|zusd-op|verify-burn-trace|settle-swap-trace|cpmm-op|canonical-hash|\
             verify-state-root|perp-math|advance-epoch|funding-auto|\
             publish-clearing-price|settle-epoch|partial-liquidate|account-op|\
             set-market-params|perp-isolated-op> <input.json|->"
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

    if subcommand == "fee-route" {
        return match run_fee_route(&trace) {
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

    if subcommand == "replay-guard-admit" {
        return match run_replay_guard_admit(&trace) {
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

    if subcommand == "balance-op" {
        return match run_balance_op(&trace) {
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

    if subcommand == "zusd-op" {
        return match run_zusd_op(&trace) {
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

    if subcommand == "cpmm-op" {
        return match run_cpmm_op(&trace) {
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

    if subcommand == "perp-isolated-op" {
        let out = perp_isolated_op::materialize_isolated_op(&trace);
        return match serde_json::to_string(&out) {
            Ok(s) => {
                println!("{s}");
                ExitCode::SUCCESS
            }
            Err(e) => {
                eprintln!("error: cannot serialize output: {e}");
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

    if subcommand == "funding-auto" {
        return match run_funding_auto_cases(&trace) {
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

    if subcommand == "advance-epoch" {
        return match run_advance_epoch_cases(&trace) {
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

    if subcommand == "publish-clearing-price" {
        return match run_publish_clearing_price_cases(&trace) {
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

    if subcommand == "settle-epoch" {
        return match run_settle_epoch_cases(&trace) {
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

    if subcommand == "partial-liquidate" {
        return match run_partial_liquidate_cases(&trace) {
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

    if subcommand == "account-op" {
        return match run_account_op_cases(&trace) {
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

    if subcommand == "set-market-params" {
        return match run_set_market_params_cases(&trace) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn request_with_extra_top_level_field() -> Value {
        json!({"cases": [], "debug": true})
    }

    fn assert_unknown_debug<T>(result: Result<T, String>) {
        match result {
            Ok(_) => panic!("request with unknown field unexpectedly accepted"),
            Err(err) => assert_eq!(err, "unknown_field:debug"),
        }
    }

    fn zusd_ready_state() -> Value {
        json!({
            "now_epoch": 0,
            "oracle_seen": true,
            "oracle_last_update_epoch": 0,
            "price_e8": 100_000_000,
            "price_pending_e8": 100_000_000,
            "max_oracle_staleness_epochs": 100,
            "collateral_e8": 100_000_000_000u64,
            "debt_e8": 0,
            "free_debt_e8": 0,
            "sp_debt_e8": 0,
            "sp_coll_e8": 0,
            "protocol_collateral_e8": 0,
            "protocol_revenue_zusd_cum_e8": 0,
            "liquidator_compensation_collateral_cum_e8": 0,
            "mcr_bps": 11_000,
            "ccr_bps": 15_000,
            "min_debt_open_e8": 10_000_000_000u64,
            "max_debt_e8": 1_000_000_000_000_000u64,
            "max_debt_supply_e8": 2_000_000_000_000_000u64,
            "max_sp_coll_e8": 2_000_000_000_000_000u64,
            "max_protocol_coll_e8": 2_000_000_000_000_000u64,
            "base_rate_bps": 0,
            "base_rate_last_epoch": 0,
            "base_rate_decay_per_epoch_bps": 0,
            "base_rate_borrow_bump_bps": 0,
            "base_rate_redeem_bump_bps": 0,
            "borrow_fee_floor_bps": 0,
            "borrow_fee_max_bps": 1_000,
            "redemption_fee_floor_bps": 0,
            "redemption_fee_max_bps": 1_000,
            "liquidation_gas_comp_fixed_collateral_e8": 0,
            "liquidation_gas_comp_bps": 0
        })
    }

    fn zusd_mint_request(require_oracle_authorization: bool, facts: Option<Value>) -> Value {
        let mut req = json!({
            "version": 1,
            "state": zusd_ready_state(),
            "tx": {
                "kind": "mint_zusd",
                "amount_e8": 20_000_000_000u64
            },
            "require_oracle_authorization": require_oracle_authorization
        });
        if let Some(facts) = facts {
            req.as_object_mut()
                .unwrap()
                .insert("facts".to_string(), facts);
        }
        req
    }

    fn zusd_mint_oracle_facts(runtime_value_e8: u64) -> Value {
        json!({
            "oracle_authorization_ok": true,
            "query_id": ZUSD_ORACLE_COLLATERAL_QUERY_ID,
            "action_kind": "mint",
            "runtime_value_e8": runtime_value_e8
        })
    }

    #[test]
    fn case_based_subcommands_reject_unknown_top_level_fields() {
        let req = request_with_extra_top_level_field();
        assert_unknown_debug(run_canonical_cases(&req));
        assert_unknown_debug(run_state_root_cases(&req));
        assert_unknown_debug(run_perp_math_cases(&req));
        assert_unknown_debug(run_advance_epoch_cases(&req));
        assert_unknown_debug(run_publish_clearing_price_cases(&req));
        assert_unknown_debug(run_settle_epoch_cases(&req));
        assert_unknown_debug(run_partial_liquidate_cases(&req));
        assert_unknown_debug(run_account_op_cases(&req));
        assert_unknown_debug(run_set_market_params_cases(&req));
        assert_unknown_debug(run_funding_auto_cases(&req));
    }

    #[test]
    fn canonical_case_rejects_unknown_operation_field() {
        let out = run_canonical_cases(&json!({
            "cases": [
                {
                    "op": "domain_json_hash",
                    "label": "dex_intent_sig:test",
                    "version": 1,
                    "value": {},
                    "debug": true
                }
            ]
        }))
        .unwrap();

        assert_eq!(out.version, 1);
        assert_eq!(out.results.len(), 1);
        assert!(!out.results[0].ok);
        assert_eq!(out.results[0].code.as_deref(), Some("unknown_field:debug"));
        assert!(out.results[0].hash.is_none());
    }

    #[test]
    fn zusd_prod_gate_rejects_mint_without_oracle_facts() {
        let out = run_zusd_op(&zusd_mint_request(true, None)).unwrap();
        assert!(!out.accept);
        assert_eq!(out.reject_reason.as_deref(), Some("oracle_facts_required"));
        assert_eq!(out.pre_state_root, out.post_state_root);
        assert!(out.receipt_hash.is_none());
    }

    #[test]
    fn zusd_prod_gate_rejects_self_attested_oracle_facts() {
        let out = run_zusd_op(&zusd_mint_request(
            true,
            Some(zusd_mint_oracle_facts(100_000_000)),
        ))
        .unwrap();
        assert!(!out.accept);
        assert_eq!(
            out.reject_reason.as_deref(),
            Some("oracle_authorization_external_required")
        );
        assert_eq!(out.pre_state_root, out.post_state_root);
    }

    #[test]
    fn zusd_prod_gate_rejects_mint_with_wrong_oracle_value() {
        let out = run_zusd_op(&zusd_mint_request(
            true,
            Some(zusd_mint_oracle_facts(100_000_001)),
        ))
        .unwrap();
        assert!(!out.accept);
        assert_eq!(
            out.reject_reason.as_deref(),
            Some("oracle_authorization_external_required")
        );
        assert_eq!(out.pre_state_root, out.post_state_root);
    }

    #[test]
    fn zusd_shadow_mode_keeps_accounting_replay_without_oracle_facts() {
        let out = run_zusd_op(&zusd_mint_request(false, None)).unwrap();
        assert!(out.accept, "{:?}", out.reject_reason);
        assert_eq!(out.post_state.debt_e8, "20000000000");
    }
}
