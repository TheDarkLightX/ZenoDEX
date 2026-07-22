//! zUSD issuance kernel — single-vault CDP accounting (mint / redeem / oracle).
//!
//! Rust shadow of the authoritative `src/core/zusd.py` (`step`, single-vault
//! model). Integer-only, deterministic, no I/O. The CDP ratio checks
//! (`collateral * price * bps` vs `debt * mcr * 1e8`) reach ~2^213 at the
//! authority's `MAX_AMOUNT_E8 = 1e30` bound — far beyond `u128` — so all
//! products are computed with `num_bigint::BigUint`, exactly mirroring Python's
//! arbitrary-precision ints. Stored state fields are `<= 1e30` (enforced by the
//! bound checks) and therefore fit `u128`.
//!
//! Reject reasons are stable string codes; the Python harness
//! (`tools/runtime/zusd_kernel_lib.py`) maps `zusd.py`'s error prose to the same
//! codes, and the Python/Rust differential pins the agreement.

use num_bigint::BigUint;

use crate::canonical::{domain_sep_bytes, encode_bytes, encode_uvarint, sha256_bytes, sha256_hex};

pub const E8: u128 = 100_000_000;
pub const BPS_SCALE: u128 = 10_000;
/// Authority bound (`10**30`); every stored amount must be `<= MAX_AMOUNT_E8`.
pub const MAX_AMOUNT_E8: u128 = 1_000_000_000_000_000_000_000_000_000_000;
const _: () = assert!(MAX_AMOUNT_E8 <= u128::MAX / 3);

const STATE_LABEL: &str = "zusd_state";
const RECEIPT_LABEL: &str = "zusd_receipt";
const STATE_VERSION: u32 = 1;
const RECEIPT_VERSION: u32 = 1;

// --- Stable reject codes (mirrored by the Python harness mapping) -------------
pub const REJ_NOT_POSITIVE_INT: &str = "not_positive_int";
pub const REJ_BOUNDED_CHECK_FAILED: &str = "bounded_check_failed";
pub const REJ_INVARIANT_VIOLATION: &str = "invariant_violation";
pub const REJ_UNKNOWN_ACTION: &str = "unknown_action";

/// A parsed zUSD command. Numeric args are the integer literal string (or `None`
/// if missing / not an integer); `require_pos` enforces the positive-int rule at
/// the point `zusd.py` calls `_require_pos_int`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ZusdCommand {
    AdvanceEpoch {
        delta: Option<String>,
    },
    BootstrapOracle {
        auth_ok: bool,
        price_e8: Option<String>,
    },
    OracleReport {
        auth_ok: bool,
        price_e8: Option<String>,
    },
    OracleCommit {
        auth_ok: bool,
    },
    DepositCollateral {
        amount_e8: Option<String>,
    },
    WithdrawCollateral {
        amount_e8: Option<String>,
    },
    MintZusd {
        amount_e8: Option<String>,
    },
    RepayZusd {
        amount_e8: Option<String>,
    },
    DepositSp {
        amount_e8: Option<String>,
    },
    WithdrawSp {
        amount_e8: Option<String>,
    },
    RedeemZusd {
        amount_e8: Option<String>,
    },
    Liquidate,
    Unknown,
}

/// zUSD state (single vault). All stored amounts are `<= MAX_AMOUNT_E8`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ZusdState {
    pub now_epoch: u128,
    pub oracle_seen: bool,
    pub oracle_last_update_epoch: u128,
    pub price_e8: u128,
    pub price_pending_e8: u128,
    pub max_oracle_staleness_epochs: u128,
    pub collateral_e8: u128,
    pub debt_e8: u128,
    pub free_debt_e8: u128,
    pub sp_debt_e8: u128,
    pub sp_coll_e8: u128,
    pub protocol_collateral_e8: u128,
    pub protocol_revenue_zusd_cum_e8: u128,
    pub liquidator_compensation_collateral_cum_e8: u128,
    pub mcr_bps: u128,
    pub ccr_bps: u128,
    pub min_debt_open_e8: u128,
    pub max_debt_e8: u128,
    pub max_debt_supply_e8: u128,
    pub max_sp_coll_e8: u128,
    pub max_protocol_coll_e8: u128,
    pub base_rate_bps: u128,
    pub base_rate_last_epoch: u128,
    pub base_rate_decay_per_epoch_bps: u128,
    pub base_rate_borrow_bump_bps: u128,
    pub base_rate_redeem_bump_bps: u128,
    pub borrow_fee_floor_bps: u128,
    pub borrow_fee_max_bps: u128,
    pub redemption_fee_floor_bps: u128,
    pub redemption_fee_max_bps: u128,
    pub liquidation_gas_comp_fixed_collateral_e8: u128,
    pub liquidation_gas_comp_bps: u128,
}

impl Default for ZusdState {
    /// Mirrors `zusd.init_state()` / `ZUSDState()` defaults.
    fn default() -> Self {
        ZusdState {
            now_epoch: 0,
            oracle_seen: false,
            oracle_last_update_epoch: 0,
            price_e8: 0,
            price_pending_e8: 0,
            max_oracle_staleness_epochs: 100,
            collateral_e8: 0,
            debt_e8: 0,
            free_debt_e8: 0,
            sp_debt_e8: 0,
            sp_coll_e8: 0,
            protocol_collateral_e8: 0,
            protocol_revenue_zusd_cum_e8: 0,
            liquidator_compensation_collateral_cum_e8: 0,
            mcr_bps: 11_000,
            ccr_bps: 15_000,
            min_debt_open_e8: 100 * E8,
            max_debt_e8: 10_000_000 * E8,
            max_debt_supply_e8: 20_000_000 * E8,
            max_sp_coll_e8: 20_000_000 * E8,
            max_protocol_coll_e8: 20_000_000 * E8,
            base_rate_bps: 0,
            base_rate_last_epoch: 0,
            base_rate_decay_per_epoch_bps: 0,
            base_rate_borrow_bump_bps: 0,
            base_rate_redeem_bump_bps: 0,
            borrow_fee_floor_bps: 0,
            borrow_fee_max_bps: 1_000,
            redemption_fee_floor_bps: 0,
            redemption_fee_max_bps: 1_000,
            liquidation_gas_comp_fixed_collateral_e8: 0,
            liquidation_gas_comp_bps: 0,
        }
    }
}

impl ZusdState {
    /// All amount fields in declaration order (`oracle_seen` as 0/1). Used by
    /// both the state root and the `<= MAX_AMOUNT_E8` bound check.
    fn fields(&self) -> [u128; 32] {
        [
            self.now_epoch,
            self.oracle_seen as u128,
            self.oracle_last_update_epoch,
            self.price_e8,
            self.price_pending_e8,
            self.max_oracle_staleness_epochs,
            self.collateral_e8,
            self.debt_e8,
            self.free_debt_e8,
            self.sp_debt_e8,
            self.sp_coll_e8,
            self.protocol_collateral_e8,
            self.protocol_revenue_zusd_cum_e8,
            self.liquidator_compensation_collateral_cum_e8,
            self.mcr_bps,
            self.ccr_bps,
            self.min_debt_open_e8,
            self.max_debt_e8,
            self.max_debt_supply_e8,
            self.max_sp_coll_e8,
            self.max_protocol_coll_e8,
            self.base_rate_bps,
            self.base_rate_last_epoch,
            self.base_rate_decay_per_epoch_bps,
            self.base_rate_borrow_bump_bps,
            self.base_rate_redeem_bump_bps,
            self.borrow_fee_floor_bps,
            self.borrow_fee_max_bps,
            self.redemption_fee_floor_bps,
            self.redemption_fee_max_bps,
            self.liquidation_gas_comp_fixed_collateral_e8,
            self.liquidation_gas_comp_bps,
        ]
    }

    /// Canonical state root: `domain_sep("zusd_state", v1)` + every field as a
    /// uvarint, in declaration order.
    pub fn state_root(&self) -> String {
        format!("0x{}", hex::encode(self.state_root_bytes()))
    }

    fn state_root_bytes(&self) -> [u8; 32] {
        let mut buf = domain_sep_bytes(STATE_LABEL, STATE_VERSION);
        for f in self.fields() {
            buf.extend(encode_uvarint(f));
        }
        sha256_bytes(&buf)
    }
}

/// Successful step: the command tag, the next state, and a receipt that commits
/// to `(tag, post_state_root)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ZusdAccepted {
    pub tag: &'static str,
    pub state: ZusdState,
    pub receipt_hash: String,
}

fn receipt_hash(tag: &str, post_root: &[u8; 32]) -> String {
    let mut buf = domain_sep_bytes(RECEIPT_LABEL, RECEIPT_VERSION);
    buf.extend_from_slice(b"TAG");
    buf.extend(encode_bytes(tag.as_bytes()));
    buf.extend_from_slice(b"RT");
    buf.extend(encode_bytes(post_root));
    sha256_hex(&buf)
}

// --- BigUint arithmetic helpers (mirror zusd.py exactly) ----------------------

fn bu(x: u128) -> BigUint {
    BigUint::from(x)
}

fn mcr_ok(collateral_e8: u128, debt_e8: u128, price_e8: u128, mcr_bps: u128) -> bool {
    if debt_e8 == 0 {
        return true;
    }
    bu(collateral_e8) * bu(price_e8) * bu(BPS_SCALE) >= bu(debt_e8) * bu(mcr_bps) * bu(E8)
}

fn solvent_at_price(collateral_e8: u128, debt_e8: u128, price_e8: u128) -> bool {
    if debt_e8 == 0 {
        return true;
    }
    bu(collateral_e8) * bu(price_e8) >= bu(debt_e8) * bu(E8)
}

fn debt_floor_ok(debt_e8: u128, min_debt_open_e8: u128) -> bool {
    debt_e8 == 0 || debt_e8 >= min_debt_open_e8
}

/// `ceil(a * b / den)` over BigUint; result is returned as BigUint (caller bound-checks).
fn mul_div_up(a: &BigUint, b: &BigUint, den: u128) -> BigUint {
    if a == &BigUint::ZERO || b == &BigUint::ZERO {
        return BigUint::ZERO;
    }
    (a * b + bu(den) - 1u32) / bu(den)
}

fn is_oracle_fresh(
    now_epoch: u128,
    last_update_epoch: u128,
    max_staleness: u128,
    seen: bool,
) -> bool {
    seen && now_epoch >= last_update_epoch && now_epoch - last_update_epoch <= max_staleness
}

fn decayed_base_rate_bps(
    base_rate_bps: u128,
    now_epoch: u128,
    last_epoch: u128,
    decay_per_epoch_bps: u128,
) -> u128 {
    // zusd.py raises if now < last; transitions keep last <= now, so saturating.
    let elapsed = now_epoch.saturating_sub(last_epoch);
    let decay = decay_per_epoch_bps.saturating_mul(elapsed);
    base_rate_bps.saturating_sub(decay)
}

fn effective_fee_bps(decayed: u128, floor_bps: u128, max_bps: u128) -> u128 {
    let mut fee = floor_bps.saturating_add(decayed);
    if fee > max_bps {
        fee = max_bps;
    }
    if fee > BPS_SCALE {
        fee = BPS_SCALE;
    }
    fee
}

fn liquidation_compensation_split(
    liquidated_collateral_e8: u128,
    fixed_compensation_e8: u128,
    variable_comp_bps: u128,
) -> Option<(u128, u128)> {
    if variable_comp_bps > BPS_SCALE {
        return None;
    }
    let variable_comp = liquidated_collateral_e8
        .checked_mul(variable_comp_bps)?
        .div_ceil(BPS_SCALE);
    let requested = fixed_compensation_e8.checked_add(variable_comp)?;
    let liquidator_compensation = liquidated_collateral_e8.min(requested);
    let stability_pool_gain = liquidated_collateral_e8 - liquidator_compensation;
    Some((liquidator_compensation, stability_pool_gain))
}

fn tcr_ok(state: &ZusdState, price_e8: u128) -> bool {
    if state.debt_e8 == 0 {
        return true;
    }
    let total_coll =
        bu(state.collateral_e8) + bu(state.sp_coll_e8) + bu(state.protocol_collateral_e8);
    total_coll * bu(price_e8) * bu(BPS_SCALE) >= bu(state.debt_e8) * bu(state.ccr_bps) * bu(E8)
}

/// Whether the system is in recovery mode (TCR < CCR or oracle unseen).
pub fn in_recovery_mode(state: &ZusdState) -> bool {
    if !state.oracle_seen || state.price_e8 == 0 {
        return true;
    }
    !tcr_ok(state, state.price_e8)
}

fn risky_ops_allowed(state: &ZusdState) -> bool {
    if !state.oracle_seen || state.price_e8 == 0 || state.price_pending_e8 == 0 {
        return false;
    }
    if state.price_pending_e8 != state.price_e8 {
        return false;
    }
    if !is_oracle_fresh(
        state.now_epoch,
        state.oracle_last_update_epoch,
        state.max_oracle_staleness_epochs,
        state.oracle_seen,
    ) {
        return false;
    }
    !in_recovery_mode(state)
}

/// Hard accounting and representation invariants.
pub fn check_invariants(state: &ZusdState) -> Vec<&'static str> {
    let mut failed = Vec::new();
    if state.oracle_last_update_epoch > state.now_epoch {
        failed.push("inv_oracle_update_not_future");
    }
    if state.base_rate_last_epoch > state.now_epoch {
        failed.push("inv_base_rate_not_future");
    }
    if state.oracle_seen && (state.price_e8 == 0 || state.price_pending_e8 == 0) {
        failed.push("inv_oracle_seen_positive_prices");
    }
    if state.oracle_seen && state.price_pending_e8 > state.price_e8 {
        failed.push("inv_pending_le_active");
    }
    if !state.oracle_seen
        && (state.price_e8 != 0
            || state.price_pending_e8 != 0
            || state.oracle_last_update_epoch != 0)
    {
        failed.push("inv_oracle_unseen_zeroed");
    }
    if state.free_debt_e8 + state.sp_debt_e8 != state.debt_e8 {
        failed.push("inv_supply_conservation");
    }
    if state.debt_e8 > state.max_debt_supply_e8 {
        failed.push("inv_total_debt_cap");
    }
    if !debt_floor_ok(state.debt_e8, state.min_debt_open_e8) {
        failed.push("inv_debt_floor");
    }
    failed
}

/// Finalized-price health facts. Distress remains representable state.
pub fn check_health_conditions(state: &ZusdState) -> Vec<&'static str> {
    let mut failed = Vec::new();
    if !state.oracle_seen || state.price_e8 == 0 {
        return failed;
    }
    if state.debt_e8 > 0
        && !mcr_ok(
            state.collateral_e8,
            state.debt_e8,
            state.price_e8,
            state.mcr_bps,
        )
    {
        failed.push("health_vault_below_mcr");
    }
    // Each term is structurally bounded by MAX_AMOUNT_E8. The compile-time
    // assertion above proves this exact sum fits u128 without saturation.
    let system_collateral = state.collateral_e8 + state.sp_coll_e8 + state.protocol_collateral_e8;
    if !solvent_at_price(system_collateral, state.debt_e8, state.price_e8) {
        failed.push("health_system_bad_debt");
    }
    failed
}

// --- arg parsing helpers ------------------------------------------------------

fn validate_state_shape(state: &ZusdState) -> Result<(), &'static str> {
    if state.fields().iter().any(|f| *f > MAX_AMOUNT_E8) {
        return Err(REJ_BOUNDED_CHECK_FAILED);
    }
    if state.oracle_last_update_epoch > state.now_epoch
        || state.base_rate_last_epoch > state.now_epoch
    {
        return Err(REJ_INVARIANT_VIOLATION);
    }
    if state.oracle_seen {
        if state.price_e8 == 0
            || state.price_pending_e8 == 0
            || state.price_pending_e8 > state.price_e8
        {
            return Err(REJ_INVARIANT_VIOLATION);
        }
    } else if state.price_e8 != 0
        || state.price_pending_e8 != 0
        || state.oracle_last_update_epoch != 0
    {
        return Err(REJ_INVARIANT_VIOLATION);
    }
    if state.mcr_bps == 0 || state.mcr_bps > state.ccr_bps {
        return Err(REJ_INVARIANT_VIOLATION);
    }
    if state.max_debt_e8 > state.max_debt_supply_e8 {
        return Err(REJ_INVARIANT_VIOLATION);
    }
    if state.base_rate_bps > BPS_SCALE
        || state.base_rate_decay_per_epoch_bps > BPS_SCALE
        || state.base_rate_borrow_bump_bps > BPS_SCALE
        || state.base_rate_redeem_bump_bps > BPS_SCALE
        || state.borrow_fee_floor_bps > state.borrow_fee_max_bps
        || state.borrow_fee_max_bps > BPS_SCALE
        || state.redemption_fee_floor_bps > state.redemption_fee_max_bps
        || state.redemption_fee_max_bps > BPS_SCALE
        || state.liquidation_gas_comp_bps > BPS_SCALE
    {
        return Err(REJ_INVARIANT_VIOLATION);
    }
    if !check_invariants(state).is_empty() {
        return Err(REJ_INVARIANT_VIOLATION);
    }
    Ok(())
}

/// `_require_pos_int`: the literal must be a positive integer. **No upper
/// bound** — exactly like the authority, which rejects huge values only via
/// downstream command logic. Returns the value as a `BigUint`.
fn require_pos(arg: &Option<String>) -> Result<BigUint, &'static str> {
    let s = arg.as_deref().ok_or(REJ_NOT_POSITIVE_INT)?;
    if s.starts_with('-') {
        return Err(REJ_NOT_POSITIVE_INT);
    }
    let v: BigUint = s.parse().map_err(|_| REJ_NOT_POSITIVE_INT)?;
    if v == BigUint::ZERO {
        return Err(REJ_NOT_POSITIVE_INT);
    }
    Ok(v)
}

/// Convert a (validated) BigUint to `u128`; overflow maps to a bound failure.
fn to_u128(b: &BigUint) -> Result<u128, &'static str> {
    u128::try_from(b).map_err(|_| REJ_BOUNDED_CHECK_FAILED)
}

fn finish(tag: &'static str, ns: ZusdState) -> Result<ZusdAccepted, &'static str> {
    // `__post_init__` bound portion: every stored amount must be <= MAX_AMOUNT_E8.
    if ns.fields().iter().any(|f| *f > MAX_AMOUNT_E8) {
        return Err(REJ_BOUNDED_CHECK_FAILED);
    }
    if !check_invariants(&ns).is_empty() {
        return Err(REJ_INVARIANT_VIOLATION);
    }
    let root_bytes = ns.state_root_bytes();
    let rh = receipt_hash(tag, &root_bytes);
    Ok(ZusdAccepted {
        tag,
        state: ns,
        receipt_hash: rh,
    })
}

/// Apply one zUSD command (single-vault), mirroring `zusd.step`.
pub fn step(state: &ZusdState, cmd: &ZusdCommand) -> Result<ZusdAccepted, &'static str> {
    validate_state_shape(state)?;
    match cmd {
        ZusdCommand::AdvanceEpoch { delta } => {
            let d = require_pos(delta)?;
            let new_now = to_u128(&(bu(state.now_epoch) + d))?;
            let ns = ZusdState {
                now_epoch: new_now,
                ..state.clone()
            };
            finish("advance_epoch", ns)
        }

        ZusdCommand::BootstrapOracle { auth_ok, price_e8 } => {
            if state.oracle_seen {
                return Err("oracle_already_bootstrapped");
            }
            if !auth_ok {
                return Err("bootstrap_requires_auth");
            }
            let p = to_u128(&require_pos(price_e8)?)?;
            let ns = ZusdState {
                oracle_seen: true,
                oracle_last_update_epoch: state.now_epoch,
                price_e8: p,
                price_pending_e8: p,
                ..state.clone()
            };
            finish("bootstrap_oracle", ns)
        }

        ZusdCommand::OracleReport { auth_ok, price_e8 } => {
            if !state.oracle_seen {
                return Err("oracle_not_bootstrapped");
            }
            if !auth_ok {
                return Err("report_requires_auth");
            }
            let p = require_pos(price_e8)?;
            if p > bu(state.price_pending_e8) {
                return Err("report_price_not_non_increasing");
            }
            let ns = ZusdState {
                price_pending_e8: to_u128(&p)?,
                ..state.clone()
            };
            finish("oracle_report", ns)
        }

        ZusdCommand::OracleCommit { auth_ok } => {
            if !state.oracle_seen {
                return Err("oracle_not_bootstrapped");
            }
            if !auth_ok {
                return Err("commit_requires_auth");
            }
            if !is_oracle_fresh(
                state.now_epoch,
                state.oracle_last_update_epoch,
                state.max_oracle_staleness_epochs,
                state.oracle_seen,
            ) {
                return Err("commit_stale_oracle_context");
            }
            let ns = ZusdState {
                price_e8: state.price_pending_e8,
                oracle_last_update_epoch: state.now_epoch,
                ..state.clone()
            };
            finish("oracle_commit", ns)
        }

        ZusdCommand::DepositCollateral { amount_e8 } => {
            let amt = require_pos(amount_e8)?;
            let new_coll = to_u128(&(bu(state.collateral_e8) + amt))?;
            let ns = ZusdState {
                collateral_e8: new_coll,
                ..state.clone()
            };
            finish("deposit_collateral", ns)
        }

        ZusdCommand::WithdrawCollateral { amount_e8 } => {
            let amt = require_pos(amount_e8)?;
            if amt > bu(state.collateral_e8) {
                return Err("insufficient_collateral");
            }
            if state.debt_e8 > 0 && !risky_ops_allowed(state) {
                return Err("withdraw_blocked_oracle");
            }
            let post_coll = state.collateral_e8 - to_u128(&amt)?;
            if !mcr_ok(post_coll, state.debt_e8, state.price_e8, state.mcr_bps) {
                return Err("withdraw_violates_mcr");
            }
            let ns = ZusdState {
                collateral_e8: post_coll,
                ..state.clone()
            };
            finish("withdraw_collateral", ns)
        }

        ZusdCommand::MintZusd { amount_e8 } => {
            let amt = require_pos(amount_e8)?;
            if !risky_ops_allowed(state) {
                return Err("mint_blocked_oracle");
            }
            if state.debt_e8 == 0 && amt < bu(state.min_debt_open_e8) {
                return Err("mint_below_min_debt");
            }
            let decayed = decayed_base_rate_bps(
                state.base_rate_bps,
                state.now_epoch,
                state.base_rate_last_epoch,
                state.base_rate_decay_per_epoch_bps,
            );
            let fee_bps = effective_fee_bps(
                decayed,
                state.borrow_fee_floor_bps,
                state.borrow_fee_max_bps,
            );
            let fee_big = mul_div_up(&amt, &bu(fee_bps), BPS_SCALE);
            let debt_delta_big = &amt + &fee_big;
            let new_debt_big = bu(state.debt_e8) + &debt_delta_big;
            if new_debt_big > bu(state.max_debt_e8) {
                return Err("mint_exceeds_max_debt");
            }
            if new_debt_big > bu(state.max_debt_supply_e8) {
                return Err("mint_exceeds_max_supply");
            }
            let new_debt = to_u128(&new_debt_big)?;
            if !mcr_ok(state.collateral_e8, new_debt, state.price_e8, state.mcr_bps) {
                return Err("mint_violates_mcr");
            }
            let fee_e8 = to_u128(&fee_big)?;
            let debt_delta = to_u128(&debt_delta_big)?;
            let ns = ZusdState {
                debt_e8: new_debt,
                free_debt_e8: state.free_debt_e8 + debt_delta,
                protocol_revenue_zusd_cum_e8: state.protocol_revenue_zusd_cum_e8 + fee_e8,
                base_rate_bps: (decayed + state.base_rate_borrow_bump_bps).min(BPS_SCALE),
                base_rate_last_epoch: state.now_epoch,
                ..state.clone()
            };
            finish("mint_zusd", ns)
        }

        ZusdCommand::RepayZusd { amount_e8 } => {
            let amt = require_pos(amount_e8)?;
            if amt > bu(state.debt_e8) {
                return Err("repay_exceeds_debt");
            }
            if amt > bu(state.free_debt_e8) {
                return Err("repay_exceeds_free_debt");
            }
            let amt128 = to_u128(&amt)?;
            let post_debt = state.debt_e8 - amt128;
            if !debt_floor_ok(post_debt, state.min_debt_open_e8) {
                return Err("repay_below_min_debt");
            }
            let ns = ZusdState {
                debt_e8: post_debt,
                free_debt_e8: state.free_debt_e8 - amt128,
                ..state.clone()
            };
            finish("repay_zusd", ns)
        }

        ZusdCommand::DepositSp { amount_e8 } => {
            let amt = require_pos(amount_e8)?;
            if amt > bu(state.free_debt_e8) {
                return Err("deposit_sp_exceeds_free_debt");
            }
            if bu(state.sp_debt_e8) + &amt > bu(state.max_debt_supply_e8) {
                return Err("deposit_sp_exceeds_max_supply");
            }
            let amt128 = to_u128(&amt)?;
            let ns = ZusdState {
                free_debt_e8: state.free_debt_e8 - amt128,
                sp_debt_e8: state.sp_debt_e8 + amt128,
                ..state.clone()
            };
            finish("deposit_sp", ns)
        }

        ZusdCommand::WithdrawSp { amount_e8 } => {
            let amt = require_pos(amount_e8)?;
            if amt > bu(state.sp_debt_e8) {
                return Err("withdraw_sp_exceeds_sp_debt");
            }
            if !risky_ops_allowed(state) {
                return Err("withdraw_sp_blocked_oracle");
            }
            if !mcr_ok(
                state.collateral_e8,
                state.debt_e8,
                state.price_e8,
                state.mcr_bps,
            ) {
                return Err("withdraw_sp_below_mcr");
            }
            let amt128 = to_u128(&amt)?;
            let ns = ZusdState {
                sp_debt_e8: state.sp_debt_e8 - amt128,
                free_debt_e8: state.free_debt_e8 + amt128,
                ..state.clone()
            };
            finish("withdraw_sp", ns)
        }

        ZusdCommand::RedeemZusd { amount_e8 } => {
            let amt = require_pos(amount_e8)?;
            if !state.oracle_seen || state.price_e8 == 0 || state.price_pending_e8 == 0 {
                return Err("redeem_oracle_uninitialized");
            }
            if state.price_pending_e8 != state.price_e8 {
                return Err("redeem_pending_mismatch");
            }
            if !is_oracle_fresh(
                state.now_epoch,
                state.oracle_last_update_epoch,
                state.max_oracle_staleness_epochs,
                state.oracle_seen,
            ) {
                return Err("redeem_stale_oracle");
            }
            if amt > bu(state.debt_e8) {
                return Err("redeem_exceeds_debt");
            }
            if amt > bu(state.free_debt_e8) {
                return Err("redeem_exceeds_free_debt");
            }
            let amt128 = to_u128(&amt)?;
            let gross_big = (&amt * bu(E8)) / bu(state.price_e8);
            if gross_big == BigUint::ZERO {
                return Err("redeem_amount_too_small");
            }
            if gross_big > bu(state.collateral_e8) {
                return Err("redeem_insufficient_collateral");
            }
            let gross = to_u128(&gross_big)?;
            let decayed = decayed_base_rate_bps(
                state.base_rate_bps,
                state.now_epoch,
                state.base_rate_last_epoch,
                state.base_rate_decay_per_epoch_bps,
            );
            let fee_bps = effective_fee_bps(
                decayed,
                state.redemption_fee_floor_bps,
                state.redemption_fee_max_bps,
            );
            let fee_big = mul_div_up(&bu(gross), &bu(fee_bps), BPS_SCALE);
            if fee_big >= bu(gross) {
                return Err("redeem_fee_consumes_all");
            }
            let fee = to_u128(&fee_big)?;
            if state.protocol_collateral_e8 + fee > state.max_protocol_coll_e8 {
                return Err("redeem_protocol_cap_exceeded");
            }
            let post_debt = state.debt_e8 - amt128;
            let post_collateral = state.collateral_e8 - gross;
            if !debt_floor_ok(post_debt, state.min_debt_open_e8) {
                return Err("redeem_below_min_debt");
            }
            if !mcr_ok(post_collateral, post_debt, state.price_e8, state.mcr_bps) {
                return Err("redeem_violates_mcr");
            }
            let ns = ZusdState {
                debt_e8: post_debt,
                free_debt_e8: state.free_debt_e8 - amt128,
                collateral_e8: post_collateral,
                protocol_collateral_e8: state.protocol_collateral_e8 + fee,
                base_rate_bps: (decayed + state.base_rate_redeem_bump_bps).min(BPS_SCALE),
                base_rate_last_epoch: state.now_epoch,
                ..state.clone()
            };
            finish("redeem_zusd", ns)
        }

        ZusdCommand::Liquidate => {
            if !state.oracle_seen || state.price_e8 == 0 {
                return Err("liquidate_oracle_uninitialized");
            }
            if state.price_pending_e8 != state.price_e8 {
                return Err("liquidate_pending_mismatch");
            }
            if !is_oracle_fresh(
                state.now_epoch,
                state.oracle_last_update_epoch,
                state.max_oracle_staleness_epochs,
                state.oracle_seen,
            ) {
                return Err("liquidate_stale_oracle");
            }
            if state.debt_e8 == 0 {
                return Err("liquidate_no_debt");
            }
            if mcr_ok(
                state.collateral_e8,
                state.debt_e8,
                state.price_e8,
                state.mcr_bps,
            ) {
                return Err("liquidate_not_under_mcr");
            }
            if state.debt_e8 > state.sp_debt_e8 {
                return Err("liquidate_sp_cannot_absorb");
            }
            let liquidated_coll = state.collateral_e8;
            let (liquidator_comp, sp_gain) = liquidation_compensation_split(
                liquidated_coll,
                state.liquidation_gas_comp_fixed_collateral_e8,
                state.liquidation_gas_comp_bps,
            )
            .ok_or(REJ_BOUNDED_CHECK_FAILED)?;
            if state.sp_coll_e8 + sp_gain > state.max_sp_coll_e8 {
                return Err("liquidate_sp_cap_exceeded");
            }
            let ns = ZusdState {
                debt_e8: 0,
                collateral_e8: 0,
                sp_debt_e8: state.sp_debt_e8 - state.debt_e8,
                sp_coll_e8: state.sp_coll_e8 + sp_gain,
                liquidator_compensation_collateral_cum_e8: state
                    .liquidator_compensation_collateral_cum_e8
                    + liquidator_comp,
                ..state.clone()
            };
            finish("liquidate", ns)
        }

        ZusdCommand::Unknown => Err(REJ_UNKNOWN_ACTION),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn amt(v: &str) -> Option<String> {
        Some(v.to_string())
    }

    #[test]
    fn state_root_bytes_match_hex_root_without_reparse() {
        let state = ZusdState::default();
        let root = state.state_root();
        assert_eq!(root, format!("0x{}", hex::encode(state.state_root_bytes())));
        let receipt = receipt_hash("advance_epoch", &state.state_root_bytes());
        assert!(receipt.starts_with("0x"));
        assert_eq!(receipt.len(), 66);
    }

    fn bootstrap(state: &ZusdState, price: &str) -> ZusdState {
        step(
            state,
            &ZusdCommand::BootstrapOracle {
                auth_ok: true,
                price_e8: amt(price),
            },
        )
        .unwrap()
        .state
    }

    #[test]
    fn mint_then_repay_lifecycle() {
        let s = ZusdState::default();
        let s = bootstrap(&s, "100000000"); // price = $1 (1e8)
        let s = step(
            &s,
            &ZusdCommand::DepositCollateral {
                amount_e8: amt("100000000000"),
            },
        )
        .unwrap()
        .state; // 1000 units
                // Mint 200 zUSD (>= min_debt_open 100*1e8).
        let r = step(
            &s,
            &ZusdCommand::MintZusd {
                amount_e8: amt("20000000000"),
            },
        )
        .unwrap();
        assert_eq!(r.state.debt_e8, 20_000_000_000);
        assert_eq!(r.state.free_debt_e8, r.state.debt_e8);
        // Repay 50.
        let r2 = step(
            &r.state,
            &ZusdCommand::RepayZusd {
                amount_e8: amt("5000000000"),
            },
        )
        .unwrap();
        assert_eq!(r2.state.debt_e8, 15_000_000_000);
    }

    #[test]
    fn mint_below_min_debt_rejected() {
        let s = bootstrap(&ZusdState::default(), "100000000");
        let s = step(
            &s,
            &ZusdCommand::DepositCollateral {
                amount_e8: amt("100000000000"),
            },
        )
        .unwrap()
        .state;
        assert_eq!(
            step(
                &s,
                &ZusdCommand::MintZusd {
                    amount_e8: amt("1")
                }
            ),
            Err("mint_below_min_debt")
        );
    }

    #[test]
    fn mint_without_collateral_violates_mcr() {
        let s = bootstrap(&ZusdState::default(), "100000000");
        // No collateral: any mint violates MCR.
        assert_eq!(
            step(
                &s,
                &ZusdCommand::MintZusd {
                    amount_e8: amt("20000000000")
                }
            ),
            Err("mint_violates_mcr")
        );
    }

    #[test]
    fn not_positive_int_rejected() {
        let s = ZusdState::default();
        assert_eq!(
            step(&s, &ZusdCommand::AdvanceEpoch { delta: amt("0") }),
            Err(REJ_NOT_POSITIVE_INT)
        );
        assert_eq!(
            step(&s, &ZusdCommand::AdvanceEpoch { delta: amt("-1") }),
            Err(REJ_NOT_POSITIVE_INT)
        );
        assert_eq!(
            step(&s, &ZusdCommand::AdvanceEpoch { delta: None }),
            Err(REJ_NOT_POSITIVE_INT)
        );
    }

    #[test]
    fn oracle_freshness_future_update_fails_closed() {
        assert!(!is_oracle_fresh(1, 2, 100, true));
    }

    #[test]
    fn liquidation_compensation_split_caps_and_conserves() {
        assert_eq!(
            liquidation_compensation_split(1_000, 50, 100),
            Some((60, 940))
        );
        assert_eq!(
            liquidation_compensation_split(1_000, 2_000, 100),
            Some((1_000, 0))
        );
        assert_eq!(
            liquidation_compensation_split(1_000, 0, 0),
            Some((0, 1_000))
        );
        assert_eq!(
            liquidation_compensation_split(1_000, 0, BPS_SCALE + 1),
            None
        );
    }

    #[test]
    fn malformed_pre_state_rejected_before_transition() {
        let s = ZusdState {
            now_epoch: 1,
            oracle_seen: true,
            oracle_last_update_epoch: 2,
            price_e8: E8,
            price_pending_e8: E8,
            ..Default::default()
        };
        assert_eq!(
            step(
                &s,
                &ZusdCommand::DepositCollateral {
                    amount_e8: amt("1")
                }
            ),
            Err(REJ_INVARIANT_VIOLATION)
        );
    }

    #[test]
    fn state_root_changes_on_mint() {
        let s = bootstrap(&ZusdState::default(), "100000000");
        let s = step(
            &s,
            &ZusdCommand::DepositCollateral {
                amount_e8: amt("100000000000"),
            },
        )
        .unwrap()
        .state;
        let before = s.state_root();
        let after = step(
            &s,
            &ZusdCommand::MintZusd {
                amount_e8: amt("20000000000"),
            },
        )
        .unwrap()
        .state;
        assert_ne!(before, after.state_root());
    }

    fn cap_state() -> ZusdState {
        ZusdState {
            oracle_seen: true,
            price_e8: 100 * E8,
            price_pending_e8: 100 * E8,
            collateral_e8: 100 * E8,
            debt_e8: 1_400 * E8,
            free_debt_e8: 100 * E8,
            sp_debt_e8: 1_300 * E8,
            max_debt_e8: 1_500 * E8,
            max_debt_supply_e8: 1_500 * E8,
            ..Default::default()
        }
    }

    #[test]
    fn mint_accepts_exact_total_debt_cap() {
        let accepted = step(
            &cap_state(),
            &ZusdCommand::MintZusd {
                amount_e8: amt(&(100 * E8).to_string()),
            },
        )
        .unwrap();
        assert_eq!(accepted.state.debt_e8, 1_500 * E8);
        assert_eq!(accepted.state.free_debt_e8, 200 * E8);
        assert_eq!(accepted.state.sp_debt_e8, 1_300 * E8);
        assert!(check_invariants(&accepted.state).is_empty());
    }

    #[test]
    fn mint_above_shared_vault_and_supply_cap_rejects() {
        assert_eq!(
            step(
                &cap_state(),
                &ZusdCommand::MintZusd {
                    amount_e8: amt(&(101 * E8).to_string()),
                },
            ),
            Err("mint_exceeds_max_debt")
        );
    }

    #[test]
    fn forged_total_debt_above_cap_is_invalid_state() {
        let forged = ZusdState {
            oracle_seen: true,
            price_e8: 100 * E8,
            price_pending_e8: 100 * E8,
            collateral_e8: 100 * E8,
            debt_e8: 1_600 * E8,
            free_debt_e8: 300 * E8,
            sp_debt_e8: 1_300 * E8,
            max_debt_e8: 1_500 * E8,
            max_debt_supply_e8: 1_500 * E8,
            ..Default::default()
        };
        assert!(check_invariants(&forged).contains(&"inv_total_debt_cap"));
        assert_eq!(
            step(
                &forged,
                &ZusdCommand::DepositCollateral {
                    amount_e8: amt("1"),
                },
            ),
            Err(REJ_INVARIANT_VIOLATION)
        );
    }

    fn pending_distress() -> ZusdState {
        let state = bootstrap(&ZusdState::default(), &(100 * E8).to_string());
        let state = step(
            &state,
            &ZusdCommand::DepositCollateral {
                amount_e8: amt(&(2 * E8).to_string()),
            },
        )
        .unwrap()
        .state;
        let state = step(
            &state,
            &ZusdCommand::MintZusd {
                amount_e8: amt(&(150 * E8).to_string()),
            },
        )
        .unwrap()
        .state;
        let state = step(
            &state,
            &ZusdCommand::DepositSp {
                amount_e8: amt(&(150 * E8).to_string()),
            },
        )
        .unwrap()
        .state;
        step(
            &state,
            &ZusdCommand::OracleReport {
                auth_ok: true,
                price_e8: amt(&(70 * E8).to_string()),
            },
        )
        .unwrap()
        .state
    }

    #[test]
    fn pending_price_cannot_liquidate_before_finalization() {
        assert_eq!(
            step(&pending_distress(), &ZusdCommand::Liquidate),
            Err("liquidate_pending_mismatch")
        );
    }

    #[test]
    fn adverse_price_finalizes_then_authorizes_liquidation() {
        let finalized = step(
            &pending_distress(),
            &ZusdCommand::OracleCommit { auth_ok: true },
        )
        .unwrap()
        .state;
        assert_eq!(finalized.price_e8, 70 * E8);
        assert!(check_invariants(&finalized).is_empty());
        let health = check_health_conditions(&finalized);
        assert!(health.contains(&"health_vault_below_mcr"));
        assert!(health.contains(&"health_system_bad_debt"));

        let liquidated = step(&finalized, &ZusdCommand::Liquidate).unwrap();
        assert_eq!(liquidated.state.debt_e8, 0);
        assert_eq!(liquidated.state.collateral_e8, 0);
    }

    #[test]
    fn stale_finalized_price_cannot_liquidate() {
        let finalized = step(
            &pending_distress(),
            &ZusdCommand::OracleCommit { auth_ok: true },
        )
        .unwrap()
        .state;
        let stale = step(
            &finalized,
            &ZusdCommand::AdvanceEpoch {
                delta: amt(&(finalized.max_oracle_staleness_epochs + 1).to_string()),
            },
        )
        .unwrap()
        .state;
        assert_eq!(
            step(&stale, &ZusdCommand::Liquidate),
            Err("liquidate_stale_oracle")
        );
    }
}

// ---------------------------------------------------------------------------
// CBC_CORE_V0 — Kani contracts on BigInt-free zUSD risk helpers.
//
// The full zUSD transition intentionally uses BigUint for CDP ratio arithmetic
// and remains differential/vector backed. These contracts prove scalar helper
// behavior used by the running step before or around that BigUint boundary.
// ---------------------------------------------------------------------------
#[cfg(kani)]
mod kani_contracts {
    use super::*;

    #[kani::proof]
    fn oracle_freshness_is_exact_and_total() {
        let now_epoch: u128 = kani::any();
        let last_update_epoch: u128 = kani::any();
        let max_staleness: u128 = kani::any();
        let seen: bool = kani::any();

        let actual = is_oracle_fresh(now_epoch, last_update_epoch, max_staleness, seen);
        if !seen || now_epoch < last_update_epoch {
            assert!(!actual);
        } else {
            assert_eq!(actual, now_epoch - last_update_epoch <= max_staleness);
        }
    }

    #[kani::proof]
    fn decayed_base_rate_never_increases() {
        let base_rate_bps: u128 = kani::any();
        let now_epoch: u128 = kani::any();
        let last_epoch: u128 = kani::any();
        let decay_per_epoch_bps: u128 = kani::any();

        let decayed =
            decayed_base_rate_bps(base_rate_bps, now_epoch, last_epoch, decay_per_epoch_bps);
        assert!(decayed <= base_rate_bps);
        if now_epoch <= last_epoch || decay_per_epoch_bps == 0 {
            assert_eq!(decayed, base_rate_bps);
        }
    }

    #[kani::proof]
    fn effective_fee_is_capped_and_respects_floor_when_ordered() {
        let decayed: u128 = kani::any();
        let floor_bps: u128 = kani::any();
        let max_bps: u128 = kani::any();

        let fee = effective_fee_bps(decayed, floor_bps, max_bps);
        assert!(fee <= BPS_SCALE);
        assert!(fee <= max_bps || max_bps > BPS_SCALE);
        if floor_bps <= max_bps && max_bps <= BPS_SCALE {
            assert!(fee >= floor_bps);
        }
    }

    #[kani::proof]
    fn debt_floor_guard_is_exact() {
        let debt_e8: u128 = kani::any();
        let min_debt_open_e8: u128 = kani::any();
        assert_eq!(
            debt_floor_ok(debt_e8, min_debt_open_e8),
            debt_e8 == 0 || debt_e8 >= min_debt_open_e8
        );
    }

    #[kani::proof]
    fn liquidation_compensation_split_total_on_state_domain() {
        let collateral_e8: u128 = kani::any();
        let fixed_compensation_e8: u128 = kani::any();
        let variable_comp_bps: u128 = kani::any();
        kani::assume(collateral_e8 <= MAX_AMOUNT_E8);
        kani::assume(fixed_compensation_e8 <= MAX_AMOUNT_E8);
        kani::assume(variable_comp_bps <= BPS_SCALE);

        let Some((liquidator_comp, stability_pool_gain)) =
            liquidation_compensation_split(collateral_e8, fixed_compensation_e8, variable_comp_bps)
        else {
            unreachable!("state-domain liquidation compensation is total")
        };

        assert!(liquidator_comp <= collateral_e8);
        assert_eq!(
            liquidator_comp.checked_add(stability_pool_gain),
            Some(collateral_e8)
        );
    }

    #[kani::proof]
    fn liquidation_compensation_split_covers_are_reachable() {
        kani::cover!(liquidation_compensation_split(1_000, 50, 100) == Some((60, 940)));
        kani::cover!(liquidation_compensation_split(1_000, 2_000, 100) == Some((1_000, 0)));
        kani::cover!(liquidation_compensation_split(1_000, 0, 0) == Some((0, 1_000)));
        kani::cover!(liquidation_compensation_split(1_000, 0, BPS_SCALE + 1).is_none());
    }
}
