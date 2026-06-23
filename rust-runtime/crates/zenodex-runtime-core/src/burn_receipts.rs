//! Buyback / burn accounting rails — Rust shadow of the four integer rails in
//! `src/core/burn_receipts.py` (`_rail_replay_guard`, `_rail_amount_guard`,
//! `_rail_supply_guard`, `_rail_batch_sum_guard`).
//!
//! These rails are the buyback-accounting heart: the **amount/budget** rail is
//! the burn budget / floor gate (`burn_budget >= burn_amount`, `burn_amount > 0`
//! when burning), the **supply** rail conserves supply (`supply_after ==
//! supply_before - burn_amount`), and the **batch-sum** rail is the public burn
//! **accumulator** (`batch_after == batch_before + burn_amount`). The replay
//! rail gates a burn on receipt-bound / nullifier-unused / policy-ok host flags.
//!
//! Scope: this shadows the integer rails only. The receipt structural envelope
//! (schema, canonical-JSON `receipt_hash`, and `zusd.py`-style `int()` coercion)
//! remains Python-only for now (it needs bit-exact canonical-JSON + coercion
//! parity); see `docs/runtime/RUNTIME_TRUSTED_CORE_BOUNDARY.md`.

use crate::canonical::{domain_sep_bytes, encode_uvarint, sha256_hex};

/// Per-rail bound: amounts are `<= 0x7FFF`, supplies/sums-after `<= 0xFFFF`
/// (matching the authority's `_rail_*` range checks).
const AMOUNT_MAX: i64 = 0x7FFF;
const SUPPLY_MAX: i64 = 0xFFFF;

pub const REJ_BAD_NUMERIC_FIELD: &str = "bad_numeric_field";
pub const REJ_REPLAY_GUARD_FAILED: &str = "replay_guard_failed";
pub const REJ_AMOUNT_GUARD_FAILED: &str = "amount_guard_failed";
pub const REJ_SUPPLY_GUARD_FAILED: &str = "supply_guard_failed";
pub const REJ_BATCH_SUM_GUARD_FAILED: &str = "batch_sum_guard_failed";

/// The eleven integer rail inputs (extracted by the caller). Stored as `i64`
/// so out-of-range / negative values are representable and rejected by the
/// rails, matching the Python `int` checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RailInputs {
    pub do_burn: i64,
    pub receipt_bound: i64,
    pub nullifier_unused: i64,
    pub policy_ok: i64,
    pub burn_amount: i64,
    pub receipt_amount: i64,
    pub burn_budget: i64,
    pub supply_before: i64,
    pub supply_after: i64,
    pub batch_burn_sum_before: i64,
    pub batch_burn_sum_after: i64,
}

fn is_bit(v: i64) -> bool {
    v == 0 || v == 1
}

pub fn rail_replay_guard(r: &RailInputs) -> bool {
    if !is_bit(r.do_burn) {
        return false;
    }
    if !is_bit(r.receipt_bound) || !is_bit(r.nullifier_unused) || !is_bit(r.policy_ok) {
        return false;
    }
    if r.do_burn == 0 {
        return true;
    }
    r.receipt_bound == 1 && r.nullifier_unused == 1 && r.policy_ok == 1
}

pub fn rail_amount_guard(r: &RailInputs) -> bool {
    for v in [r.burn_amount, r.receipt_amount, r.burn_budget] {
        if !(0..=AMOUNT_MAX).contains(&v) {
            return false;
        }
    }
    if r.do_burn == 0 {
        return r.burn_amount == 0 && r.receipt_amount == 0;
    }
    r.burn_amount > 0 && r.burn_amount == r.receipt_amount && r.burn_budget >= r.burn_amount
}

pub fn rail_supply_guard(r: &RailInputs) -> bool {
    if !(0..=AMOUNT_MAX).contains(&r.burn_amount) {
        return false;
    }
    for v in [r.supply_before, r.supply_after] {
        if !(0..=SUPPLY_MAX).contains(&v) {
            return false;
        }
    }
    if r.do_burn == 0 {
        return r.supply_after == r.supply_before;
    }
    r.supply_before >= r.burn_amount && r.supply_after == r.supply_before - r.burn_amount
}

pub fn rail_batch_sum_guard(r: &RailInputs) -> bool {
    if !(0..=AMOUNT_MAX).contains(&r.burn_amount) {
        return false;
    }
    if !(0..=AMOUNT_MAX).contains(&r.batch_burn_sum_before) {
        return false;
    }
    if !(0..=SUPPLY_MAX).contains(&r.batch_burn_sum_after) {
        return false;
    }
    if r.do_burn == 0 {
        return r.batch_burn_sum_after == r.batch_burn_sum_before;
    }
    r.batch_burn_sum_after == r.batch_burn_sum_before + r.burn_amount
}

/// Stateless kernel root (the rail verifier carries no threaded state).
pub fn stateless_root() -> String {
    sha256_hex(&domain_sep_bytes("burn_rails_state", 1))
}

/// Receipt committing to the (validated) rail inputs. Only meaningful after
/// `verify_rails` returns `Ok` (all fields in range, non-negative).
pub fn rail_receipt_hash(r: &RailInputs) -> String {
    let fields = [
        r.do_burn,
        r.receipt_bound,
        r.nullifier_unused,
        r.policy_ok,
        r.burn_amount,
        r.receipt_amount,
        r.burn_budget,
        r.supply_before,
        r.supply_after,
        r.batch_burn_sum_before,
        r.batch_burn_sum_after,
    ];
    let mut buf = domain_sep_bytes("burn_rails_receipt", 1);
    for f in fields {
        buf.extend(encode_uvarint(f.max(0) as u128));
    }
    sha256_hex(&buf)
}

/// Run the four rails in the authority's order; return the first failure's
/// stable code, or `Ok(())` if all pass.
pub fn verify_rails(r: &RailInputs) -> Result<(), &'static str> {
    if !rail_replay_guard(r) {
        return Err(REJ_REPLAY_GUARD_FAILED);
    }
    if !rail_amount_guard(r) {
        return Err(REJ_AMOUNT_GUARD_FAILED);
    }
    if !rail_supply_guard(r) {
        return Err(REJ_SUPPLY_GUARD_FAILED);
    }
    if !rail_batch_sum_guard(r) {
        return Err(REJ_BATCH_SUM_GUARD_FAILED);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn no_burn() -> RailInputs {
        RailInputs {
            do_burn: 0,
            receipt_bound: 0,
            nullifier_unused: 0,
            policy_ok: 0,
            burn_amount: 0,
            receipt_amount: 0,
            burn_budget: 0,
            supply_before: 100,
            supply_after: 100,
            batch_burn_sum_before: 0,
            batch_burn_sum_after: 0,
        }
    }

    fn burn(amount: i64) -> RailInputs {
        RailInputs {
            do_burn: 1,
            receipt_bound: 1,
            nullifier_unused: 1,
            policy_ok: 1,
            burn_amount: amount,
            receipt_amount: amount,
            burn_budget: amount,
            supply_before: 100,
            supply_after: 100 - amount,
            batch_burn_sum_before: 0,
            batch_burn_sum_after: amount,
        }
    }

    #[test]
    fn no_burn_is_valid() {
        assert_eq!(verify_rails(&no_burn()), Ok(()));
    }

    #[test]
    fn well_formed_burn_is_valid() {
        assert_eq!(verify_rails(&burn(10)), Ok(()));
    }

    #[test]
    fn replay_gate_blocks_unbound_burn() {
        let mut r = burn(10);
        r.receipt_bound = 0;
        assert_eq!(verify_rails(&r), Err(REJ_REPLAY_GUARD_FAILED));
    }

    #[test]
    fn budget_floor_blocks_overspend() {
        let mut r = burn(10);
        r.burn_budget = 5; // budget < burn_amount
        assert_eq!(verify_rails(&r), Err(REJ_AMOUNT_GUARD_FAILED));
    }

    #[test]
    fn supply_must_decrease_by_burn() {
        let mut r = burn(10);
        r.supply_after = 95; // should be 90
        assert_eq!(verify_rails(&r), Err(REJ_SUPPLY_GUARD_FAILED));
    }

    #[test]
    fn batch_accumulator_must_add_burn() {
        let mut r = burn(10);
        r.batch_burn_sum_after = 5; // should be 10
        assert_eq!(verify_rails(&r), Err(REJ_BATCH_SUM_GUARD_FAILED));
    }

    #[test]
    fn out_of_range_amount_fails_amount_rail() {
        let mut r = burn(1);
        r.burn_amount = AMOUNT_MAX + 1;
        r.receipt_amount = AMOUNT_MAX + 1;
        assert_eq!(verify_rails(&r), Err(REJ_AMOUNT_GUARD_FAILED));
    }
}

// ---------------------------------------------------------------------------
// CBC_CORE_V0 — Kani contracts on the ACTUAL runtime burn-rail core.
//
// `verify_rails` composes the four consensus rails that gate a burn-accounting
// tuple after the Python envelope has extracted integer fields. The contract is
// intentionally about the rail core, not the receipt JSON/canonical-hash shell:
// TOTALITY holds over all `i64` inputs, and accept obligations state the exact
// no-burn / burn conservation laws enforced by the running verifier. Rejection
// order is checked by the ordinary unit and Python<->Rust differential tests.
// Run: `cargo kani -p zenodex-runtime-core --harness burn_receipts::kani_contracts`.
// ---------------------------------------------------------------------------
#[cfg(kani)]
mod kani_contracts {
    use super::*;

    fn any_rails() -> RailInputs {
        RailInputs {
            do_burn: kani::any(),
            receipt_bound: kani::any(),
            nullifier_unused: kani::any(),
            policy_ok: kani::any(),
            burn_amount: kani::any(),
            receipt_amount: kani::any(),
            burn_budget: kani::any(),
            supply_before: kani::any(),
            supply_after: kani::any(),
            batch_burn_sum_before: kani::any(),
            batch_burn_sum_after: kani::any(),
        }
    }

    /// TOTALITY. For arbitrary signed rail fields, the rail verifier never
    /// panics or overflows. The only additions/subtractions are reached after
    /// the small rail-domain checks have bounded the operands.
    #[kani::proof]
    fn verify_rails_is_total() {
        let r = any_rails();
        let _ = verify_rails(&r);
    }

    /// ACCEPT => EXACT RAIL SEMANTICS. Any accepted tuple is either a no-burn
    /// no-op or a positive burn whose budget, receipt amount, supply delta, and
    /// batch accumulator delta all agree exactly.
    #[kani::proof]
    fn accepted_rails_enforce_conservation() {
        let r = any_rails();
        if verify_rails(&r).is_ok() {
            assert!(r.do_burn == 0 || r.do_burn == 1);
            assert!((0..=AMOUNT_MAX).contains(&r.burn_amount));
            assert!((0..=AMOUNT_MAX).contains(&r.receipt_amount));
            assert!((0..=AMOUNT_MAX).contains(&r.burn_budget));
            assert!((0..=SUPPLY_MAX).contains(&r.supply_before));
            assert!((0..=SUPPLY_MAX).contains(&r.supply_after));
            assert!((0..=AMOUNT_MAX).contains(&r.batch_burn_sum_before));
            assert!((0..=SUPPLY_MAX).contains(&r.batch_burn_sum_after));

            if r.do_burn == 0 {
                assert_eq!(r.burn_amount, 0);
                assert_eq!(r.receipt_amount, 0);
                assert_eq!(r.supply_after, r.supply_before);
                assert_eq!(r.batch_burn_sum_after, r.batch_burn_sum_before);
            } else {
                assert_eq!(r.receipt_bound, 1);
                assert_eq!(r.nullifier_unused, 1);
                assert_eq!(r.policy_ok, 1);
                assert!(r.burn_amount > 0);
                assert_eq!(r.receipt_amount, r.burn_amount);
                assert!(r.burn_budget >= r.burn_amount);
                assert!(r.supply_before >= r.burn_amount);
                assert_eq!(r.supply_after, r.supply_before - r.burn_amount);
                assert_eq!(
                    r.batch_burn_sum_after,
                    r.batch_burn_sum_before + r.burn_amount
                );
            }
        }
    }

    /// NON-VACUITY. Kani must find accepted no-burn, accepted burn, and rejected
    /// tuples. These covers make a constant-reject verifier fail this harness.
    #[kani::proof]
    fn covers_are_reachable() {
        let r = any_rails();
        let res = verify_rails(&r);
        kani::cover!(res.is_ok() && r.do_burn == 0);
        kani::cover!(res.is_ok() && r.do_burn == 1);
        kani::cover!(res.is_err());
    }
}
