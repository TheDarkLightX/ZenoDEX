//! Pure verdict kernel for the ZenoDEX governance gates (Rust mirror).
//!
//! Three implementations of the SAME Boolean gates exist and are differentially
//! bound: the Tau specs (`src/tau_specs/governance/gov_*_v1.tau`, bf-layer
//! verified), the Python runtime mirror (`gov_gate.py`), and this kernel. The
//! shared boundary table (`tests/tau_specs/governance/fixtures/`
//! `gov_gate_parity_cases.json`, generated from `gov_parity_cases.py`) is run
//! against all three; none is trusted over the others.
//!
//! DOMAIN BOUNDARY (vs the Python shell): the Python mirror takes unbounded
//! Python ints and HARD-REJECTS anything outside `[0, 0xFFFF]` or any non-plain
//! int/bool (hostile-subclass defense). In Rust that entire class is
//! unrepresentable: the domain IS the type (`u16`), bools are real bools, and
//! there is no subclassing or monkeypatching. The fixture therefore contains
//! only in-domain cases (Python's out-of-domain rejections are Python-shell
//! behavior, covered by `test_gov_gate.py`). What this kernel must — and does —
//! reproduce exactly is the in-domain Boolean structure, including the
//! wrap-safe subtraction-guard forms, which map onto `checked_sub` one-to-one.
//!
//! CBC discipline: pure functions, no panics, no unwraps, checked or
//! provably-non-overflowing arithmetic only (the one widening sum is commented
//! at the site), `#[cfg(kani)]` harnesses prove no-panic + accept⇒invariant
//! over the FULL symbolic input domain — strictly stronger than the fixture.
//!
//! Scope: VERDICT kernel only. The epoch machine (state, receipts, no-op-on-
//! reject) stays in `gov_epoch.py` until that transition ports with its own
//! reject-is-no-op Kani harnesses.

#![forbid(unsafe_code)]
#![deny(clippy::arithmetic_side_effects)]

use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

pub mod epoch;

// ---------------------------------------------------------------------------
// IMMUTABLE per-surface guardrails (mirror gov_gate.py / the .tau constants).
// ---------------------------------------------------------------------------
pub const MIN_DELAY: u16 = 24;

pub const FEE_MAX_BPS: u16 = 1000;
pub const FEE_STEP_BPS: u16 = 50;

pub const SPLIT_SHARE_MAX: u16 = 10000;
pub const SPLIT_SUM: u16 = 10000;
pub const SPLIT_STEP_BPS: u16 = 500;

pub const RATIO_MIN_BPS: u16 = 10000;
pub const RATIO_MAX_BPS: u16 = 30000;
pub const RATIO_STEP_BPS: u16 = 1000;

pub const FUNDING_CAP_MAX_BPS: u16 = 200;
pub const FUNDING_STEP_BPS: u16 = 25;

pub const WHALE_STAKER_BPS_MAX: u16 = 7000;
pub const WHALE_STEP_BPS: u16 = 500;

// Trajectory tier (autonomy envelope) constants.
pub const CHARTER_TTL_MAX: u16 = 4096;
pub const GOV_COOLDOWN_EPOCHS: u16 = 48;
pub const DRIFT_WINDOW_EPOCHS: u16 = 720;
pub const EPOCH_MOVEMENT_BUDGET: u16 = 2000;

/// Wrap-safe timelock: `current >= proposal AND current - proposal >= min_delay`.
/// `checked_sub` IS the subtraction-guard: underflow (the bv[16] wrap bypass the
/// Tau harness probe caught) is unrepresentable, not just rejected.
fn timelock_ok(proposal_ts: u16, current_ts: u16, min_delay: u16) -> bool {
    current_ts
        .checked_sub(proposal_ts)
        .is_some_and(|gap| gap >= min_delay)
}

/// Bounded drift: `|next - curr| <= step` (both sides in-domain by type).
fn step_ok(curr: u16, next: u16, step: u16) -> bool {
    curr.abs_diff(next) <= step
}

// ---------------------------------------------------------------------------
// Universal gate (mirrors gov_action_bound_v1.tau / gov_gate.action_bound_ok).
// ---------------------------------------------------------------------------
#[allow(clippy::too_many_arguments)] // mirrors the Tau spec's input vector exactly
pub fn action_bound_ok(
    approved: bool,
    exec_req: bool,
    proposal_ts: u16,
    current_ts: u16,
    min_delay: u16,
    curr: u16,
    next: u16,
    lo: u16,
    hi: u16,
    step: u16,
) -> bool {
    if !exec_req {
        return true;
    }
    approved
        && timelock_ok(proposal_ts, current_ts, min_delay)
        && lo <= next
        && next <= hi
        && step_ok(curr, next, step)
}

// ---------------------------------------------------------------------------
// Per-surface pointwise gates.
// ---------------------------------------------------------------------------
pub fn fee_revision_ok(
    approved: bool,
    exec_req: bool,
    proposal_ts: u16,
    current_ts: u16,
    fee_curr_bps: u16,
    fee_next_bps: u16,
) -> bool {
    action_bound_ok(
        approved,
        exec_req,
        proposal_ts,
        current_ts,
        MIN_DELAY,
        fee_curr_bps,
        fee_next_bps,
        0,
        FEE_MAX_BPS,
        FEE_STEP_BPS,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn router_split_revision_ok(
    approved: bool,
    exec_req: bool,
    proposal_ts: u16,
    current_ts: u16,
    buyburn_next: u16,
    stakers_next: u16,
    reserve_next: u16,
    hosts_next: u16,
) -> bool {
    if !exec_req {
        return true;
    }
    let nexts = [buyburn_next, stakers_next, reserve_next, hosts_next];
    // Sum of four u16 fits u32 with room to spare (4 * 0xFFFF < u32::MAX): the
    // widening makes overflow unrepresentable, mirroring Python's exact ints.
    let sum: u32 = nexts.iter().map(|&s| u32::from(s)).sum();
    approved
        && timelock_ok(proposal_ts, current_ts, MIN_DELAY)
        && nexts.iter().all(|&s| s <= SPLIT_SHARE_MAX)
        && sum == u32::from(SPLIT_SUM)
}

#[allow(clippy::too_many_arguments)]
pub fn router_step_revision_ok(
    approved: bool,
    exec_req: bool,
    proposal_ts: u16,
    current_ts: u16,
    buyburn_next: u16,
    stakers_next: u16,
    reserve_next: u16,
    hosts_next: u16,
    buyburn_curr: u16,
    stakers_curr: u16,
    reserve_curr: u16,
    hosts_curr: u16,
) -> bool {
    let pairs = [
        (buyburn_curr, buyburn_next),
        (stakers_curr, stakers_next),
        (reserve_curr, reserve_next),
        (hosts_curr, hosts_next),
    ];
    pairs.iter().all(|&(c, n)| {
        action_bound_ok(
            approved,
            exec_req,
            proposal_ts,
            current_ts,
            MIN_DELAY,
            c,
            n,
            0,
            SPLIT_SHARE_MAX,
            SPLIT_STEP_BPS,
        )
    })
}

#[allow(clippy::too_many_arguments)]
pub fn router_revision_ok(
    approved: bool,
    exec_req: bool,
    proposal_ts: u16,
    current_ts: u16,
    buyburn_next: u16,
    stakers_next: u16,
    reserve_next: u16,
    hosts_next: u16,
    buyburn_curr: u16,
    stakers_curr: u16,
    reserve_curr: u16,
    hosts_curr: u16,
) -> bool {
    router_split_revision_ok(
        approved,
        exec_req,
        proposal_ts,
        current_ts,
        buyburn_next,
        stakers_next,
        reserve_next,
        hosts_next,
    ) && router_step_revision_ok(
        approved,
        exec_req,
        proposal_ts,
        current_ts,
        buyburn_next,
        stakers_next,
        reserve_next,
        hosts_next,
        buyburn_curr,
        stakers_curr,
        reserve_curr,
        hosts_curr,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn collateral_ratio_revision_ok(
    approved: bool,
    exec_req: bool,
    proposal_ts: u16,
    current_ts: u16,
    mcr_curr_bps: u16,
    mcr_next_bps: u16,
    ccr_curr_bps: u16,
    ccr_next_bps: u16,
) -> bool {
    if !exec_req {
        return true;
    }
    approved
        && timelock_ok(proposal_ts, current_ts, MIN_DELAY)
        && mcr_next_bps >= RATIO_MIN_BPS
        && ccr_next_bps <= RATIO_MAX_BPS
        && mcr_next_bps <= ccr_next_bps
        && step_ok(mcr_curr_bps, mcr_next_bps, RATIO_STEP_BPS)
        && step_ok(ccr_curr_bps, ccr_next_bps, RATIO_STEP_BPS)
}

pub fn whale_defense_revision_ok(
    approved: bool,
    exec_req: bool,
    proposal_ts: u16,
    current_ts: u16,
    staker_bps_curr: u16,
    staker_bps_next: u16,
) -> bool {
    action_bound_ok(
        approved,
        exec_req,
        proposal_ts,
        current_ts,
        MIN_DELAY,
        staker_bps_curr,
        staker_bps_next,
        0,
        WHALE_STAKER_BPS_MAX,
        WHALE_STEP_BPS,
    )
}

pub fn funding_rate_revision_ok(
    approved: bool,
    exec_req: bool,
    proposal_ts: u16,
    current_ts: u16,
    funding_cap_curr_bps: u16,
    funding_cap_next_bps: u16,
) -> bool {
    action_bound_ok(
        approved,
        exec_req,
        proposal_ts,
        current_ts,
        MIN_DELAY,
        funding_cap_curr_bps,
        funding_cap_next_bps,
        0,
        FUNDING_CAP_MAX_BPS,
        FUNDING_STEP_BPS,
    )
}

// ---------------------------------------------------------------------------
// Trajectory tier (pure bits; composed alongside the pointwise gates).
// ---------------------------------------------------------------------------

/// Window drift budget (mirrors gov_drift_budget_v1.tau):
/// `used <= budget AND |next - curr| <= budget - used`.
pub fn drift_budget_ok(curr: u16, next: u16, used: u16, budget: u16) -> bool {
    budget
        .checked_sub(used)
        .is_some_and(|remaining| curr.abs_diff(next) <= remaining)
}

/// Revision-spacing cooldown (mirrors gov_cooldown_v1.tau), wrap-safe.
pub fn cooldown_ok(last_revision_epoch: u16, now_epoch: u16, cooldown: u16) -> bool {
    now_epoch
        .checked_sub(last_revision_epoch)
        .is_some_and(|gap| gap >= cooldown)
}

/// Autonomy-charter validity (mirrors gov_charter_v1.tau): not revoked, ttl
/// within the constitutional cap, granted in the past, now STRICTLY inside ttl
/// (a ttl-T charter covers epochs granted..granted+T-1; ttl = 0 is dead at birth).
pub fn charter_ok(revoked: bool, granted_epoch: u16, now_epoch: u16, ttl: u16) -> bool {
    !revoked
        && ttl <= CHARTER_TTL_MAX
        && now_epoch
            .checked_sub(granted_epoch)
            .is_some_and(|age| age < ttl)
}

/// Aggregate per-revision movement budget (mirrors gov_epoch_budget_v1.tau).
/// Three u16 group sums widen to u32 (3 * 0xFFFF < u32::MAX, so the checked
/// adds cannot fail; written checked anyway — CBC style), matching the spec's
/// no-wrap-guarded chain and Python's exact-int comparison on the same set.
pub fn epoch_budget_ok(scalar_sum: u16, router_sum: u16, collateral_sum: u16, budget: u16) -> bool {
    u32::from(scalar_sum)
        .checked_add(u32::from(router_sum))
        .and_then(|s| s.checked_add(u32::from(collateral_sum)))
        .is_some_and(|total| total <= u32::from(budget))
}

// ---------------------------------------------------------------------------
// Canonical params digest (the cross-language golden-vector surface; must be
// byte-identical to gov_epoch.params_digest: sha256 over
// `[["k",v],...]` sorted by key, no whitespace).
// ---------------------------------------------------------------------------

/// The nine governed surfaces, sorted — exactly `gov_epoch.ALL_SURFACES`.
/// `params_digest`'s domain is maps over EXACTLY this key set.
pub const ALL_SURFACES: [&str; 9] = [
    "buyburn_bps",
    "ccr_bps",
    "fee_bps",
    "funding_cap_bps",
    "hosts_bps",
    "mcr_bps",
    "redeem_staker_bps",
    "reserve_bps",
    "stakers_bps",
];

/// Returns `None` unless `params` covers EXACTLY the nine governed surfaces —
/// the same contract `gov_epoch.params_digest` enforces via `_snapshot_params`
/// (unknown key or missing surface ⇒ reject). Without this, the two encoders
/// would agree on the bytes but disagree on the DOMAIN, and a digest over a
/// map Python rejects is a pin nothing on the Python side can ever match.
pub fn params_digest(params: &BTreeMap<String, u16>) -> Option<String> {
    if params.len() != ALL_SURFACES.len() {
        return None;
    }
    if !params.keys().all(|k| ALL_SURFACES.contains(&k.as_str())) {
        return None;
    }
    let mut canonical = String::from("[");
    let mut first = true;
    for (k, v) in params {
        if !first {
            canonical.push(',');
        }
        first = false;
        canonical.push_str("[\"");
        canonical.push_str(k);
        canonical.push_str("\",");
        canonical.push_str(itoa(*v).as_str());
        canonical.push(']');
    }
    canonical.push(']');
    let mut hasher = Sha256::new();
    hasher.update(canonical.as_bytes());
    Some(hex::encode(hasher.finalize()))
}

/// Minimal integer formatter (avoids format! machinery in the kernel path).
pub(crate) fn itoa_u16(v: u16) -> String {
    itoa(v)
}

fn itoa(v: u16) -> String {
    let mut n = v;
    let mut buf = [0u8; 5];
    let mut i = buf.len();
    loop {
        i = i.saturating_sub(1);
        buf[i] = b'0'.saturating_add((n % 10) as u8);
        n /= 10;
        if n == 0 {
            break;
        }
    }
    String::from_utf8_lossy(&buf[i..]).into_owned()
}

// ---------------------------------------------------------------------------
// Unit teeth (mirror test_gov_gate.py's key cases; the full boundary table runs
// in tests/parity.rs against the shared fixture).
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fee_teeth() {
        assert!(fee_revision_ok(true, true, 0, 24, 500, 550));
        assert!(!fee_revision_ok(true, true, 0, 24, 500, 1001)); // cap
        assert!(!fee_revision_ok(true, true, 0, 24, 0, 200)); // step
        assert!(!fee_revision_ok(false, true, 0, 24, 500, 550)); // approval
        assert!(!fee_revision_ok(true, true, 100, 110, 500, 500)); // timelock gap 10
        assert!(fee_revision_ok(false, false, 0, 0, 500, 9999)); // exec_req=false escape
    }

    #[test]
    fn timelock_wrap_bypass_unrepresentable() {
        // proposal near 2^16: the naive add-form would wrap below current.
        assert!(!fee_revision_ok(true, true, 0xFFF0, 0x0008, 500, 500));
    }

    #[test]
    fn trajectory_teeth() {
        assert!(drift_budget_ok(500, 520, 20, 150));
        assert!(drift_budget_ok(500, 470, 120, 150)); // boundary: delta == remaining
        assert!(!drift_budget_ok(500, 520, 140, 150));
        assert!(!drift_budget_ok(500, 501, 150, 150)); // exhausted blocks minimal move
        assert!(!drift_budget_ok(0, 0, 200, 150)); // used > budget rejects even a hold
        assert!(cooldown_ok(0, 48, 48));
        assert!(!cooldown_ok(100, 110, 24));
        assert!(!cooldown_ok(65520, 8, 24)); // wrap probe
        assert!(charter_ok(false, 0, 10, 24));
        assert!(!charter_ok(true, 0, 10, 24));
        assert!(!charter_ok(false, 0, 24, 24)); // expired at granted+ttl
        assert!(!charter_ok(false, 0, 10, 4097)); // constitutional cap
        assert!(!charter_ok(false, 65520, 8, 4095)); // future grant wrap probe
        assert!(!charter_ok(false, 0, 0, 0)); // dead at birth
        assert!(epoch_budget_ok(60, 400, 0, 600));
        assert!(!epoch_budget_ok(300, 300, 100, 600));
        assert!(!epoch_budget_ok(65535, 1, 0, 256)); // would wrap in bv[16]
    }

    fn full_params(fee: u16) -> BTreeMap<String, u16> {
        let vals: [(&str, u16); 9] = [
            ("fee_bps", fee),
            ("funding_cap_bps", 100),
            ("redeem_staker_bps", 6000),
            ("buyburn_bps", 6000),
            ("stakers_bps", 0),
            ("reserve_bps", 2000),
            ("hosts_bps", 2000),
            ("mcr_bps", 11000),
            ("ccr_bps", 15000),
        ];
        vals.iter().map(|(k, v)| (k.to_string(), *v)).collect()
    }

    #[test]
    fn digest_formatter_exact() {
        assert_eq!(itoa(0), "0");
        assert_eq!(itoa(7), "7");
        assert_eq!(itoa(65535), "65535");
        let d = params_digest(&full_params(500)).expect("exact surface set");
        assert_eq!(d.len(), 64);
    }

    #[test]
    fn digest_contract_matches_python_domain() {
        // gov_epoch.params_digest hard-rejects unknown keys and missing surfaces;
        // the Rust encoder must refuse the same maps, or a pinned digest could
        // exist that nothing on the Python side can ever reproduce.
        let mut missing = full_params(500);
        missing.remove("fee_bps");
        assert!(params_digest(&missing).is_none()); // missing surface
        let mut extra = full_params(500);
        extra.insert("charter_ttl".to_string(), 1u16);
        assert!(params_digest(&extra).is_none()); // unknown key (10 entries)
        let mut renamed = full_params(500);
        renamed.remove("fee_bps");
        renamed.insert("Bad Key".to_string(), 500u16);
        assert!(params_digest(&renamed).is_none()); // unknown key (9 entries)
        assert!(params_digest(&BTreeMap::from([("fee_bps".to_string(), 1u16)])).is_none());
    }
}

// ---------------------------------------------------------------------------
// Kani harnesses: no-panic + accept⇒invariant over the FULL symbolic domain.
// Run: cargo kani -p zenodex-governance-gate
// ---------------------------------------------------------------------------
#[cfg(kani)]
mod verification {
    use super::*;

    #[kani::proof]
    fn action_bound_no_panic_and_accept_invariants() {
        let (approved, exec_req): (bool, bool) = (kani::any(), kani::any());
        let (p, c, d): (u16, u16, u16) = (kani::any(), kani::any(), kani::any());
        let (curr, next): (u16, u16) = (kani::any(), kani::any());
        let (lo, hi, step): (u16, u16, u16) = (kani::any(), kani::any(), kani::any());
        let ok = action_bound_ok(approved, exec_req, p, c, d, curr, next, lo, hi, step);
        if ok && exec_req {
            assert!(approved);
            assert!(c >= p && c - p >= d);
            assert!(lo <= next && next <= hi);
            assert!(curr.abs_diff(next) <= step);
        }
    }

    #[kani::proof]
    fn drift_budget_accept_invariants() {
        let (curr, next, used, budget): (u16, u16, u16, u16) =
            (kani::any(), kani::any(), kani::any(), kani::any());
        if drift_budget_ok(curr, next, used, budget) {
            assert!(used <= budget);
            assert!(curr.abs_diff(next) <= budget - used);
        }
    }

    #[kani::proof]
    fn cooldown_accept_invariants() {
        let (last, now, cd): (u16, u16, u16) = (kani::any(), kani::any(), kani::any());
        if cooldown_ok(last, now, cd) {
            assert!(now >= last && now - last >= cd);
        }
    }

    #[kani::proof]
    fn charter_accept_invariants() {
        let revoked: bool = kani::any();
        let (granted, now, ttl): (u16, u16, u16) = (kani::any(), kani::any(), kani::any());
        if charter_ok(revoked, granted, now, ttl) {
            assert!(!revoked);
            assert!(ttl <= CHARTER_TTL_MAX && ttl > 0);
            assert!(now >= granted && now - granted < ttl);
        }
    }

    #[kani::proof]
    fn epoch_budget_accept_invariants() {
        let (a, b, c, budget): (u16, u16, u16, u16) =
            (kani::any(), kani::any(), kani::any(), kani::any());
        if epoch_budget_ok(a, b, c, budget) {
            assert!(u32::from(a) + u32::from(b) + u32::from(c) <= u32::from(budget));
        }
    }

    #[kani::proof]
    fn router_split_no_panic() {
        let _ = router_split_revision_ok(
            kani::any(),
            kani::any(),
            kani::any(),
            kani::any(),
            kani::any(),
            kani::any(),
            kani::any(),
            kani::any(),
        );
    }

    #[kani::proof]
    fn collateral_accept_invariants() {
        let (approved, exec_req): (bool, bool) = (kani::any(), kani::any());
        let (p, c): (u16, u16) = (kani::any(), kani::any());
        let (mc, mn, cc, cn): (u16, u16, u16, u16) =
            (kani::any(), kani::any(), kani::any(), kani::any());
        if collateral_ratio_revision_ok(approved, exec_req, p, c, mc, mn, cc, cn) && exec_req {
            assert!(mn >= RATIO_MIN_BPS && cn <= RATIO_MAX_BPS && mn <= cn);
            assert!(mc.abs_diff(mn) <= RATIO_STEP_BPS && cc.abs_diff(cn) <= RATIO_STEP_BPS);
        }
    }
}
