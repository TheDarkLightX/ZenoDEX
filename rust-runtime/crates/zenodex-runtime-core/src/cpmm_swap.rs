//! CPMM settlement swap — per-pool exact-in / exact-out quotes with reserves
//! threaded across a batch order.
//!
//! Rust shadow of the authoritative `quote_cpmm_swap_exact_in/out`
//! (`src/kernels/python/settlement_swap_runtime_v1.py`, backed by the v8 CPMM
//! kernel). This is the consensus-critical arithmetic at the heart of batch
//! clearing: every swap-ordering strategy ultimately applies these per-swap
//! quotes against the evolving reserves. Integer-only, deterministic rounding
//! (fee = ceil, exact-in out = floor, exact-out in = ceil).
//!
//! Scope: this surface shadows the single-pool settlement *arithmetic* +
//! per-swap admission (domain bounds, trade-too-small, slippage). Multi-pool
//! aggregation, the swap-ordering heuristics (greedy/optimal-AB/MCI/CoW), and
//! liquidity ops in `src/core/batch_clearing.py` are orchestration layered on
//! top and are staged separately; see the boundary doc.

use crate::canonical::{domain_sep_bytes, encode_uvarint, sha256_hex};

pub const BPS_DENOM: u128 = 10_000;
/// Consensus domain bounds (match `src/core/domain_limits.py`).
pub const DEX_POOL_RESERVE_MAX: u128 = 3_000_000_000;
pub const DEX_SWAP_AMOUNT_MAX: u128 = 3_000_000_000;
pub const CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT: u128 = 200;

const STATE_LABEL: &str = "cpmm_pool";
const RECEIPT_LABEL: &str = "cpmm_swap_receipt";
const STATE_VERSION: u32 = 1;
const RECEIPT_VERSION: u32 = 1;

// --- Stable reject codes (mirrored by the Python harness mapping) -------------
pub const REJ_ALREADY_INITIALIZED: &str = "already_initialized";
pub const REJ_INVALID_RESERVE: &str = "invalid_reserve";
pub const REJ_INVALID_FEE_BPS: &str = "invalid_fee_bps";
pub const REJ_POOL_NOT_INITIALIZED: &str = "pool_not_initialized";
pub const REJ_RESERVE_OUT_OF_DOMAIN: &str = "reserve_out_of_domain";
pub const REJ_INVALID_AMOUNT: &str = "invalid_amount";
pub const REJ_RESERVE_DOMAIN_EXCEEDED: &str = "reserve_domain_exceeded";
pub const REJ_TRADE_TOO_SMALL: &str = "trade_too_small";
pub const REJ_AMOUNT_OUT_GE_RESERVE: &str = "amount_out_ge_reserve";
pub const REJ_FEE_FULL: &str = "fee_full";
pub const REJ_OVERDELIVERY_GAP: &str = "overdelivery_gap";
pub const REJ_SLIPPAGE: &str = "slippage";

fn in_range(v: u128, lo: u128, hi: u128) -> bool {
    lo <= v && v <= hi
}

/// `ceil(num / den)` for `den > 0` (num may be 0 -> 0).
///
/// Uses the std `div_ceil`, which is identical to `(num + den - 1) / den` for
/// `den > 0` but cannot overflow on the intermediate sum.
fn ceil_div(num: u128, den: u128) -> u128 {
    num.div_ceil(den)
}

/// Single CPMM pool. `reserve0`/`reserve1` are the constant-product reserves;
/// `fee_bps` the swap fee. `initialized` distinguishes the empty default.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Pool {
    pub initialized: bool,
    pub reserve0: u128,
    pub reserve1: u128,
    pub fee_bps: u128,
}

impl Pool {
    pub fn state_root(&self) -> String {
        let mut buf = domain_sep_bytes(STATE_LABEL, STATE_VERSION);
        buf.extend(encode_uvarint(self.initialized as u128));
        buf.extend(encode_uvarint(self.reserve0));
        buf.extend(encode_uvarint(self.reserve1));
        buf.extend(encode_uvarint(self.fee_bps));
        sha256_hex(&buf)
    }
}

/// A settled swap (or pool init). `kind`: "swap_exact_in" | "swap_exact_out" |
/// "init_pool". For init, the amount/fee fields are 0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SwapReceipt {
    pub kind: SwapKind,
    pub zero_for_one: bool,
    pub amount_in: u128,
    pub amount_out: u128,
    pub fee_total: u128,
    pub amount_out_quote: u128,
    pub overdelivery_gap: u128,
    pub gap_bps: u128,
    pub new_reserve0: u128,
    pub new_reserve1: u128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SwapKind {
    InitPool,
    ExactIn,
    ExactOut,
}

impl SwapKind {
    fn label(self) -> &'static str {
        match self {
            SwapKind::InitPool => "init_pool",
            SwapKind::ExactIn => "swap_exact_in",
            SwapKind::ExactOut => "swap_exact_out",
        }
    }
}

impl SwapReceipt {
    pub fn receipt_hash(&self) -> String {
        let mut buf = domain_sep_bytes(RECEIPT_LABEL, RECEIPT_VERSION);
        buf.extend_from_slice(b"KND");
        buf.extend(crate::canonical::encode_bytes(self.kind.label().as_bytes()));
        buf.extend_from_slice(b"DIR");
        buf.extend(encode_uvarint(self.zero_for_one as u128));
        buf.extend_from_slice(b"AIN");
        buf.extend(encode_uvarint(self.amount_in));
        buf.extend_from_slice(b"AOU");
        buf.extend(encode_uvarint(self.amount_out));
        buf.extend_from_slice(b"FEE");
        buf.extend(encode_uvarint(self.fee_total));
        buf.extend_from_slice(b"R0");
        buf.extend(encode_uvarint(self.new_reserve0));
        buf.extend_from_slice(b"R1");
        buf.extend(encode_uvarint(self.new_reserve1));
        sha256_hex(&buf)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Accepted {
    pub receipt: SwapReceipt,
    pub pool: Pool,
}

/// Initialize the pool (only valid once).
pub fn init_pool(
    pool: &Pool,
    reserve0: u128,
    reserve1: u128,
    fee_bps: u128,
) -> Result<Accepted, &'static str> {
    if pool.initialized {
        return Err(REJ_ALREADY_INITIALIZED);
    }
    if !in_range(reserve0, 1, DEX_POOL_RESERVE_MAX) || !in_range(reserve1, 1, DEX_POOL_RESERVE_MAX)
    {
        return Err(REJ_INVALID_RESERVE);
    }
    if fee_bps > BPS_DENOM {
        return Err(REJ_INVALID_FEE_BPS);
    }
    let next = Pool {
        initialized: true,
        reserve0,
        reserve1,
        fee_bps,
    };
    Ok(Accepted {
        receipt: SwapReceipt {
            kind: SwapKind::InitPool,
            zero_for_one: false,
            amount_in: 0,
            amount_out: 0,
            fee_total: 0,
            amount_out_quote: 0,
            overdelivery_gap: 0,
            gap_bps: 0,
            new_reserve0: reserve0,
            new_reserve1: reserve1,
        },
        pool: next,
    })
}

/// Return `(reserve_in, reserve_out)` for the swap direction, validating both
/// are in the reserve domain (a prior exact-out can push a reserve out of range).
fn directed_reserves(pool: &Pool, zero_for_one: bool) -> Result<(u128, u128), &'static str> {
    let (r_in, r_out) = if zero_for_one {
        (pool.reserve0, pool.reserve1)
    } else {
        (pool.reserve1, pool.reserve0)
    };
    if !in_range(r_in, 1, DEX_POOL_RESERVE_MAX) || !in_range(r_out, 1, DEX_POOL_RESERVE_MAX) {
        return Err(REJ_RESERVE_OUT_OF_DOMAIN);
    }
    Ok((r_in, r_out))
}

fn pool_after(pool: &Pool, zero_for_one: bool, new_in: u128, new_out: u128) -> Pool {
    if zero_for_one {
        Pool {
            reserve0: new_in,
            reserve1: new_out,
            ..*pool
        }
    } else {
        Pool {
            reserve0: new_out,
            reserve1: new_in,
            ..*pool
        }
    }
}

fn validate_reachable_pool_fee_bps(pool: &Pool) -> Result<u128, &'static str> {
    if pool.fee_bps > BPS_DENOM {
        return Err(REJ_INVALID_FEE_BPS);
    }
    Ok(pool.fee_bps)
}

fn checked_ceil_mul_div(
    lhs: u128,
    rhs: u128,
    denominator: u128,
    overflow_reason: &'static str,
) -> Result<u128, &'static str> {
    if denominator == 0 {
        return Err(overflow_reason);
    }
    let product = lhs.checked_mul(rhs).ok_or(overflow_reason)?;
    Ok(ceil_div(product, denominator))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ExactInCalc {
    fee_total: u128,
    amount_out: u128,
    new_in: u128,
    new_out: u128,
}

fn compute_exact_in_calc(
    reserve_in: u128,
    reserve_out: u128,
    fee_bps: u128,
    amount_in: u128,
    min_amount_out: u128,
) -> Result<ExactInCalc, &'static str> {
    let new_in = reserve_in
        .checked_add(amount_in)
        .filter(|v| *v <= DEX_POOL_RESERVE_MAX)
        .ok_or(REJ_RESERVE_DOMAIN_EXCEEDED)?;
    let fee_total = checked_ceil_mul_div(amount_in, fee_bps, BPS_DENOM, REJ_INVALID_FEE_BPS)?;
    if fee_total >= amount_in {
        // net_in <= 0
        return Err(REJ_TRADE_TOO_SMALL);
    }
    let net_in = amount_in - fee_total;
    let denominator = reserve_in
        .checked_add(net_in)
        .ok_or(REJ_RESERVE_DOMAIN_EXCEEDED)?;
    let numerator = reserve_out
        .checked_mul(net_in)
        .ok_or(REJ_RESERVE_DOMAIN_EXCEEDED)?;
    let amount_out = numerator / denominator;
    if amount_out == 0 {
        return Err(REJ_TRADE_TOO_SMALL);
    }
    if amount_out < min_amount_out {
        return Err(REJ_SLIPPAGE);
    }
    let new_out = reserve_out
        .checked_sub(amount_out)
        .ok_or(REJ_TRADE_TOO_SMALL)?;
    Ok(ExactInCalc {
        fee_total,
        amount_out,
        new_in,
        new_out,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ExactOutCalc {
    gross_in: u128,
    fee_total: u128,
    amount_out_quote: u128,
    overdelivery_gap: u128,
    gap_bps: u128,
    new_in: u128,
    new_out: u128,
}

fn compute_exact_out_calc(
    reserve_in: u128,
    reserve_out: u128,
    fee_bps: u128,
    amount_out: u128,
    max_amount_in: u128,
    max_overdelivery_gap_bps: u128,
) -> Result<ExactOutCalc, &'static str> {
    if max_overdelivery_gap_bps > BPS_DENOM {
        return Err(REJ_OVERDELIVERY_GAP);
    }
    if amount_out >= reserve_out {
        return Err(REJ_AMOUNT_OUT_GE_RESERVE);
    }
    if fee_bps > BPS_DENOM {
        return Err(REJ_INVALID_FEE_BPS);
    }
    if fee_bps == BPS_DENOM {
        return Err(REJ_FEE_FULL);
    }
    let reserve_delta = reserve_out - amount_out;
    let net_in = checked_ceil_mul_div(
        reserve_in,
        amount_out,
        reserve_delta,
        REJ_RESERVE_DOMAIN_EXCEEDED,
    )?;
    let gross_in = checked_ceil_mul_div(
        net_in,
        BPS_DENOM,
        BPS_DENOM - fee_bps,
        REJ_RESERVE_DOMAIN_EXCEEDED,
    )?;
    let fee_total = gross_in - net_in;
    let net_in_actual = gross_in - fee_total;
    let quote_denominator = reserve_in
        .checked_add(net_in_actual)
        .ok_or(REJ_RESERVE_DOMAIN_EXCEEDED)?;
    let quote_numerator = reserve_out
        .checked_mul(net_in_actual)
        .ok_or(REJ_RESERVE_DOMAIN_EXCEEDED)?;
    let amount_out_quote = quote_numerator / quote_denominator;
    let new_in = reserve_in
        .checked_add(gross_in)
        .filter(|v| *v <= DEX_POOL_RESERVE_MAX)
        .ok_or(REJ_RESERVE_DOMAIN_EXCEEDED)?;
    let overdelivery_gap = amount_out_quote.saturating_sub(amount_out);
    let gap_bps = checked_ceil_mul_div(
        overdelivery_gap,
        BPS_DENOM,
        amount_out,
        REJ_OVERDELIVERY_GAP,
    )?;
    if gap_bps > max_overdelivery_gap_bps {
        return Err(REJ_OVERDELIVERY_GAP);
    }
    if gross_in > max_amount_in {
        return Err(REJ_SLIPPAGE);
    }
    let new_out = reserve_out - amount_out;
    Ok(ExactOutCalc {
        gross_in,
        fee_total,
        amount_out_quote,
        overdelivery_gap,
        gap_bps,
        new_in,
        new_out,
    })
}

/// Exact-in settlement swap. `min_amount_out` is the slippage floor.
pub fn swap_exact_in(
    pool: &Pool,
    zero_for_one: bool,
    amount_in: u128,
    min_amount_out: u128,
) -> Result<Accepted, &'static str> {
    if !pool.initialized {
        return Err(REJ_POOL_NOT_INITIALIZED);
    }
    let (reserve_in, reserve_out) = directed_reserves(pool, zero_for_one)?;
    if !in_range(amount_in, 1, DEX_SWAP_AMOUNT_MAX) {
        return Err(REJ_INVALID_AMOUNT);
    }
    let fee_bps = validate_reachable_pool_fee_bps(pool)?;
    let calc = compute_exact_in_calc(reserve_in, reserve_out, fee_bps, amount_in, min_amount_out)?;
    Ok(Accepted {
        receipt: SwapReceipt {
            kind: SwapKind::ExactIn,
            zero_for_one,
            amount_in,
            amount_out: calc.amount_out,
            fee_total: calc.fee_total,
            amount_out_quote: calc.amount_out,
            overdelivery_gap: 0,
            gap_bps: 0,
            new_reserve0: if zero_for_one {
                calc.new_in
            } else {
                calc.new_out
            },
            new_reserve1: if zero_for_one {
                calc.new_out
            } else {
                calc.new_in
            },
        },
        pool: pool_after(pool, zero_for_one, calc.new_in, calc.new_out),
    })
}

/// Exact-out settlement swap. `max_amount_in` is the slippage cap.
pub fn swap_exact_out(
    pool: &Pool,
    zero_for_one: bool,
    amount_out: u128,
    max_amount_in: u128,
) -> Result<Accepted, &'static str> {
    swap_exact_out_with_max_gap_bps(
        pool,
        zero_for_one,
        amount_out,
        max_amount_in,
        CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
    )
}

pub fn swap_exact_out_with_max_gap_bps(
    pool: &Pool,
    zero_for_one: bool,
    amount_out: u128,
    max_amount_in: u128,
    max_overdelivery_gap_bps: u128,
) -> Result<Accepted, &'static str> {
    if !pool.initialized {
        return Err(REJ_POOL_NOT_INITIALIZED);
    }
    let (reserve_in, reserve_out) = directed_reserves(pool, zero_for_one)?;
    if !in_range(amount_out, 1, DEX_SWAP_AMOUNT_MAX) {
        return Err(REJ_INVALID_AMOUNT);
    }
    let calc = compute_exact_out_calc(
        reserve_in,
        reserve_out,
        pool.fee_bps,
        amount_out,
        max_amount_in,
        max_overdelivery_gap_bps,
    )?;
    Ok(Accepted {
        receipt: SwapReceipt {
            kind: SwapKind::ExactOut,
            zero_for_one,
            amount_in: calc.gross_in,
            amount_out,
            fee_total: calc.fee_total,
            amount_out_quote: calc.amount_out_quote,
            overdelivery_gap: calc.overdelivery_gap,
            gap_bps: calc.gap_bps,
            new_reserve0: if zero_for_one {
                calc.new_in
            } else {
                calc.new_out
            },
            new_reserve1: if zero_for_one {
                calc.new_out
            } else {
                calc.new_in
            },
        },
        pool: pool_after(pool, zero_for_one, calc.new_in, calc.new_out),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inited() -> Pool {
        init_pool(&Pool::default(), 1_000_000, 1_000_000, 30)
            .unwrap()
            .pool
    }

    #[test]
    fn init_then_swap_exact_in_conserves_k() {
        let p = inited();
        let k_before = p.reserve0 * p.reserve1;
        let acc = swap_exact_in(&p, true, 10_000, 0).unwrap();
        // Constant-product invariant: k must not decrease.
        assert!(acc.pool.reserve0 * acc.pool.reserve1 >= k_before);
        assert_eq!(acc.pool.reserve0, p.reserve0 + 10_000);
        assert!(acc.receipt.amount_out > 0);
    }

    #[test]
    fn exact_out_delivers_requested_and_holds_k() {
        let p = inited();
        let k_before = p.reserve0 * p.reserve1;
        let acc = swap_exact_out(&p, true, 5_000, u128::MAX).unwrap();
        assert_eq!(acc.receipt.amount_out, 5_000);
        assert_eq!(acc.pool.reserve1, p.reserve1 - 5_000);
        assert!(acc.pool.reserve0 * acc.pool.reserve1 >= k_before);
    }

    #[test]
    fn rejections() {
        let p = inited();
        assert_eq!(init_pool(&p, 1, 1, 1), Err(REJ_ALREADY_INITIALIZED));
        assert_eq!(
            swap_exact_in(&Pool::default(), true, 1, 0),
            Err(REJ_POOL_NOT_INITIALIZED)
        );
        assert_eq!(swap_exact_in(&p, true, 0, 0), Err(REJ_INVALID_AMOUNT));
        assert_eq!(
            swap_exact_in(&p, true, DEX_SWAP_AMOUNT_MAX, 0),
            Err(REJ_RESERVE_DOMAIN_EXCEEDED)
        );
        // slippage: demand more than the pool can give.
        assert_eq!(
            swap_exact_in(&p, true, 10_000, 1_000_000_000),
            Err(REJ_SLIPPAGE)
        );
        assert_eq!(swap_exact_out(&p, true, 5_000, 1), Err(REJ_SLIPPAGE));
        assert_eq!(
            swap_exact_out(&p, true, 1_000_000, u128::MAX),
            Err(REJ_AMOUNT_OUT_GE_RESERVE)
        );
    }

    #[test]
    fn exact_out_rejects_reserve_domain_exceeded() {
        let p = init_pool(&Pool::default(), DEX_POOL_RESERVE_MAX, 1_000_000, 30)
            .unwrap()
            .pool;
        assert_eq!(
            swap_exact_out(&p, true, 1, u128::MAX),
            Err(REJ_RESERVE_DOMAIN_EXCEEDED)
        );
    }

    #[test]
    fn exact_out_rejects_reserve_domain_before_gap_policy_when_both_trip() {
        let p = init_pool(&Pool::default(), 1_000_000, 2_613_288_063, 9_999)
            .unwrap()
            .pool;
        assert_eq!(
            swap_exact_out_with_max_gap_bps(&p, true, 884_635_356, u128::MAX, 0),
            Err(REJ_RESERVE_DOMAIN_EXCEEDED)
        );
    }

    #[test]
    fn exact_out_enforces_overdelivery_gap_policy() {
        let p = init_pool(&Pool::default(), 1, 4, 30).unwrap().pool;
        assert_eq!(
            swap_exact_out(&p, true, 1, u128::MAX),
            Err(REJ_OVERDELIVERY_GAP)
        );
        let accepted = swap_exact_out_with_max_gap_bps(&p, true, 1, u128::MAX, BPS_DENOM).unwrap();
        assert_eq!(accepted.receipt.amount_out_quote, 2);
        assert_eq!(accepted.receipt.overdelivery_gap, 1);
        assert_eq!(accepted.receipt.gap_bps, BPS_DENOM);
    }

    #[test]
    fn tiny_trade_rejected() {
        let p = init_pool(&Pool::default(), 1_000_000, 1, 0).unwrap().pool;
        // reserve_out == 1, a swap yields amount_out == 0 -> trade_too_small.
        assert_eq!(swap_exact_in(&p, true, 1, 0), Err(REJ_TRADE_TOO_SMALL));
    }

    #[test]
    fn initialized_swaps_reject_invalid_fee_without_panic() {
        let p = Pool {
            initialized: true,
            reserve0: 1_000_000,
            reserve1: 1_000_000,
            fee_bps: BPS_DENOM + 1,
        };
        assert_eq!(swap_exact_in(&p, true, 10_000, 0), Err(REJ_INVALID_FEE_BPS));
        assert_eq!(
            swap_exact_out(&p, true, 5_000, u128::MAX),
            Err(REJ_INVALID_FEE_BPS)
        );
    }

    #[test]
    fn checked_ceil_mul_div_rejects_zero_denominator() {
        assert_eq!(
            checked_ceil_mul_div(1, 1, 0, REJ_RESERVE_DOMAIN_EXCEEDED),
            Err(REJ_RESERVE_DOMAIN_EXCEEDED)
        );
    }
}

// ---------------------------------------------------------------------------
// CBC_CORE_V0 — Kani contracts on the ACTUAL CPMM settlement-swap transitions.
//
// These harnesses target the tractable part of the running public transitions:
// pool initialization, uninitialized-pool fail-closed behavior, and concrete
// non-vacuity witnesses through exact-in/exact-out. Full symbolic exact-in/out
// arithmetic over `u128` multiplication/division timed out under CBMC. That
// contract stays covered by ESSO/Lean plus property/differential tests until the
// swap formulas are decomposed into smaller checked helpers.
// ---------------------------------------------------------------------------
#[cfg(kani)]
mod kani_contracts {
    use super::*;

    /// TOTALITY. `init_pool` has no multiplication or division, so it is total
    /// for arbitrary reserves, fees, and prior pool state.
    #[kani::proof]
    fn init_pool_is_total() {
        let pool = Pool {
            initialized: kani::any(),
            reserve0: kani::any(),
            reserve1: kani::any(),
            fee_bps: kani::any(),
        };
        let _ = init_pool(&pool, kani::any(), kani::any(), kani::any());
    }

    /// ACCEPT SHAPE. A successful initialization echoes validated inputs into
    /// both the new pool and the receipt.
    #[kani::proof]
    fn init_pool_accept_shape() {
        let reserve0: u128 = kani::any();
        let reserve1: u128 = kani::any();
        let fee_bps: u128 = kani::any();
        if let Ok(acc) = init_pool(&Pool::default(), reserve0, reserve1, fee_bps) {
            assert!(acc.pool.initialized);
            assert_eq!(acc.pool.reserve0, reserve0);
            assert_eq!(acc.pool.reserve1, reserve1);
            assert_eq!(acc.pool.fee_bps, fee_bps);
            assert!(acc.receipt.kind == SwapKind::InitPool);
            assert_eq!(acc.receipt.amount_in, 0);
            assert_eq!(acc.receipt.amount_out, 0);
            assert_eq!(acc.receipt.fee_total, 0);
            assert_eq!(acc.receipt.new_reserve0, reserve0);
            assert_eq!(acc.receipt.new_reserve1, reserve1);
            assert!((1..=DEX_POOL_RESERVE_MAX).contains(&reserve0));
            assert!((1..=DEX_POOL_RESERVE_MAX).contains(&reserve1));
            assert!(fee_bps <= BPS_DENOM);
        }
    }

    /// FAIL-CLOSED. An uninitialized pool rejects every swap with the stable
    /// `pool_not_initialized` code.
    #[kani::proof]
    fn uninitialized_pool_rejects_all_swaps() {
        let pool = Pool {
            initialized: false,
            reserve0: kani::any(),
            reserve1: kani::any(),
            fee_bps: kani::any(),
        };
        let zfo: bool = kani::any();
        let amt: u128 = kani::any();
        let bound: u128 = kani::any();
        assert_eq!(
            swap_exact_in(&pool, zfo, amt, bound),
            Err(REJ_POOL_NOT_INITIALIZED)
        );
        assert_eq!(
            swap_exact_out(&pool, zfo, amt, bound),
            Err(REJ_POOL_NOT_INITIALIZED)
        );
    }

    /// CONTRACT. Fee validation handles the live boundary and malformed
    /// impossible-pool cases without entering swap arithmetic.
    #[kani::proof]
    fn fee_validation_boundary_cases() {
        let mut pool = Pool {
            initialized: true,
            reserve0: 1,
            reserve1: 1,
            fee_bps: 0,
        };
        pool.fee_bps = 0;
        assert_eq!(validate_reachable_pool_fee_bps(&pool), Ok(0));
        pool.fee_bps = BPS_DENOM;
        assert_eq!(validate_reachable_pool_fee_bps(&pool), Ok(BPS_DENOM));
        pool.fee_bps = BPS_DENOM + 1;
        assert_eq!(
            validate_reachable_pool_fee_bps(&pool),
            Err(REJ_INVALID_FEE_BPS)
        );
        pool.fee_bps = u128::MAX;
        assert_eq!(
            validate_reachable_pool_fee_bps(&pool),
            Err(REJ_INVALID_FEE_BPS)
        );
    }

    /// CONTRACT. Fee ceil-multiply/divide is total on a small symbolic domain,
    /// and it cannot charge more than the input amount. The full live `u128`
    /// division proof is currently CBMC-intractable and remains covered by
    /// differential/property tests.
    #[kani::proof]
    fn fee_ceil_mul_div_small_domain_is_total_and_bounded() {
        let amount = kani::any::<u8>() as u128;
        let fee_bps = kani::any::<u8>() as u128;

        let fee = checked_ceil_mul_div(amount, fee_bps, BPS_DENOM, REJ_INVALID_FEE_BPS).unwrap();
        assert!(fee <= amount);
        if amount == 0 || fee_bps == 0 {
            assert_eq!(fee, 0);
        }
        if fee_bps == BPS_DENOM {
            assert_eq!(fee, amount);
        }
    }

    /// CONTRACT. A zero denominator rejects before multiplication, even for
    /// arbitrary operands.
    #[kani::proof]
    fn checked_ceil_mul_div_zero_denominator_is_total() {
        let lhs: u128 = kani::any();
        let rhs: u128 = kani::any();
        assert_eq!(
            checked_ceil_mul_div(lhs, rhs, 0, REJ_RESERVE_DOMAIN_EXCEEDED),
            Err(REJ_RESERVE_DOMAIN_EXCEEDED)
        );
    }

    /// CONTRACT. Exact-in arithmetic is total on a small symbolic domain and
    /// every accepted result has the expected reserve shape.
    #[kani::proof]
    fn exact_in_calc_small_domain_total_and_accept_shape() {
        let reserve_in = kani::any::<u8>() as u128;
        let reserve_out = kani::any::<u8>() as u128;
        let fee_bps = kani::any::<u8>() as u128;
        let amount_in = kani::any::<u8>() as u128;
        let min_amount_out = kani::any::<u8>() as u128;

        kani::assume((1..=DEX_POOL_RESERVE_MAX).contains(&reserve_in));
        kani::assume((1..=DEX_POOL_RESERVE_MAX).contains(&reserve_out));
        kani::assume(fee_bps <= BPS_DENOM);
        kani::assume((1..=DEX_SWAP_AMOUNT_MAX).contains(&amount_in));
        kani::assume(reserve_in + amount_in <= DEX_POOL_RESERVE_MAX);

        if let Ok(calc) =
            compute_exact_in_calc(reserve_in, reserve_out, fee_bps, amount_in, min_amount_out)
        {
            assert!(calc.fee_total < amount_in);
            assert!(calc.amount_out > 0);
            assert!(calc.amount_out >= min_amount_out);
            assert_eq!(calc.new_in, reserve_in + amount_in);
            assert_eq!(calc.new_out, reserve_out - calc.amount_out);
            assert!(calc.amount_out <= reserve_out);
            assert!(calc.new_in <= DEX_POOL_RESERVE_MAX);
            assert!(calc.new_out < reserve_out);
        }
    }

    /// NON-VACUITY. Accepted exact-in/exact-out paths and representative
    /// rejects are reachable.
    #[kani::proof]
    fn covers_are_reachable() {
        let p = init_pool(&Pool::default(), 1_000_000, 1_000_000, 30)
            .unwrap()
            .pool;
        kani::cover!(swap_exact_in(&p, true, 10_000, 0).is_ok());
        kani::cover!(swap_exact_in(&p, true, 10_000, 1_000_000_000) == Err(REJ_SLIPPAGE));
        kani::cover!(swap_exact_out(&p, true, 5_000, u128::MAX).is_ok());
        kani::cover!(
            swap_exact_out(&p, true, 1_000_000, u128::MAX) == Err(REJ_AMOUNT_OUT_GE_RESERVE)
        );
        kani::cover!(init_pool(&p, 1, 1, 1) == Err(REJ_ALREADY_INITIALIZED));
    }
}
