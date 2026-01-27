"""
Split routing across *pool objects* (multi-curve via AMM dispatch).

This module extends `src/core/split_routing.py` (CPMM-specific) to support splitting across
arbitrary pool curve types by treating each pool as an exact-in oracle:

  out_i(a) = quote_exact_in(pool_i, a)

We then maximize `out_0(a) + out_1(D-a)` for total input `D`.

Notes:
- For CPMM pools we reuse the specialized, faster solver from `split_routing.py`.
- For non-CPMM pools we use a deterministic windowed search with bounded brute-force on small trades.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Sequence, Tuple

from ..state.balances import Amount, AssetId
from ..state.pools import CURVE_TAG_CPMM, PoolState
from .amm_dispatch import swap_exact_in_for_pool
from .split_routing import PoolXY, best_split_two_pools_exact_in, exact_out_for_pool_exact_in


@dataclass(frozen=True)
class SplitTwoPoolsQuote:
    pool0_id: str
    pool1_id: str
    amount_in_total: Amount
    amount_out_total: Amount
    amount_in_0: Amount
    amount_out_0: Amount
    amount_in_1: Amount
    amount_out_1: Amount


@dataclass(frozen=True)
class SplitLegQuote:
    pool_id: str
    amount_in: Amount
    amount_out: Amount


@dataclass(frozen=True)
class SplitManyPoolsQuote:
    amount_in_total: Amount
    amount_out_total: Amount
    legs: Tuple[SplitLegQuote, ...]


def _reserves_for(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId) -> Optional[Tuple[int, int]]:
    if pool.status.value != "ACTIVE":
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def _quote_exact_in(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in: Amount) -> int:
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    reserves = _reserves_for(pool, asset_in=asset_in, asset_out=asset_out)
    if reserves is None:
        raise ValueError("pool does not support this direction (or is inactive)")
    rin, rout = reserves
    out, _ = swap_exact_in_for_pool(pool, reserve_in=rin, reserve_out=rout, amount_in=int(amount_in))
    return int(out)


def _is_valid(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in: Amount) -> bool:
    if amount_in <= 0:
        return False
    try:
        _quote_exact_in(pool, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)
    except Exception:
        return False
    return True


def _min_valid_amount(
    pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in_total: Amount
) -> Optional[int]:
    if not _is_valid(pool, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in_total):
        return None
    lo = 1
    hi = int(amount_in_total)
    while lo < hi:
        mid = (lo + hi) // 2
        if _is_valid(pool, asset_in=asset_in, asset_out=asset_out, amount_in=int(mid)):
            hi = mid
        else:
            lo = mid + 1
    return int(lo)


def _brute_force_best_split(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
) -> Tuple[int, int]:
    if amount_in_total <= 0:
        raise ValueError("amount_in_total must be positive")
    best_out: int | None = None
    best_a = 0
    for a in range(0, int(amount_in_total) + 1):
        b = int(amount_in_total) - a
        try:
            out0 = _quote_exact_in(pool0, asset_in=asset_in, asset_out=asset_out, amount_in=a) if a > 0 else 0
            out1 = _quote_exact_in(pool1, asset_in=asset_in, asset_out=asset_out, amount_in=b) if b > 0 else 0
        except Exception:
            continue
        total = int(out0 + out1)
        if best_out is None or total > best_out or (total == best_out and a < best_a):
            best_out = total
            best_a = a
    if best_out is None:
        raise ValueError("no feasible split")
    return int(best_out), int(best_a)


def _generic_best_split_two_pools_exact_in(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    window: int,
    brute_force_max: int,
) -> Tuple[int, int]:
    if amount_in_total <= 0:
        raise ValueError("amount_in_total must be positive")
    if window < 0:
        raise ValueError("window must be non-negative")

    if int(amount_in_total) <= int(brute_force_max):
        return _brute_force_best_split(
            pool0,
            pool1,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in_total=amount_in_total,
        )

    def total_out(a: int) -> int | None:
        if not (0 <= a <= int(amount_in_total)):
            return None
        b = int(amount_in_total) - a
        try:
            out0 = _quote_exact_in(pool0, asset_in=asset_in, asset_out=asset_out, amount_in=a) if a > 0 else 0
            out1 = _quote_exact_in(pool1, asset_in=asset_in, asset_out=asset_out, amount_in=b) if b > 0 else 0
        except Exception:
            return None
        return int(out0 + out1)

    def scan_range(lo: int, hi: int) -> tuple[int, int] | None:
        if lo > hi:
            return None
        best_out = -1
        best_a = 0
        for a in range(lo, hi + 1):
            tot = total_out(a)
            if tot is None:
                continue
            if tot > best_out or (tot == best_out and a < best_a):
                best_out = tot
                best_a = a
        return None if best_out < 0 else (best_out, best_a)

    best_out = -1
    best_a = 0
    for a in (0, int(amount_in_total)):
        tot = total_out(a)
        if tot is None:
            continue
        if tot > best_out or (tot == best_out and a < best_a):
            best_out = int(tot)
            best_a = int(a)

    min0 = _min_valid_amount(pool0, asset_in=asset_in, asset_out=asset_out, amount_in_total=amount_in_total)
    min1 = _min_valid_amount(pool1, asset_in=asset_in, asset_out=asset_out, amount_in_total=amount_in_total)
    if min0 is not None and min1 is not None:
        lo_both = int(min0)
        hi_both = int(amount_in_total) - int(min1)
        if lo_both <= hi_both:
            span = int(hi_both - lo_both)
            centers = {lo_both, hi_both, (lo_both + hi_both) // 2}
            if span > 8 * int(window):
                for i in range(1, 8):
                    centers.add(lo_both + (span * i) // 8)

            best_both: tuple[int, int] | None = None
            for c in sorted(centers):
                r_lo = max(lo_both, int(c) - int(window))
                r_hi = min(hi_both, int(c) + int(window))
                cand = scan_range(r_lo, r_hi)
                if cand is None:
                    continue
                if best_both is None or cand[0] > best_both[0] or (cand[0] == best_both[0] and cand[1] < best_both[1]):
                    best_both = cand

            if best_both is not None:
                refine_out, refine_a = best_both
                half = max(1, int(window))
                while True:
                    r_lo = max(lo_both, refine_a - half)
                    r_hi = min(hi_both, refine_a + half)
                    cand = scan_range(r_lo, r_hi)
                    if cand is not None:
                        refine_out2, refine_a2 = cand
                        if refine_out2 > refine_out or (refine_out2 == refine_out and refine_a2 < refine_a):
                            refine_out, refine_a = refine_out2, refine_a2
                    if r_lo == lo_both and r_hi == hi_both:
                        break
                    if refine_a in (r_lo, r_hi):
                        half *= 2
                        if half >= span:
                            half = span
                        continue
                    break

                # Canonicalize within a local plateau.
                a0 = int(refine_a)
                while a0 > lo_both:
                    prev = total_out(a0 - 1)
                    if prev is None or int(prev) != int(refine_out):
                        break
                    a0 -= 1

                if int(refine_out) > best_out or (int(refine_out) == best_out and int(a0) < best_a):
                    best_out, best_a = int(refine_out), int(a0)

    if best_out < 0:
        raise ValueError("no feasible split")
    return int(best_out), int(best_a)


def best_split_two_pools_exact_in_for_pools(
    pool0: PoolState,
    pool1: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    window: int = 64,
) -> SplitTwoPoolsQuote:
    """
    Compute the best exact-in split across two pools for the same asset pair direction.

    Determinism:
    - Pools are ordered by `pool_id` before split optimization.
    - Ties are broken by smaller `amount_in_0` (send less to the first pool).
    """
    if amount_in_total <= 0:
        raise ValueError("amount_in_total must be positive")

    # Canonicalize pool order.
    p0, p1 = (pool0, pool1) if pool0.pool_id <= pool1.pool_id else (pool1, pool0)

    # Fast path: CPMM uses the dedicated solver.
    if p0.curve_tag == CURVE_TAG_CPMM and p1.curve_tag == CURVE_TAG_CPMM:
        r0 = _reserves_for(p0, asset_in=asset_in, asset_out=asset_out)
        r1 = _reserves_for(p1, asset_in=asset_in, asset_out=asset_out)
        if r0 is None or r1 is None:
            raise ValueError("pools do not support this direction (or are inactive)")
        rin0, rout0 = r0
        rin1, rout1 = r1
        xy0 = PoolXY(x=int(rin0), y=int(rout0), fee_bps=int(p0.fee_bps))
        xy1 = PoolXY(x=int(rin1), y=int(rout1), fee_bps=int(p1.fee_bps))
        best_out, best_a = best_split_two_pools_exact_in(xy0, xy1, int(amount_in_total), window=int(window))
        out0 = exact_out_for_pool_exact_in(xy0, best_a) if best_a > 0 else 0
        out1 = exact_out_for_pool_exact_in(xy1, int(amount_in_total) - best_a) if best_a < int(amount_in_total) else 0
        return SplitTwoPoolsQuote(
            pool0_id=p0.pool_id,
            pool1_id=p1.pool_id,
            amount_in_total=int(amount_in_total),
            amount_out_total=int(best_out),
            amount_in_0=int(best_a),
            amount_out_0=int(out0),
            amount_in_1=int(amount_in_total) - int(best_a),
            amount_out_1=int(out1),
        )

    best_out, best_a = _generic_best_split_two_pools_exact_in(
        p0,
        p1,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in_total=amount_in_total,
        window=int(window),
        brute_force_max=2048,
    )
    b = int(amount_in_total) - int(best_a)
    out0 = _quote_exact_in(p0, asset_in=asset_in, asset_out=asset_out, amount_in=int(best_a)) if best_a > 0 else 0
    out1 = _quote_exact_in(p1, asset_in=asset_in, asset_out=asset_out, amount_in=int(b)) if b > 0 else 0
    if int(out0 + out1) != int(best_out):
        # Defensive: recompute total from per-leg quotes.
        best_out = int(out0 + out1)
    return SplitTwoPoolsQuote(
        pool0_id=p0.pool_id,
        pool1_id=p1.pool_id,
        amount_in_total=int(amount_in_total),
        amount_out_total=int(best_out),
        amount_in_0=int(best_a),
        amount_out_0=int(out0),
        amount_in_1=int(b),
        amount_out_1=int(out1),
    )


def best_split_many_pools_exact_in_for_pools(
    pools: Sequence[PoolState],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in_total: Amount,
    max_legs: int = 4,
    max_candidates: int = 16,
    max_iters: int = 4096,
) -> SplitManyPoolsQuote:
    """
    Deterministic N-way split router for *parallel* pools on the same asset pair direction.

    This is an execution improvement over "pick best single pool" and "split across two pools" in
    fragmented liquidity regimes.

    Approach:
    - Treat each pool as an exact-in oracle `f_i(a)`.
    - Solve `max Σ f_i(a_i)` s.t. `Σ a_i = D`, `a_i ∈ ℕ`.
    - Use a bounded multi-stage greedy allocator (marginal-output-per-input), with deterministic tie-breaks.
    - Limit to at most `max_legs` non-zero legs and `max_candidates` candidate pools.
    """
    if amount_in_total <= 0:
        raise ValueError("amount_in_total must be positive")
    if max_legs <= 0:
        raise ValueError("max_legs must be positive")
    if max_candidates <= 0:
        raise ValueError("max_candidates must be positive")
    if max_iters <= 0:
        raise ValueError("max_iters must be positive")

    # Filter to feasible direct pools (direction + active + nonzero output at full amount).
    feasible: List[PoolState] = []
    for p in pools:
        if p.status.value != "ACTIVE":
            continue
        if _reserves_for(p, asset_in=asset_in, asset_out=asset_out) is None:
            continue
        if not _is_valid(p, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in_total):
            continue
        feasible.append(p)

    if not feasible:
        raise ValueError("no feasible pools for split")

    # Rank pools by single-pool output at full amount (desc), then pool_id (asc).
    ranked: List[Tuple[int, PoolState]] = []
    for p in feasible:
        try:
            out_full = _quote_exact_in(p, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in_total)
        except Exception:
            continue
        ranked.append((int(out_full), p))
    if not ranked:
        raise ValueError("no feasible pools for split")
    ranked.sort(key=lambda t: (-int(t[0]), t[1].pool_id))
    candidates: List[PoolState] = [p for _out, p in ranked[: min(int(max_candidates), len(ranked))]]

    # Canonicalize pool order for deterministic tie-breaks.
    candidates.sort(key=lambda p: p.pool_id)

    min_valid: Dict[str, int] = {}
    for p in candidates:
        mv = _min_valid_amount(p, asset_in=asset_in, asset_out=asset_out, amount_in_total=amount_in_total)
        if mv is None:
            continue
        min_valid[p.pool_id] = int(mv)
    if not min_valid:
        raise ValueError("no feasible pools for split")

    pools_by_id: Dict[str, PoolState] = {p.pool_id: p for p in candidates if p.pool_id in min_valid}

    quote_cache: Dict[Tuple[str, int], int] = {}

    def quote(pid: str, amt: int) -> Optional[int]:
        if amt < 0:
            return None
        if amt == 0:
            return 0
        mv = min_valid.get(pid)
        if mv is None or amt < mv:
            return None
        key = (pid, int(amt))
        if key in quote_cache:
            return quote_cache[key]
        out = _quote_exact_in(pools_by_id[pid], asset_in=asset_in, asset_out=asset_out, amount_in=int(amt))
        quote_cache[key] = int(out)
        return int(out)

    def greedy_allocate(step: int) -> Dict[str, int]:
        if step <= 0:
            raise ValueError("step must be positive")

        alloc: Dict[str, int] = {pid: 0 for pid in pools_by_id.keys()}
        used: set[str] = set()
        remaining = int(amount_in_total)

        # Seed: allocate min_valid to the best-looking pools first to allow splitting.
        seed_order = sorted(
            pools_by_id.keys(),
            key=lambda pid: (-int(quote(pid, int(amount_in_total)) or 0), pid),
        )
        for pid in seed_order:
            if remaining <= 0:
                break
            if len(used) >= int(max_legs):
                break
            mv = int(min_valid[pid])
            if mv <= 0 or mv > remaining:
                continue
            alloc[pid] = mv
            remaining -= mv
            used.add(pid)

        # If seeding chose nothing (should be rare), start with the best pool.
        if not used:
            pid0 = seed_order[0]
            mv0 = int(min_valid[pid0])
            inc0 = mv0 if mv0 <= remaining else remaining
            if inc0 <= 0:
                raise ValueError("no feasible allocation")
            alloc[pid0] = inc0
            remaining -= inc0
            used.add(pid0)

        # Greedy remainder allocation.
        while remaining > 0:
            base = min(int(step), int(remaining))
            best_pid: Optional[str] = None
            best_delta = -1
            best_inc = 1
            best_curr = 0

            for pid in pools_by_id.keys():
                curr = int(alloc.get(pid, 0))
                if curr == 0 and pid not in used and len(used) >= int(max_legs):
                    continue

                inc = int(base)
                if curr == 0:
                    mv = int(min_valid[pid])
                    if mv > inc:
                        inc = mv
                if inc <= 0 or inc > remaining:
                    continue

                out_before = quote(pid, curr) or 0
                out_after = quote(pid, curr + inc)
                if out_after is None:
                    continue
                delta = int(out_after - out_before)
                if delta < 0:
                    continue

                if best_pid is None:
                    best_pid, best_delta, best_inc, best_curr = pid, delta, inc, curr
                    continue

                # Compare marginal efficiency delta/inc as rationals: delta*best_inc ? best_delta*inc.
                lhs = int(delta) * int(best_inc)
                rhs = int(best_delta) * int(inc)
                if lhs > rhs:
                    best_pid, best_delta, best_inc, best_curr = pid, delta, inc, curr
                    continue
                if lhs < rhs:
                    continue

                # Tie-break: higher delta, then smaller current allocation (encourage splitting), then pool_id.
                if delta > best_delta:
                    best_pid, best_delta, best_inc, best_curr = pid, delta, inc, curr
                    continue
                if delta < best_delta:
                    continue
                if curr < best_curr:
                    best_pid, best_delta, best_inc, best_curr = pid, delta, inc, curr
                    continue
                if curr > best_curr:
                    continue
                if pid < best_pid:
                    best_pid, best_delta, best_inc, best_curr = pid, delta, inc, curr

            if best_pid is None:
                raise ValueError("no feasible allocation step (unexpected)")

            was_zero = alloc[best_pid] == 0
            alloc[best_pid] = int(alloc[best_pid] + best_inc)
            remaining -= int(best_inc)
            if was_zero:
                used.add(best_pid)

        return alloc

    # Multi-stage schedule: start coarse, refine until step yields <= max_iters increments.
    D = int(amount_in_total)
    step_min = max(1, D // int(max_iters))
    step = max(step_min, max(1, D // 256))

    best_alloc: Optional[Dict[str, int]] = None
    best_out = -1

    while True:
        alloc = greedy_allocate(int(step))
        total_out = 0
        legs_tmp: List[Tuple[str, int, int]] = []
        for pid, amt in alloc.items():
            if amt <= 0:
                continue
            out_amt = quote(pid, int(amt))
            if out_amt is None:
                continue
            total_out += int(out_amt)
            legs_tmp.append((pid, int(amt), int(out_amt)))

        legs_tmp.sort(key=lambda t: t[0])
        if total_out > best_out:
            best_out = int(total_out)
            best_alloc = alloc
        elif total_out == best_out and best_alloc is not None:
            # Deterministic tie-break: fewer legs, then lexicographic (pool_id, amount_in) sequence.
            best_legs = sorted([(pid, int(a)) for pid, a in best_alloc.items() if int(a) > 0], key=lambda t: t[0])
            cur_legs = sorted([(pid, int(a)) for pid, a in alloc.items() if int(a) > 0], key=lambda t: t[0])
            if len(cur_legs) < len(best_legs) or (len(cur_legs) == len(best_legs) and cur_legs < best_legs):
                best_alloc = alloc

        if step <= step_min:
            break
        step = max(step_min, step // 2)

    assert best_alloc is not None
    legs: List[SplitLegQuote] = []
    out_total = 0
    in_total = 0
    for pid in sorted(best_alloc.keys()):
        amt = int(best_alloc[pid])
        if amt <= 0:
            continue
        out_amt = quote(pid, amt)
        if out_amt is None:
            continue
        legs.append(SplitLegQuote(pool_id=pid, amount_in=int(amt), amount_out=int(out_amt)))
        in_total += int(amt)
        out_total += int(out_amt)

    # All input must be allocated.
    if in_total != int(amount_in_total):
        raise ValueError("split allocation did not consume full input (unexpected)")

    return SplitManyPoolsQuote(amount_in_total=int(amount_in_total), amount_out_total=int(out_total), legs=tuple(legs))
