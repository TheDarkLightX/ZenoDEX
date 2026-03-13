"""Direct tests for `src/core/split_routing_dispatch.py`.

These tests cover:
- deterministic canonicalization (pool_id ordering + tie-break rules)
- exactness vs brute force in small domains (BVA-sized amounts)

Note: we intentionally keep trade sizes small to avoid spending lots of CPU
in per-quote curve kernels.
"""

from __future__ import annotations

import pytest

from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from src.core.split_routing_dispatch import (
    best_split_two_pools_exact_in_for_pools,
    best_split_two_pools_exact_out_for_pools,
)
from src.state.pools import (
    CURVE_TAG_CPMM,
    CURVE_TAG_CUBIC_SUM_V1,
    PoolState,
    PoolStatus,
)


ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32


def _mk_pool(
    *,
    pool_id: str,
    curve_tag: str,
    reserve0: int,
    reserve1: int,
    fee_bps: int,
    curve_params=None,
) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=int(fee_bps),
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=curve_tag,
        curve_params=curve_params,
    )


def _reserves_for(pool: PoolState, *, asset_in: str, asset_out: str) -> tuple[int, int]:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    raise ValueError("pool does not support this direction")


def _quote_exact_in(pool: PoolState, *, asset_in: str, asset_out: str, amount_in: int) -> int:
    rin, rout = _reserves_for(pool, asset_in=asset_in, asset_out=asset_out)
    out, _ = swap_exact_in_for_pool(pool, reserve_in=rin, reserve_out=rout, amount_in=int(amount_in))
    return int(out)


def _quote_exact_out(pool: PoolState, *, asset_in: str, asset_out: str, amount_out: int) -> int:
    rin, rout = _reserves_for(pool, asset_in=asset_in, asset_out=asset_out)
    amount_in, _ = swap_exact_out_for_pool(pool, reserve_in=rin, reserve_out=rout, amount_out=int(amount_out))
    return int(amount_in)


def _brute_force_best_split_exact_in(
    p0: PoolState, p1: PoolState, *, asset_in: str, asset_out: str, amount_in_total: int
) -> tuple[int, int]:
    best_out: int | None = None
    best_a = 0
    for a in range(0, int(amount_in_total) + 1):
        b = int(amount_in_total) - a
        try:
            out0 = _quote_exact_in(p0, asset_in=asset_in, asset_out=asset_out, amount_in=a) if a > 0 else 0
            out1 = _quote_exact_in(p1, asset_in=asset_in, asset_out=asset_out, amount_in=b) if b > 0 else 0
        except Exception:
            continue
        tot = int(out0 + out1)
        if best_out is None or tot > best_out or (tot == best_out and a < best_a):
            best_out = tot
            best_a = a
    if best_out is None:
        raise ValueError("no feasible split")
    return int(best_out), int(best_a)


def _brute_force_best_split_exact_out(
    p0: PoolState, p1: PoolState, *, asset_in: str, asset_out: str, amount_out_total: int
) -> tuple[int, int]:
    Q = int(amount_out_total)
    # Respect the obvious reserve_out boundaries: amount_out < reserve_out.
    _rin0, rout0 = _reserves_for(p0, asset_in=asset_in, asset_out=asset_out)
    _rin1, rout1 = _reserves_for(p1, asset_in=asset_in, asset_out=asset_out)
    lo = max(0, Q - max(0, int(rout1) - 1))
    hi = min(Q, max(0, int(rout0) - 1))

    best_in: int | None = None
    best_q0 = int(lo)
    for q0 in range(int(lo), int(hi) + 1):
        q1 = int(Q) - int(q0)
        try:
            in0 = _quote_exact_out(p0, asset_in=asset_in, asset_out=asset_out, amount_out=q0) if q0 > 0 else 0
            in1 = _quote_exact_out(p1, asset_in=asset_in, asset_out=asset_out, amount_out=q1) if q1 > 0 else 0
        except Exception:
            continue
        tot = int(in0 + in1)
        if best_in is None or tot < best_in or (tot == best_in and q0 < best_q0):
            best_in = tot
            best_q0 = int(q0)
    if best_in is None:
        raise ValueError("no feasible split")
    return int(best_in), int(best_q0)


class TestSplitRoutingDispatch:
    @pytest.mark.parametrize(
        "amount_in_total,reason",
        [
            (-1, "just below min=1"),
            (0, "at zero"),
        ],
    )
    def test_exact_in_amount_total_rejected(self, amount_in_total: int, reason: str) -> None:
        p0 = _mk_pool(pool_id="pool_a", curve_tag=CURVE_TAG_CPMM, reserve0=10_000, reserve1=10_000, fee_bps=0)
        p1 = _mk_pool(pool_id="pool_b", curve_tag=CURVE_TAG_CPMM, reserve0=10_000, reserve1=10_000, fee_bps=0)
        with pytest.raises(ValueError, match="amount_in_total must be positive"):
            best_split_two_pools_exact_in_for_pools(
                p0, p1, asset_in=ASSET0, asset_out=ASSET1, amount_in_total=amount_in_total
            )

    def test_exact_in_matches_bruteforce_small_domain_and_canonicalizes_pool_order(self) -> None:
        # Intentionally pass pools in reverse order; solver should canonicalize by pool_id.
        pool_lo = _mk_pool(
            pool_id="pool_a",
            curve_tag=CURVE_TAG_CPMM,
            reserve0=50_000,
            reserve1=50_000,
            fee_bps=30,
        )
        pool_hi = _mk_pool(
            pool_id="pool_b",
            curve_tag=CURVE_TAG_CUBIC_SUM_V1,
            reserve0=60_000,
            reserve1=40_000,
            fee_bps=10,
            curve_params={"p": 1, "q": 1},
        )

        amt = 50
        q = best_split_two_pools_exact_in_for_pools(
            pool_hi, pool_lo, asset_in=ASSET0, asset_out=ASSET1, amount_in_total=amt
        )
        assert q.pool0_id == "pool_a"
        assert q.pool1_id == "pool_b"

        best_out_bf, best_a_bf = _brute_force_best_split_exact_in(
            pool_lo, pool_hi, asset_in=ASSET0, asset_out=ASSET1, amount_in_total=amt
        )
        assert q.amount_out_total == best_out_bf
        assert q.amount_in_0 == best_a_bf
        assert q.amount_in_0 + q.amount_in_1 == amt

        # Leg quotes match the returned totals.
        out0 = _quote_exact_in(pool_lo, asset_in=ASSET0, asset_out=ASSET1, amount_in=q.amount_in_0) if q.amount_in_0 > 0 else 0
        out1 = _quote_exact_in(pool_hi, asset_in=ASSET0, asset_out=ASSET1, amount_in=q.amount_in_1) if q.amount_in_1 > 0 else 0
        assert q.amount_out_0 == out0
        assert q.amount_out_1 == out1
        assert q.amount_out_total == out0 + out1

    @pytest.mark.parametrize(
        "amount_out_total,reason",
        [
            (-1, "just below min=1"),
            (0, "at zero"),
        ],
    )
    def test_exact_out_amount_total_rejected(self, amount_out_total: int, reason: str) -> None:
        p0 = _mk_pool(pool_id="pool_a", curve_tag=CURVE_TAG_CPMM, reserve0=10_000, reserve1=10_000, fee_bps=0)
        p1 = _mk_pool(pool_id="pool_b", curve_tag=CURVE_TAG_CPMM, reserve0=10_000, reserve1=10_000, fee_bps=0)
        with pytest.raises(ValueError, match="amount_out_total must be positive"):
            best_split_two_pools_exact_out_for_pools(
                p0, p1, asset_in=ASSET0, asset_out=ASSET1, amount_out_total=amount_out_total
            )

    def test_exact_out_matches_bruteforce_small_domain(self) -> None:
        pool_lo = _mk_pool(
            pool_id="pool_a",
            curve_tag=CURVE_TAG_CPMM,
            reserve0=50_000,
            reserve1=50_000,
            fee_bps=0,
        )
        pool_hi = _mk_pool(
            pool_id="pool_b",
            curve_tag=CURVE_TAG_CPMM,
            reserve0=60_000,
            reserve1=40_000,
            fee_bps=0,
        )

        Q = 100
        q = best_split_two_pools_exact_out_for_pools(
            pool_hi, pool_lo, asset_in=ASSET0, asset_out=ASSET1, amount_out_total=Q, brute_force_max=256
        )
        # Canonical order by pool_id.
        assert q.pool0_id == "pool_a"
        assert q.pool1_id == "pool_b"

        best_in_bf, best_q0_bf = _brute_force_best_split_exact_out(
            pool_lo, pool_hi, asset_in=ASSET0, asset_out=ASSET1, amount_out_total=Q
        )
        assert q.amount_in_total == best_in_bf
        assert q.amount_out_0 == best_q0_bf
        assert q.amount_out_0 + q.amount_out_1 == Q

