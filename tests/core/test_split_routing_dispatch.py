"""Direct tests for `src/core/split_routing_dispatch.py`.

These tests cover:
- deterministic canonicalization (pool_id ordering + tie-break rules)
- exactness vs brute force in small domains (BVA-sized amounts)

Note: we intentionally keep trade sizes small to avoid spending lots of CPU
in per-quote curve kernels.
"""

from __future__ import annotations

import pytest

from src.core import split_routing_dispatch as dispatch_mod
from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from src.core.split_routing_dispatch import (
    SplitLegExactOutQuote,
    SplitManyPoolsExactOutQuote,
    best_split_many_pools_exact_out_for_pools,
    best_split_two_pools_exact_in_for_pools,
    best_split_two_pools_exact_out_for_pools,
    exact_out_capacity_guard_for_pools,
    exact_out_route_canonical_key,
    exact_out_route_canonical_key_for_legs,
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
    best_key = None
    best_q0 = int(lo)
    for q0 in range(int(lo), int(hi) + 1):
        q1 = int(Q) - int(q0)
        try:
            in0 = _quote_exact_out(p0, asset_in=asset_in, asset_out=asset_out, amount_out=q0) if q0 > 0 else 0
            in1 = _quote_exact_out(p1, asset_in=asset_in, asset_out=asset_out, amount_out=q1) if q1 > 0 else 0
        except Exception:
            continue
        tot = int(in0 + in1)
        cand_key = exact_out_route_canonical_key_for_legs(
            amount_in_total=int(tot),
            legs=tuple((pid, amt) for pid, amt in ((p0.pool_id, int(q0)), (p1.pool_id, int(q1))) if amt > 0),
        )
        if best_in is None or best_key is None or tot < best_in or (tot == best_in and cand_key < best_key):
            best_in = tot
            best_key = cand_key
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

    def test_exact_in_unexpected_quote_fault_is_not_swallowed(self, monkeypatch: pytest.MonkeyPatch) -> None:
        def broken_quote(*_args, **_kwargs) -> int:
            raise RuntimeError("dispatch exact-in quote bug")

        monkeypatch.setattr(dispatch_mod, "_quote_exact_in", broken_quote)
        p0 = _mk_pool(pool_id="pool_a", curve_tag=CURVE_TAG_CPMM, reserve0=10_000, reserve1=10_000, fee_bps=0)
        p1 = _mk_pool(
            pool_id="pool_b",
            curve_tag=CURVE_TAG_CUBIC_SUM_V1,
            reserve0=10_000,
            reserve1=10_000,
            fee_bps=0,
            curve_params={"p": 1, "q": 1},
        )

        with pytest.raises(RuntimeError, match="dispatch exact-in quote bug"):
            best_split_two_pools_exact_in_for_pools(
                p0,
                p1,
                asset_in=ASSET0,
                asset_out=ASSET1,
                amount_in_total=50,
            )

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

    def test_exact_out_unexpected_quote_fault_is_not_swallowed(self, monkeypatch: pytest.MonkeyPatch) -> None:
        def broken_quote(*_args, **_kwargs) -> int:
            raise RuntimeError("dispatch exact-out quote bug")

        monkeypatch.setattr(dispatch_mod, "_quote_exact_out", broken_quote)
        p0 = _mk_pool(pool_id="pool_a", curve_tag=CURVE_TAG_CPMM, reserve0=10_000, reserve1=10_000, fee_bps=0)
        p1 = _mk_pool(pool_id="pool_b", curve_tag=CURVE_TAG_CPMM, reserve0=10_000, reserve1=10_000, fee_bps=0)

        with pytest.raises(RuntimeError, match="dispatch exact-out quote bug"):
            best_split_two_pools_exact_out_for_pools(
                p0,
                p1,
                asset_in=ASSET0,
                asset_out=ASSET1,
                amount_out_total=50,
            )

    def test_exact_out_tie_break_uses_full_canonical_key_on_symmetric_plateau(self) -> None:
        pool_a = _mk_pool(
            pool_id="pool_a",
            curve_tag=CURVE_TAG_CPMM,
            reserve0=40,
            reserve1=15,
            fee_bps=0,
        )
        pool_b = _mk_pool(
            pool_id="pool_b",
            curve_tag=CURVE_TAG_CPMM,
            reserve0=40,
            reserve1=15,
            fee_bps=0,
        )

        q = best_split_two_pools_exact_out_for_pools(
            pool_b,
            pool_a,
            asset_in=ASSET0,
            asset_out=ASSET1,
            amount_out_total=1,
            brute_force_max=1,
        )

        assert q.pool0_id == "pool_a"
        assert q.pool1_id == "pool_b"
        assert q.amount_in_total == 3
        assert q.amount_out_0 == 1
        assert q.amount_out_1 == 0

    def test_exact_out_capacity_guard_reports_canonical_top_caps(self) -> None:
        pools = (
            _mk_pool(pool_id="pool_b", curve_tag=CURVE_TAG_CPMM, reserve0=1_000, reserve1=5, fee_bps=0),
            _mk_pool(pool_id="pool_a", curve_tag=CURVE_TAG_CPMM, reserve0=1_000, reserve1=5, fee_bps=0),
            _mk_pool(pool_id="pool_c", curve_tag=CURVE_TAG_CPMM, reserve0=1_000, reserve1=5, fee_bps=0),
        )

        guard = exact_out_capacity_guard_for_pools(
            pools,
            asset_in=ASSET0,
            asset_out=ASSET1,
            amount_out_total=9,
            max_legs=2,
        )

        assert not guard.feasible
        assert guard.capacity_upper_bound == 8
        assert guard.top_caps == (("pool_a", 4), ("pool_b", 4))

    def test_exact_out_many_pool_rejects_infeasible_max_legs_request(self) -> None:
        pools = (
            _mk_pool(pool_id="pool_a", curve_tag=CURVE_TAG_CPMM, reserve0=1_000, reserve1=5, fee_bps=0),
            _mk_pool(pool_id="pool_b", curve_tag=CURVE_TAG_CPMM, reserve0=1_000, reserve1=5, fee_bps=0),
            _mk_pool(pool_id="pool_c", curve_tag=CURVE_TAG_CPMM, reserve0=1_000, reserve1=5, fee_bps=0),
        )

        with pytest.raises(
            ValueError,
            match=r"no feasible split under max_legs constraint: requested=9 capacity_upper_bound=8 max_legs=2",
        ):
            best_split_many_pools_exact_out_for_pools(
                pools,
                asset_in=ASSET0,
                asset_out=ASSET1,
                amount_out_total=9,
                max_legs=2,
            )

    def test_exact_out_many_pool_quote_satisfies_allocation_contract(self) -> None:
        pools = (
            _mk_pool(pool_id="pool_c", curve_tag=CURVE_TAG_CPMM, reserve0=12_000, reserve1=900, fee_bps=5),
            _mk_pool(pool_id="pool_a", curve_tag=CURVE_TAG_CPMM, reserve0=10_000, reserve1=800, fee_bps=0),
            _mk_pool(pool_id="pool_b", curve_tag=CURVE_TAG_CPMM, reserve0=11_000, reserve1=850, fee_bps=3),
        )

        quote = best_split_many_pools_exact_out_for_pools(
            pools,
            asset_in=ASSET0,
            asset_out=ASSET1,
            amount_out_total=150,
            max_legs=2,
            brute_force_max=256,
        )

        assert len(quote.legs) <= 2
        assert sum(int(leg.amount_out) for leg in quote.legs) == 150
        assert sum(int(leg.amount_in) for leg in quote.legs) == int(quote.amount_in_total)
        assert all(int(leg.amount_out) > 0 for leg in quote.legs)
        assert all(int(leg.amount_in) > 0 for leg in quote.legs)
        assert len({leg.pool_id for leg in quote.legs}) == len(quote.legs)

    def test_exact_out_many_pool_uses_canonical_winner_over_selected_domain(self) -> None:
        pools = (
            _mk_pool(pool_id="pool_a", curve_tag=CURVE_TAG_CPMM, reserve0=40, reserve1=20, fee_bps=0),
            _mk_pool(pool_id="pool_b", curve_tag=CURVE_TAG_CPMM, reserve0=40, reserve1=63, fee_bps=0),
            _mk_pool(pool_id="pool_c", curve_tag=CURVE_TAG_CPMM, reserve0=40, reserve1=20, fee_bps=0),
        )

        quote = best_split_many_pools_exact_out_for_pools(
            pools,
            asset_in=ASSET0,
            asset_out=ASSET1,
            amount_out_total=3,
            max_legs=3,
            max_candidates=3,
            max_iters=512,
            window=8,
            brute_force_max=16,
        )

        assert quote.amount_in_total == 2
        assert quote.legs == (
            SplitLegExactOutQuote(pool_id="pool_b", amount_out=3, amount_in=2),
        )

    def test_exact_out_many_pool_uses_repaired_prefilter_within_audited_bound(self) -> None:
        pools = (
            _mk_pool(pool_id="p0", curve_tag=CURVE_TAG_CPMM, reserve0=20, reserve1=10, fee_bps=0),
            _mk_pool(pool_id="p1", curve_tag=CURVE_TAG_CPMM, reserve0=20, reserve1=10, fee_bps=0),
            _mk_pool(pool_id="p2", curve_tag=CURVE_TAG_CPMM, reserve0=30, reserve1=15, fee_bps=0),
            _mk_pool(pool_id="p3", curve_tag=CURVE_TAG_CPMM, reserve0=30, reserve1=15, fee_bps=0),
        )

        quote = best_split_many_pools_exact_out_for_pools(
            pools,
            asset_in=ASSET0,
            asset_out=ASSET1,
            amount_out_total=4,
            max_legs=3,
            max_candidates=3,
            max_iters=512,
            window=8,
            brute_force_max=16,
            max_full_domain_pools=6,
        )

        assert quote.amount_in_total == 10
        assert quote.legs == (
            SplitLegExactOutQuote(pool_id="p0", amount_out=2, amount_in=5),
            SplitLegExactOutQuote(pool_id="p1", amount_out=2, amount_in=5),
        )

    def test_exact_out_many_pool_falls_back_outside_audited_bound(self) -> None:
        pools = (
            _mk_pool(pool_id="p0", curve_tag=CURVE_TAG_CPMM, reserve0=20, reserve1=10, fee_bps=0),
            _mk_pool(pool_id="p1", curve_tag=CURVE_TAG_CPMM, reserve0=20, reserve1=10, fee_bps=0),
            _mk_pool(pool_id="p2", curve_tag=CURVE_TAG_CPMM, reserve0=30, reserve1=15, fee_bps=0),
            _mk_pool(pool_id="p3", curve_tag=CURVE_TAG_CPMM, reserve0=30, reserve1=15, fee_bps=0),
        )

        quote = best_split_many_pools_exact_out_for_pools(
            pools,
            asset_in=ASSET0,
            asset_out=ASSET1,
            amount_out_total=4,
            max_legs=3,
            max_candidates=3,
            max_iters=512,
            window=8,
            brute_force_max=16,
            max_full_domain_pools=3,
        )

        assert quote.amount_in_total == 10
        assert quote.legs == (
            SplitLegExactOutQuote(pool_id="p0", amount_out=2, amount_in=5),
            SplitLegExactOutQuote(pool_id="p2", amount_out=2, amount_in=5),
        )

    def test_exact_out_quote_rejects_partial_allocation_state(self) -> None:
        with pytest.raises(ValueError, match="amount_out_total must equal sum of leg outputs"):
            SplitManyPoolsExactOutQuote(
                amount_out_total=10,
                amount_in_total=11,
                legs=(SplitLegExactOutQuote(pool_id="pool_a", amount_out=9, amount_in=11),),
            )

    def test_exact_out_canonical_key_prefers_fewer_legs_then_lex(self) -> None:
        one_leg = SplitManyPoolsExactOutQuote(
            amount_out_total=10,
            amount_in_total=11,
            legs=(SplitLegExactOutQuote(pool_id="pool_b", amount_out=10, amount_in=11),),
        )
        two_legs_lex_low = SplitManyPoolsExactOutQuote(
            amount_out_total=10,
            amount_in_total=11,
            legs=(
                SplitLegExactOutQuote(pool_id="pool_a", amount_out=4, amount_in=4),
                SplitLegExactOutQuote(pool_id="pool_c", amount_out=6, amount_in=7),
            ),
        )
        two_legs_lex_high = SplitManyPoolsExactOutQuote(
            amount_out_total=10,
            amount_in_total=11,
            legs=(
                SplitLegExactOutQuote(pool_id="pool_b", amount_out=4, amount_in=4),
                SplitLegExactOutQuote(pool_id="pool_c", amount_out=6, amount_in=7),
            ),
        )

        assert exact_out_route_canonical_key(one_leg) < exact_out_route_canonical_key(two_legs_lex_low)
        assert exact_out_route_canonical_key(two_legs_lex_low) < exact_out_route_canonical_key(two_legs_lex_high)

    def test_exact_out_canonical_key_helper_sorts_legs_by_pool_id(self) -> None:
        key = exact_out_route_canonical_key_for_legs(
            amount_in_total=11,
            legs=(("pool_c", 6), ("pool_a", 4)),
        )

        assert key.amount_in_total == 11
        assert key.leg_count == 2
        assert key.legs_lex == (("pool_a", 4), ("pool_c", 6))
