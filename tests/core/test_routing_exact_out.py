from __future__ import annotations

import random

import pytest

from src.core.amm_dispatch import swap_exact_out_for_pool
from src.core.routing import (
    ExactOutTwoHopGateConfig,
    RouteHop,
    RouteLeg,
    RouteQuote,
    _quote_key,
    best_route_exact_out_2hop,
)
from src.state.pools import PoolState, PoolStatus


def _pool(pid: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id=pid,
        asset0=min(a0, a1),
        asset1=max(a0, a1),
        reserve0=r0 if a0 < a1 else r1,
        reserve1=r1 if a0 < a1 else r0,
        fee_bps=fee_bps,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def _quote_exact_out(pool: PoolState, *, asset_in: str, asset_out: str, amount_out: int) -> int | None:
    if pool.status.value != "ACTIVE":
        return None
    if amount_out <= 0:
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        rin, rout = int(pool.reserve0), int(pool.reserve1)
    elif asset_in == pool.asset1 and asset_out == pool.asset0:
        rin, rout = int(pool.reserve1), int(pool.reserve0)
    else:
        return None
    try:
        amount_in, _ = swap_exact_out_for_pool(pool, reserve_in=rin, reserve_out=rout, amount_out=int(amount_out))
    except Exception:
        return None
    return int(amount_in)


def _brute_best_route_exact_out_2hop(
    *, pools_by_id: dict[str, PoolState], asset_in: str, asset_out: str, amount_out: int
) -> RouteQuote | None:
    pools = tuple(sorted(pools_by_id.values(), key=lambda p: p.pool_id))
    best: RouteQuote | None = None

    direct_pools = [p for p in pools if ((asset_in == p.asset0 and asset_out == p.asset1) or (asset_in == p.asset1 and asset_out == p.asset0))]

    # 1-hop
    for p in direct_pools:
        amt_in = _quote_exact_out(p, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out)
        if amt_in is None:
            continue
        hop = RouteHop(p.pool_id, asset_in, asset_out, amt_in, amount_out)
        q = RouteQuote(
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amt_in,
            amount_out=amount_out,
            legs=(RouteLeg(hops=(hop,), amount_in=amt_in, amount_out=amount_out),),
        )
        if best is None or (q.amount_in < best.amount_in) or (q.amount_in == best.amount_in and _quote_key(q) < _quote_key(best)):
            best = q

    # 1-hop split across two parallel pools (2 legs, 1 hop each).
    if len(direct_pools) >= 2:
        for i in range(len(direct_pools)):
            for j in range(i + 1, len(direct_pools)):
                p0 = direct_pools[i]
                p1 = direct_pools[j]
                best_in: int | None = None
                best_q0 = 0
                for q0 in range(0, int(amount_out) + 1):
                    q1 = int(amount_out) - int(q0)
                    in0 = _quote_exact_out(p0, asset_in=asset_in, asset_out=asset_out, amount_out=q0) if q0 > 0 else 0
                    in1 = _quote_exact_out(p1, asset_in=asset_in, asset_out=asset_out, amount_out=q1) if q1 > 0 else 0
                    if in0 is None or in1 is None:
                        continue
                    tot = int(in0 + in1)
                    if best_in is None or tot < best_in or (tot == best_in and q0 < best_q0):
                        best_in = int(tot)
                        best_q0 = int(q0)
                if best_in is None:
                    continue
                q0 = int(best_q0)
                q1 = int(amount_out) - int(q0)
                in0 = _quote_exact_out(p0, asset_in=asset_in, asset_out=asset_out, amount_out=q0) if q0 > 0 else 0
                in1 = _quote_exact_out(p1, asset_in=asset_in, asset_out=asset_out, amount_out=q1) if q1 > 0 else 0
                assert in0 is not None and in1 is not None
                leg0 = RouteLeg(
                    hops=(RouteHop(p0.pool_id, asset_in, asset_out, int(in0), int(q0)),),
                    amount_in=int(in0),
                    amount_out=int(q0),
                )
                leg1 = RouteLeg(
                    hops=(RouteHop(p1.pool_id, asset_in, asset_out, int(in1), int(q1)),),
                    amount_in=int(in1),
                    amount_out=int(q1),
                )
                q = RouteQuote(
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(best_in),
                    amount_out=amount_out,
                    legs=(leg0, leg1),
                )
                if best is None or (q.amount_in < best.amount_in) or (q.amount_in == best.amount_in and _quote_key(q) < _quote_key(best)):
                    best = q

    # 2-hop
    for p1 in pools:
        if asset_in == p1.asset0:
            mid = p1.asset1
        elif asset_in == p1.asset1:
            mid = p1.asset0
        else:
            continue
        if mid == asset_out or mid == asset_in:
            continue
        for p2 in pools:
            if not ((mid == p2.asset0 and asset_out == p2.asset1) or (mid == p2.asset1 and asset_out == p2.asset0)):
                continue
            mid_in = _quote_exact_out(p2, asset_in=mid, asset_out=asset_out, amount_out=amount_out)
            if mid_in is None:
                continue
            amt_in = _quote_exact_out(p1, asset_in=asset_in, asset_out=mid, amount_out=mid_in)
            if amt_in is None:
                continue
            hop1 = RouteHop(p1.pool_id, asset_in, mid, amt_in, mid_in)
            hop2 = RouteHop(p2.pool_id, mid, asset_out, mid_in, amount_out)
            q = RouteQuote(
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=amt_in,
                amount_out=amount_out,
                legs=(RouteLeg(hops=(hop1, hop2), amount_in=amt_in, amount_out=amount_out),),
            )
            if best is None or (q.amount_in < best.amount_in) or (q.amount_in == best.amount_in and _quote_key(q) < _quote_key(best)):
                best = q

    return best


def test_best_route_exact_out_picks_direct_if_best() -> None:
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0),
        "p_ac": _pool("p_ac", "A", "C", 1000, 10, 0),
        "p_cb": _pool("p_cb", "C", "B", 10, 1000, 0),
    }
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=5)
    assert q is not None
    assert len(q.legs) == 1
    assert len(q.legs[0].hops) == 1
    assert q.legs[0].hops[0].pool_id == "p_ab"


def test_best_route_exact_out_uses_2hop_when_better() -> None:
    # Witness-style configuration: 2-hop requires less input than direct for amount_out=1.
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 2, 2, 0),
        "p_ac": _pool("p_ac", "A", "C", 1, 2, 0),
        "p_cb": _pool("p_cb", "C", "B", 1, 2, 0),
    }
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=1)
    assert q is not None
    assert len(q.legs) == 1
    assert len(q.legs[0].hops) == 2
    assert q.legs[0].hops[0].asset_in == "A"
    assert q.legs[0].hops[-1].asset_out == "B"


def test_best_route_exact_out_adaptive_gate_can_skip_low_stress_two_hop() -> None:
    # Construct a low-stress case where plain OR gate opens 2-hop search, but adaptive gate does not.
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 318, 254, 8),
        "p_ac": _pool("p_ac", "A", "C", 71, 221, 29),
        "p_cb": _pool("p_cb", "C", "B", 379, 338, 33),
    }
    amount_out = 54

    ungated = best_route_exact_out_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_out=amount_out,
        apply_two_hop_gate=False,
    )
    assert ungated is not None
    assert len(ungated.legs) == 1
    assert len(ungated.legs[0].hops) == 2

    combo = best_route_exact_out_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_out=amount_out,
        apply_two_hop_gate=True,
        gate_config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure",
            stress_threshold_bps=4000,
            pressure_threshold_e4=16_000,
        ),
    )
    assert combo is not None
    assert len(combo.legs) == 1
    assert len(combo.legs[0].hops) == 2
    assert int(combo.amount_in) == int(ungated.amount_in)

    adaptive = best_route_exact_out_2hop(
        pools_by_id=pools,
        asset_in="A",
        asset_out="B",
        amount_out=amount_out,
        apply_two_hop_gate=True,
        gate_config=ExactOutTwoHopGateConfig(
            policy="stress_or_pressure_adaptive",
            stress_threshold_bps=4000,
            pressure_threshold_e4=16_000,
            pressure_slope_e4=12_000,
        ),
    )
    assert adaptive is not None
    assert len(adaptive.legs) == 1
    assert len(adaptive.legs[0].hops) == 1
    assert int(adaptive.amount_in) > int(combo.amount_in)


def test_best_route_exact_out_piecewise_gate_reduces_low_stress_quote_work() -> None:
    # Witness: low-stress case where combo policy opens 2-hop scan but piecewise gate closes it.
    pools = {
        "p_ab": _pool("p_ab", "A", "B", 413, 260, 8),
        "p_ac": _pool("p_ac", "A", "C", 489, 184, 35),
        "p_cb": _pool("p_cb", "C", "B", 259, 60, 7),
    }
    amount_out = 9

    # Measure exact-out quote calls to show compute reduction while preserving chosen route.
    from src.core import routing as routing_mod

    orig = routing_mod._pool_quote_exact_out
    combo_calls = {"n": 0}
    piecewise_calls = {"n": 0}

    def counting_combo(*args, **kwargs):
        combo_calls["n"] = int(combo_calls["n"]) + 1
        return orig(*args, **kwargs)

    routing_mod._pool_quote_exact_out = counting_combo  # type: ignore[assignment]
    try:
        combo = best_route_exact_out_2hop(
            pools_by_id=pools,
            asset_in="A",
            asset_out="B",
            amount_out=amount_out,
            apply_two_hop_gate=True,
            gate_config=ExactOutTwoHopGateConfig(
                policy="stress_or_pressure",
                stress_threshold_bps=4000,
                pressure_threshold_e4=16_000,
            ),
        )
    finally:
        routing_mod._pool_quote_exact_out = orig  # type: ignore[assignment]

    def counting_piecewise(*args, **kwargs):
        piecewise_calls["n"] = int(piecewise_calls["n"]) + 1
        return orig(*args, **kwargs)

    routing_mod._pool_quote_exact_out = counting_piecewise  # type: ignore[assignment]
    try:
        piecewise = best_route_exact_out_2hop(
            pools_by_id=pools,
            asset_in="A",
            asset_out="B",
            amount_out=amount_out,
            apply_two_hop_gate=True,
            gate_config=ExactOutTwoHopGateConfig(
                policy="stress_or_pressure_piecewise",
                stress_threshold_bps=4000,
                piecewise_stress_cutoff_bps=1000,
                piecewise_pressure_mid_e4=15_500,
                piecewise_pressure_low_e4=22_000,
            ),
        )
    finally:
        routing_mod._pool_quote_exact_out = orig  # type: ignore[assignment]

    assert combo is not None and piecewise is not None
    assert int(combo.amount_in) == int(piecewise.amount_in)
    assert _quote_key(combo) == _quote_key(piecewise)
    assert piecewise_calls["n"] < combo_calls["n"]


def test_best_route_exact_out_tie_break_is_deterministic() -> None:
    pools = {
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
    }
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=10)
    assert q is not None
    assert len(q.legs) == 1
    assert len(q.legs[0].hops) == 1
    assert q.legs[0].hops[0].pool_id == "p1"


def test_exact_out_quote_value_error_marks_candidate_infeasible(monkeypatch: pytest.MonkeyPatch) -> None:
    from src.core import routing as routing_mod

    def infeasible_quote(*_args, **_kwargs):
        raise ValueError("candidate infeasible")

    monkeypatch.setattr(routing_mod, "swap_exact_out_for_pool", infeasible_quote)
    pools = {"p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0)}

    assert best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=10) is None


def test_exact_out_quote_unexpected_fault_is_not_swallowed(monkeypatch: pytest.MonkeyPatch) -> None:
    from src.core import routing as routing_mod

    def broken_quote(*_args, **_kwargs):
        raise RuntimeError("quote kernel bug")

    monkeypatch.setattr(routing_mod, "swap_exact_out_for_pool", broken_quote)
    pools = {"p_ab": _pool("p_ab", "A", "B", 1000, 1000, 0)}

    with pytest.raises(RuntimeError, match="quote kernel bug"):
        best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=10)


def test_best_route_exact_out_can_split_across_parallel_pools() -> None:
    pools = {
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
    }
    single = best_route_exact_out_2hop(pools_by_id={"p1": pools["p1"]}, asset_in="A", asset_out="B", amount_out=600)
    assert single is not None
    q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=600)
    assert q is not None
    assert q.amount_in < single.amount_in
    assert len(q.legs) == 2


def test_exact_out_split_unexpected_fault_is_not_swallowed(monkeypatch: pytest.MonkeyPatch) -> None:
    from src.core import routing as routing_mod

    def broken_split(*_args, **_kwargs):
        raise RuntimeError("split optimizer bug")

    monkeypatch.setattr(routing_mod, "best_split_two_pools_exact_out_for_pools", broken_split)
    pools = {
        "p2": _pool("p2", "A", "B", 1000, 1000, 0),
        "p1": _pool("p1", "A", "B", 1000, 1000, 0),
    }

    with pytest.raises(RuntimeError, match="split optimizer bug"):
        best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=600)


def test_best_route_exact_out_matches_bruteforce_on_small_random_domain() -> None:
    rng = random.Random(20260214)
    feasible = 0

    for i in range(400):
        pools = {
            "ab1": _pool("ab1", "A", "B", rng.randint(200, 1000), rng.randint(200, 1000), rng.randint(0, 30)),
            "ab2": _pool("ab2", "A", "B", rng.randint(200, 1000), rng.randint(200, 1000), rng.randint(0, 30)),
            "ac1": _pool("ac1", "A", "C", rng.randint(200, 1000), rng.randint(200, 1000), rng.randint(0, 30)),
            "ac2": _pool("ac2", "A", "C", rng.randint(200, 1000), rng.randint(200, 1000), rng.randint(0, 30)),
            "cb1": _pool("cb1", "C", "B", rng.randint(200, 1000), rng.randint(200, 1000), rng.randint(0, 30)),
            "cb2": _pool("cb2", "C", "B", rng.randint(200, 1000), rng.randint(200, 1000), rng.randint(0, 30)),
        }
        amount_out = rng.randint(1, 50)

        q = best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=amount_out)
        brute = _brute_best_route_exact_out_2hop(pools_by_id=pools, asset_in="A", asset_out="B", amount_out=amount_out)
        assert (q is None) == (brute is None)
        if q is None or brute is None:
            continue

        feasible += 1
        assert int(q.amount_in) == int(brute.amount_in)
        assert _quote_key(q) == _quote_key(brute)

        # Include some index variation to ensure determinism doesn't depend on dict ordering.
        if i % 37 == 0:
            pools_flipped = dict(reversed(list(pools.items())))
            q2 = best_route_exact_out_2hop(pools_by_id=pools_flipped, asset_in="A", asset_out="B", amount_out=amount_out)
            assert q2 is not None
            assert int(q2.amount_in) == int(q.amount_in)
            assert _quote_key(q2) == _quote_key(q)

    assert feasible >= 40


def test_exact_out_split_cpmm_has_bounded_quote_calls() -> None:
    # Perf regression guard: exact-out split should not degenerate into full-span scans.
    # We count `_quote_exact_out` calls to bound worst-case latency for UX-critical quoting.
    from src.core import split_routing_dispatch as srd

    p0 = PoolState(
        pool_id="p0",
        asset0="A",
        asset1="B",
        reserve0=6000,
        reserve1=6000,
        fee_bps=30,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )
    p1 = PoolState(
        pool_id="p1",
        asset0="A",
        asset1="B",
        reserve0=9000,
        reserve1=4000,
        fee_bps=5,
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    orig = srd._quote_exact_out
    calls = {"n": 0}

    def counting(pool: PoolState, *, asset_in: str, asset_out: str, amount_out: int) -> int:
        calls["n"] = int(calls["n"]) + 1
        return orig(pool, asset_in=asset_in, asset_out=asset_out, amount_out=amount_out)

    srd._quote_exact_out = counting  # type: ignore[assignment]
    try:
        q = srd.best_split_two_pools_exact_out_for_pools(
            p0,
            p1,
            asset_in="A",
            asset_out="B",
            amount_out_total=2000,
            window=32,
            brute_force_max=512,
        )
    finally:
        srd._quote_exact_out = orig  # type: ignore[assignment]

    assert q.amount_out_total == 2000
    assert q.amount_in_total > 0
    assert calls["n"] <= 1400
