from __future__ import annotations

import random

import pytest

from src.core.quote_receipts import make_route_quote_receipt, verify_route_quote_receipt
from src.core.routing import best_route_exact_in_2hop
from src.integration.fast_quote_router_v1 import FastQuoteRouterV1
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


def _mk_pool(*, pool_id: str, a0: str, a1: str, r0: int, r1: int, fee_bps: int) -> PoolState:
    # PoolState enforces canonical asset ordering; remap reserves accordingly.
    if a0 < a1:
        asset0, asset1, reserve0, reserve1 = a0, a1, int(r0), int(r1)
    else:
        asset0, asset1, reserve0, reserve1 = a1, a0, int(r1), int(r0)
    return PoolState(
        pool_id=str(pool_id),
        asset0=str(asset0),
        asset1=str(asset1),
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=int(fee_bps),
        lp_supply=0,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
        curve_params="",
    )


def _build_market(*, seed: int, n_mid: int, pools_per_mid_side: int, direct_pools: int) -> dict[str, PoolState]:
    rng = random.Random(int(seed))
    asset_in = "A_IN"
    asset_out = "A_OUT"
    mids = [f"M{i}" for i in range(int(n_mid))]

    pools: list[PoolState] = []
    pid = 0
    for _ in range(int(direct_pools)):
        r0 = rng.randint(500_000, 5_000_000)
        r1 = rng.randint(500_000, 5_000_000)
        fee = rng.choice([5, 10, 20, 30])
        pools.append(_mk_pool(pool_id=f"P{pid}", a0=asset_in, a1=asset_out, r0=r0, r1=r1, fee_bps=fee))
        pid += 1

    for mid in mids:
        for _ in range(int(pools_per_mid_side)):
            r0 = rng.randint(200_000, 10_000_000)
            r1 = rng.randint(200_000, 10_000_000)
            fee = rng.choice([5, 10, 20, 30, 50])
            pools.append(_mk_pool(pool_id=f"P{pid}", a0=asset_in, a1=mid, r0=r0, r1=r1, fee_bps=fee))
            pid += 1
        for _ in range(int(pools_per_mid_side)):
            r0 = rng.randint(200_000, 10_000_000)
            r1 = rng.randint(200_000, 10_000_000)
            fee = rng.choice([5, 10, 20, 30, 50])
            pools.append(_mk_pool(pool_id=f"P{pid}", a0=mid, a1=asset_out, r0=r0, r1=r1, fee_bps=fee))
            pid += 1

    pools_by_id: dict[str, PoolState] = {}
    for p in pools:
        assert p.pool_id not in pools_by_id
        pools_by_id[p.pool_id] = p
    return pools_by_id


def _quote_to_key(q) -> tuple:
    # Stable structural key: hop_count + per-hop (pool_id, asset_in, asset_out, amount_in, amount_out).
    hops = []
    for leg in q.legs:
        for hop in leg.hops:
            hops.append((hop.pool_id, hop.asset_in, hop.asset_out, int(hop.amount_in), int(hop.amount_out)))
    return (len(hops), tuple(hops), int(q.amount_out))


def _quote_golden_key(q) -> tuple:
    """
    Fully-pinned characterization key for exact-out behavior.

    Unlike ``_quote_to_key`` this preserves leg grouping (so a single 2-hop leg
    is distinguished from two parallel 1-hop legs) and the top-level
    (amount_in, amount_out) chosen by the router. Two RouteQuotes with this key
    equal are byte-for-byte identical for routing purposes.
    """
    legs = tuple(
        tuple(
            (h.pool_id, h.asset_in, h.asset_out, int(h.amount_in), int(h.amount_out))
            for h in leg.hops
        )
        for leg in q.legs
    )
    return (legs, int(q.amount_in), int(q.amount_out))


def test_fast_v1_quote_receipt_verifies_and_is_deterministic() -> None:
    pytest.importorskip("numpy")
    pools_by_id = _build_market(seed=1, n_mid=20, pools_per_mid_side=10, direct_pools=3)

    asset_in = "A_IN"
    asset_out = "A_OUT"
    amount_in = 250_000

    router = FastQuoteRouterV1(max_cache_pairs=8)
    q_fast = router.quote_exact_in_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        topk_max=32,
    )
    assert q_fast is not None

    # Exact router should be >= fast router (fast is a heuristic subset).
    q_exact = best_route_exact_in_2hop(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
    )
    assert q_exact is not None
    assert int(q_fast.amount_out) <= int(q_exact.amount_out)

    # Receipt verification is the key safety gate for UI/automation.
    receipt = make_route_quote_receipt(kind="exact_in", quote=q_fast, pools_by_id=pools_by_id)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools_by_id)
    assert ok, err

    # Determinism (same input => same structural output).
    q2 = router.quote_exact_in_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        topk_max=32,
    )
    assert q2 is not None
    assert _quote_to_key(q2) == _quote_to_key(q_fast)


def test_fast_v1_exact_out_receipt_verifies_and_is_deterministic() -> None:
    pytest.importorskip("numpy")
    pools_by_id = _build_market(seed=2, n_mid=20, pools_per_mid_side=10, direct_pools=3)

    asset_in = "A_IN"
    asset_out = "A_OUT"
    amount_out = 250_000

    router = FastQuoteRouterV1(max_cache_pairs=8)
    q_fast = router.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out=amount_out,
        topk_max=64,
        apply_two_hop_gate=False,
    )
    assert q_fast is not None

    # For exact-out, the core exact_out router is the oracle; fast should not beat it.
    from src.core.routing import best_route_exact_out_2hop

    q_oracle = best_route_exact_out_2hop(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out=amount_out,
        apply_two_hop_gate=False,
    )
    assert q_oracle is not None
    assert int(q_fast.amount_in) >= int(q_oracle.amount_in)

    receipt = make_route_quote_receipt(kind="exact_out", quote=q_fast, pools_by_id=pools_by_id)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools_by_id)
    assert ok, err

    q2 = router.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out=amount_out,
        topk_max=64,
        apply_two_hop_gate=False,
    )
    assert q2 is not None
    assert _quote_to_key(q2) == _quote_to_key(q_fast)


def test_fast_v1_micro_exact_out_amount_out_10_regression_seed1() -> None:
    """
    Regression for a severe micro exact-out miss found in the quality sweep:
      market(n_mid=40,pps=15) seed=1 amount_out=10 topk_max=8

    Root cause: continuous float ranking ignored ceil cascades; fix is bounded exact enumeration
    for tiny amount_out (see EXACT_OUT_MICRO_AMOUNT_OUT_MAX).
    """
    pytest.importorskip("numpy")
    pools_by_id = _build_market(seed=1, n_mid=40, pools_per_mid_side=15, direct_pools=3)

    asset_in = "A_IN"
    asset_out = "A_OUT"
    amount_out = 10

    router = FastQuoteRouterV1(max_cache_pairs=8)
    q_fast = router.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out=amount_out,
        topk_max=8,
        apply_two_hop_gate=False,
    )
    assert q_fast is not None

    from src.core.routing import best_route_exact_out_2hop

    q_oracle = best_route_exact_out_2hop(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out=amount_out,
        apply_two_hop_gate=False,
    )
    assert q_oracle is not None
    assert int(q_fast.amount_in) == int(q_oracle.amount_in)

    receipt = make_route_quote_receipt(kind="exact_out", quote=q_fast, pools_by_id=pools_by_id)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools_by_id)
    assert ok, err


def test_fast_v1_amount_in_int64_fee_boundary_values() -> None:
    pytest.importorskip("numpy")
    # BVA for SAFE_GROSS_FOR_INT64_FEE (routing ranking switches int64-exact fee => float approximation).
    from src.integration.fast_quote_router_v1 import SAFE_GROSS_FOR_INT64_FEE

    asset_in = "A_IN"
    asset_out = "A_OUT"
    mid = "M0"

    # Minimal market with a direct option and a 2-hop option (both CPMM).
    pools = [
        _mk_pool(pool_id="P0", a0=asset_in, a1=asset_out, r0=1_000_000, r1=1_000_000, fee_bps=30),
        _mk_pool(pool_id="P1", a0=asset_in, a1=mid, r0=1_000_000, r1=2_000_000, fee_bps=10),
        _mk_pool(pool_id="P2", a0=mid, a1=asset_out, r0=2_000_000, r1=1_000_000, fee_bps=10),
    ]
    pools_by_id = {p.pool_id: p for p in pools}

    router = FastQuoteRouterV1(max_cache_pairs=8)
    # just below / exactly at / just above
    for amount_in in [int(SAFE_GROSS_FOR_INT64_FEE) - 1, int(SAFE_GROSS_FOR_INT64_FEE), int(SAFE_GROSS_FOR_INT64_FEE) + 1]:
        q = router.quote_exact_in_2hop_fast_v1(
            pools_by_id=pools_by_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=int(amount_in),
            topk_max=8,
        )
        assert q is not None
        receipt = make_route_quote_receipt(kind="exact_in", quote=q, pools_by_id=pools_by_id)
        ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools_by_id)
        assert ok, err


def test_fast_v1_exact_out_micro_amount_out_boundary_values() -> None:
    pytest.importorskip("numpy")
    from src.integration.fast_quote_router_v1 import EXACT_OUT_MICRO_AMOUNT_OUT_MAX

    asset_in = "A_IN"
    asset_out = "A_OUT"
    mid = "M0"

    # Small market with multiple 2-hop candidates + a direct option.
    pools = [
        _mk_pool(pool_id="P0", a0=asset_in, a1=asset_out, r0=2_000_000, r1=2_000_000, fee_bps=30),
        _mk_pool(pool_id="P1", a0=asset_in, a1=mid, r0=1_000_000, r1=3_000_000, fee_bps=10),
        _mk_pool(pool_id="P2", a0=mid, a1=asset_out, r0=3_000_000, r1=1_000_000, fee_bps=10),
        _mk_pool(pool_id="P3", a0=asset_in, a1=mid, r0=2_000_000, r1=4_000_000, fee_bps=20),
        _mk_pool(pool_id="P4", a0=mid, a1=asset_out, r0=4_000_000, r1=2_000_000, fee_bps=20),
    ]
    pools_by_id = {p.pool_id: p for p in pools}

    router = FastQuoteRouterV1(max_cache_pairs=8)
    for amount_out in [
        int(EXACT_OUT_MICRO_AMOUNT_OUT_MAX) - 1,
        int(EXACT_OUT_MICRO_AMOUNT_OUT_MAX),
        int(EXACT_OUT_MICRO_AMOUNT_OUT_MAX) + 1,
    ]:
        q = router.quote_exact_out_2hop_fast_v1(
            pools_by_id=pools_by_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out=int(amount_out),
            topk_max=8,
            apply_two_hop_gate=False,
        )
        assert q is not None
        receipt = make_route_quote_receipt(kind="exact_out", quote=q, pools_by_id=pools_by_id)
        ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools_by_id)
        assert ok, err


def test_fast_v1_direct_split_two_identical_pools() -> None:
    pytest.importorskip("numpy")
    asset_in = "A_IN"
    asset_out = "A_OUT"
    amount_in = 1_000_000

    # Two identical direct pools => splitting strictly improves vs single pool for CPMM.
    p0 = _mk_pool(pool_id="P0", a0=asset_in, a1=asset_out, r0=1_000_000, r1=1_000_000, fee_bps=0)
    p1 = _mk_pool(pool_id="P1", a0=asset_in, a1=asset_out, r0=1_000_000, r1=1_000_000, fee_bps=0)
    pools_by_id = {p.pool_id: p for p in [p0, p1]}

    router = FastQuoteRouterV1(max_cache_pairs=8)
    q_fast = router.quote_exact_in_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        topk_max=32,
    )
    assert q_fast is not None
    assert int(q_fast.amount_in) == int(amount_in)
    # Expected: 2 * floor(1e6 * 5e5 / (1e6 + 5e5)) = 666_666
    assert int(q_fast.amount_out) == 666_666
    assert len(q_fast.legs) == 2
    assert all(len(leg.hops) == 1 for leg in q_fast.legs)

    q_exact = best_route_exact_in_2hop(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
    )
    assert q_exact is not None
    assert int(q_fast.amount_out) <= int(q_exact.amount_out)

    receipt = make_route_quote_receipt(kind="exact_in", quote=q_fast, pools_by_id=pools_by_id)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools_by_id)
    assert ok, err


def test_fast_v1_micro_trade_amount_in_1() -> None:
    pytest.importorskip("numpy")
    # Construct a deterministic "micro-trade" market:
    # - No valid direct route for amount_in=1 (direct fee>0 makes net_in=0).
    # - Exactly one valid 2-hop route with fee=0 on the first hop.
    # - Many invalid 2-hop candidates that would be misranked by continuous fee math.
    asset_in = "A_IN"
    asset_out = "A_OUT"
    amount_in = 1

    pools: list[PoolState] = []
    pid = 0

    # Direct pools: all invalid at amount_in=1 because fee>0.
    for _ in range(3):
        pools.append(_mk_pool(pool_id=f"P{pid}", a0=asset_in, a1=asset_out, r0=1_000_000, r1=1_000_000, fee_bps=5))
        pid += 1

    mids = [f"M{i}" for i in range(12)]
    mid_good = "M_good"
    mids.append(mid_good)

    # Invalid candidates: fee>0 on hop1.
    for mid in mids:
        for _ in range(10):
            pools.append(_mk_pool(pool_id=f"P{pid}", a0=asset_in, a1=mid, r0=250_000, r1=8_000_000, fee_bps=50))
            pid += 1
        for _ in range(10):
            pools.append(_mk_pool(pool_id=f"P{pid}", a0=mid, a1=asset_out, r0=250_000, r1=8_000_000, fee_bps=0))
            pid += 1

    # One valid hop1 with fee=0 (amount_in=1 => net_in=1).
    p1_good = _mk_pool(pool_id=f"P{pid}", a0=asset_in, a1=mid_good, r0=250_000, r1=8_000_000, fee_bps=0)
    pid += 1
    p2_good = _mk_pool(pool_id=f"P{pid}", a0=mid_good, a1=asset_out, r0=250_000, r1=8_000_000, fee_bps=0)
    pid += 1
    pools.append(p1_good)
    pools.append(p2_good)

    pools_by_id = {p.pool_id: p for p in pools}

    # Oracle: exhaustive direct+2hop best (small market).
    def _oracle_best_out() -> int:
        from src.core.amm_dispatch import swap_exact_in_for_pool

        best_out = -1

        # Direct
        for p in pools:
            if asset_in not in (p.asset0, p.asset1) or asset_out not in (p.asset0, p.asset1) or asset_in == asset_out:
                continue
            try:
                rin, rout = (int(p.reserve0), int(p.reserve1)) if asset_in == p.asset0 else (int(p.reserve1), int(p.reserve0))
                out, _ = swap_exact_in_for_pool(p, reserve_in=rin, reserve_out=rout, amount_in=int(amount_in))
            except Exception:
                continue
            best_out = max(best_out, int(out))

        # 2-hop
        by_asset: dict[str, list[PoolState]] = {}
        for p in pools:
            by_asset.setdefault(p.asset0, []).append(p)
            by_asset.setdefault(p.asset1, []).append(p)
        for p1 in by_asset.get(asset_in, []):
            mid = p1.asset1 if asset_in == p1.asset0 else p1.asset0
            if mid in (asset_in, asset_out):
                continue
            for p2 in by_asset.get(mid, []):
                if p2.pool_id == p1.pool_id:
                    continue
                if asset_out not in (p2.asset0, p2.asset1):
                    continue
                try:
                    rin1, rout1 = (int(p1.reserve0), int(p1.reserve1)) if asset_in == p1.asset0 else (int(p1.reserve1), int(p1.reserve0))
                    out1, _ = swap_exact_in_for_pool(p1, reserve_in=rin1, reserve_out=rout1, amount_in=int(amount_in))
                    rin2, rout2 = (int(p2.reserve0), int(p2.reserve1)) if mid == p2.asset0 else (int(p2.reserve1), int(p2.reserve0))
                    out2, _ = swap_exact_in_for_pool(p2, reserve_in=rin2, reserve_out=rout2, amount_in=int(out1))
                except Exception:
                    continue
                best_out = max(best_out, int(out2))
        return int(best_out)

    oracle_out = _oracle_best_out()
    assert oracle_out > 0

    router = FastQuoteRouterV1(max_cache_pairs=8)
    q_fast = router.quote_exact_in_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        topk_max=8,
    )
    assert q_fast is not None
    assert int(q_fast.amount_out) == int(oracle_out)

    receipt = make_route_quote_receipt(kind="exact_in", quote=q_fast, pools_by_id=pools_by_id)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools_by_id)
    assert ok, err


def test_fast_v1_tiny_trade_amount_in_2_integer_fee_ranking_regression() -> None:
    """
    Regression for a real miss found in the quality sweep:
      market(n_mid=40,pps=15) seed=18 amount_in=2 topk_max=8

    Root cause was a representation mismatch: float ranking used continuous fees, but
    kernel semantics use `ceil(gross * fee_bps / 10_000)`.
    """
    pytest.importorskip("numpy")

    def _build_market_fee0(*, seed: int, n_mid: int, pools_per_mid_side: int, direct_pools: int) -> dict[str, PoolState]:
        rng = random.Random(int(seed))
        asset_in = "A_IN"
        asset_out = "A_OUT"
        mids = [f"M{i}" for i in range(int(n_mid))]

        pools: list[PoolState] = []
        pid = 0
        for _ in range(int(direct_pools)):
            r0 = rng.randint(500_000, 5_000_000)
            r1 = rng.randint(500_000, 5_000_000)
            fee = rng.choice([0, 5, 10, 20, 30])
            pools.append(_mk_pool(pool_id=f"P{pid}", a0=asset_in, a1=asset_out, r0=r0, r1=r1, fee_bps=fee))
            pid += 1

        for mid in mids:
            for _ in range(int(pools_per_mid_side)):
                r0 = rng.randint(200_000, 10_000_000)
                r1 = rng.randint(200_000, 10_000_000)
                fee = rng.choice([0, 5, 10, 20, 30, 50])
                pools.append(_mk_pool(pool_id=f"P{pid}", a0=asset_in, a1=mid, r0=r0, r1=r1, fee_bps=fee))
                pid += 1
            for _ in range(int(pools_per_mid_side)):
                r0 = rng.randint(200_000, 10_000_000)
                r1 = rng.randint(200_000, 10_000_000)
                fee = rng.choice([0, 5, 10, 20, 30, 50])
                pools.append(_mk_pool(pool_id=f"P{pid}", a0=mid, a1=asset_out, r0=r0, r1=r1, fee_bps=fee))
                pid += 1

        return {p.pool_id: p for p in pools}

    def _oracle_best_direct_plus_twohop_out(*, pools_by_id: dict[str, PoolState], asset_in: str, asset_out: str, amount_in: int) -> int:
        from src.core.amm_dispatch import swap_exact_in_for_pool

        pools = tuple(sorted(pools_by_id.values(), key=lambda p: p.pool_id))

        best_out = -1

        # Direct
        for p in pools:
            if p.status != PoolStatus.ACTIVE or p.curve_tag != CURVE_TAG_CPMM:
                continue
            if not ((asset_in in (p.asset0, p.asset1)) and (asset_out in (p.asset0, p.asset1)) and asset_in != asset_out):
                continue
            try:
                rin, rout = (int(p.reserve0), int(p.reserve1)) if asset_in == p.asset0 else (int(p.reserve1), int(p.reserve0))
                out, _ = swap_exact_in_for_pool(p, reserve_in=rin, reserve_out=rout, amount_in=int(amount_in))
            except Exception:
                continue
            best_out = max(best_out, int(out))

        # 2-hop (adjacency by asset)
        by_asset: dict[str, list[PoolState]] = {}
        for p in pools:
            if p.status != PoolStatus.ACTIVE or p.curve_tag != CURVE_TAG_CPMM:
                continue
            by_asset.setdefault(p.asset0, []).append(p)
            by_asset.setdefault(p.asset1, []).append(p)
        for plist in by_asset.values():
            plist.sort(key=lambda p: p.pool_id)

        for p1 in by_asset.get(asset_in, []):
            mid = p1.asset1 if asset_in == p1.asset0 else p1.asset0
            if mid in (asset_in, asset_out):
                continue
            try:
                rin1, rout1 = (int(p1.reserve0), int(p1.reserve1)) if asset_in == p1.asset0 else (int(p1.reserve1), int(p1.reserve0))
                out_mid, _ = swap_exact_in_for_pool(p1, reserve_in=rin1, reserve_out=rout1, amount_in=int(amount_in))
            except Exception:
                continue
            for p2 in by_asset.get(mid, []):
                if p2.pool_id == p1.pool_id:
                    continue
                if asset_out not in (p2.asset0, p2.asset1):
                    continue
                try:
                    rin2, rout2 = (int(p2.reserve0), int(p2.reserve1)) if mid == p2.asset0 else (int(p2.reserve1), int(p2.reserve0))
                    out_final, _ = swap_exact_in_for_pool(p2, reserve_in=rin2, reserve_out=rout2, amount_in=int(out_mid))
                except Exception:
                    continue
                best_out = max(best_out, int(out_final))

        return int(best_out)

    pools_by_id = _build_market_fee0(seed=18, n_mid=40, pools_per_mid_side=15, direct_pools=3)

    asset_in = "A_IN"
    asset_out = "A_OUT"
    amount_in = 2
    topk_max = 8

    oracle_out = _oracle_best_direct_plus_twohop_out(
        pools_by_id=pools_by_id, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in
    )
    assert oracle_out > 0

    router = FastQuoteRouterV1(max_cache_pairs=8)
    q_fast = router.quote_exact_in_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=amount_in,
        topk_max=topk_max,
    )
    assert q_fast is not None
    assert int(q_fast.amount_out) == int(oracle_out)

    receipt = make_route_quote_receipt(kind="exact_in", quote=q_fast, pools_by_id=pools_by_id)
    ok, err = verify_route_quote_receipt(receipt, pools_by_id=pools_by_id)
    assert ok, err


# ---------------------------------------------------------------------------
# Characterization (golden) tests for quote_exact_out_2hop_fast_v1.
#
# These pin the EXACT route the current code selects (every pool_id, mid, leg
# grouping, and integer hop amount) for each distinct code path through the
# exact-out router. They are the behavior baseline for the complexity refactor:
# any change to candidate enumeration, scoring/tie-break, rounding, or bounds
# that alters the selected route will flip one of these tuples and fail.
#
# NOTE: paths A/D/E rank candidates with a float64 heuristic the module itself
# documents as "not guaranteed to find the global best route". Their pinned
# tuples are therefore environment-pinned characterization values: a numpy/BLAS
# change that shifts float ranking should be triaged as "re-characterize"
# (recompute the expected tuple), not necessarily a correctness regression. The
# final hop AMOUNTS are always exact integer replay; only which candidate ranks
# first is float-sensitive. Paths B/C do not depend on float ranking.
#
# Paths covered:
#   A: float-ranking 2-hop union selection (large Q)
#   B: apply_two_hop_gate=True -> gate suppresses 2-hop, direct-split wins
#   C: micro exact-out enumeration (Q <= EXACT_OUT_MICRO_AMOUNT_OUT_MAX)
#   D: float path just above the micro boundary
#   E: market with two parallel direct pools (direct-split candidate path)
# ---------------------------------------------------------------------------


def _build_exact_out_small_market() -> dict[str, PoolState]:
    return {
        p.pool_id: p
        for p in [
            _mk_pool(pool_id="P0", a0="A_IN", a1="A_OUT", r0=2_000_000, r1=2_000_000, fee_bps=30),
            _mk_pool(pool_id="P1", a0="A_IN", a1="M0", r0=1_000_000, r1=3_000_000, fee_bps=10),
            _mk_pool(pool_id="P2", a0="M0", a1="A_OUT", r0=3_000_000, r1=1_000_000, fee_bps=10),
            _mk_pool(pool_id="P3", a0="A_IN", a1="M0", r0=2_000_000, r1=4_000_000, fee_bps=20),
            _mk_pool(pool_id="P4", a0="M0", a1="A_OUT", r0=4_000_000, r1=2_000_000, fee_bps=20),
        ]
    }


def test_fast_v1_exact_out_golden_float_rank_2hop() -> None:
    """Path A: large-Q float-ranking union selection pins one 2-hop route."""
    pytest.importorskip("numpy")
    pools_by_id = _build_market(seed=2, n_mid=20, pools_per_mid_side=10, direct_pools=3)
    router = FastQuoteRouterV1(max_cache_pairs=8)
    q = router.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in="A_IN",
        asset_out="A_OUT",
        amount_out=250_000,
        topk_max=64,
        apply_two_hop_gate=False,
    )
    assert q is not None
    assert _quote_golden_key(q) == (
        ((("P63", "A_IN", "M3", 1573, 15217), ("P76", "M3", "A_OUT", 15217, 250000)),),
        1573,
        250000,
    )


def test_fast_v1_exact_out_golden_two_hop_gate_true_directsplit() -> None:
    """Path B: with apply_two_hop_gate=True the gate suppresses 2-hop and a 2-leg direct split wins."""
    pytest.importorskip("numpy")
    pools_by_id = _build_market(seed=2, n_mid=20, pools_per_mid_side=10, direct_pools=3)
    router = FastQuoteRouterV1(max_cache_pairs=8)
    q = router.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in="A_IN",
        asset_out="A_OUT",
        amount_out=250_000,
        topk_max=64,
        apply_two_hop_gate=True,
    )
    assert q is not None
    # Two parallel 1-hop legs (direct split), not a single 2-hop leg.
    assert len(q.legs) == 2
    assert all(len(leg.hops) == 1 for leg in q.legs)
    assert _quote_golden_key(q) == (
        (
            (("P0", "A_IN", "A_OUT", 222251, 235458),),
            (("P2", "A_IN", "A_OUT", 16764, 14542),),
        ),
        239015,
        250000,
    )


def test_fast_v1_exact_out_golden_micro_enumeration() -> None:
    """Path C: micro exact-out enumeration pins the exact (already==oracle) route."""
    pytest.importorskip("numpy")
    pools_by_id = _build_market(seed=1, n_mid=40, pools_per_mid_side=15, direct_pools=3)
    router = FastQuoteRouterV1(max_cache_pairs=8)
    q = router.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in="A_IN",
        asset_out="A_OUT",
        amount_out=10,
        topk_max=8,
        apply_two_hop_gate=False,
    )
    assert q is not None
    assert _quote_golden_key(q) == (
        ((("P1037", "A_IN", "M34", 2, 4), ("P1048", "M34", "A_OUT", 4, 10)),),
        2,
        10,
    )


def test_fast_v1_exact_out_golden_float_path_above_micro_boundary() -> None:
    """Path D: just above the micro boundary the float-ranking path is taken; pin its route."""
    pytest.importorskip("numpy")
    pools_by_id = _build_exact_out_small_market()
    router = FastQuoteRouterV1(max_cache_pairs=8)
    q = router.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in="A_IN",
        asset_out="A_OUT",
        amount_out=101,
        topk_max=8,
        apply_two_hop_gate=False,
    )
    assert q is not None
    assert _quote_golden_key(q) == (
        ((("P1", "A_IN", "M0", 70, 204), ("P4", "M0", "A_OUT", 204, 101)),),
        70,
        101,
    )


def test_fast_v1_exact_out_golden_two_direct_pools() -> None:
    """Path E: market with two parallel direct pools (exercises direct + direct-split candidate logic)."""
    pytest.importorskip("numpy")
    pools_by_id = dict(_build_exact_out_small_market())
    pools_by_id["P5"] = _mk_pool(pool_id="P5", a0="A_IN", a1="A_OUT", r0=1_500_000, r1=1_500_000, fee_bps=5)
    router = FastQuoteRouterV1(max_cache_pairs=8)
    q = router.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in="A_IN",
        asset_out="A_OUT",
        amount_out=300_000,
        topk_max=8,
        apply_two_hop_gate=False,
    )
    assert q is not None
    assert _quote_golden_key(q) == (
        ((("P1", "A_IN", "M0", 308809, 707298), ("P4", "M0", "A_OUT", 707298, 300000)),),
        308809,
        300000,
    )


def test_fast_v1_exact_out_two_hop_tie_break_lexicographic_pool_seq() -> None:
    """
    Teeth: constructed tie pins the exact-out candidate tie-break.

    Two identical hop-1 pools (``PA``, ``PB``) feed the same intermediate ``M0``
    and share a single hop-2 pool ``PC``. The two 2-hop routes therefore produce
    an IDENTICAL ``amount_in`` (a true tie). The deterministic tie-break must pick
    the lexicographically-smaller ``pool_seq`` -> ``PA`` (``"PA,PC" < "PB,PC"``).

    This fails if the candidate-scoring predicate reverses its tie-break key
    comparison (``cand_key < cur_key`` -> ``>``, which would select PB), drops the
    key tie-break entirely, or changes rounding/bounds so the two routes stop
    tying on ``amount_in``. It exercises BOTH selection paths with their two
    distinct key functions: the float-ranking path (large Q, ``_quote_key``) and
    the micro-enumeration path (Q <= EXACT_OUT_MICRO_AMOUNT_OUT_MAX,
    ``_quote_key_for``). Verified to flip PA->PB under the reversed-key mutation
    on both paths.
    """
    pytest.importorskip("numpy")
    asset_in = "A_IN"
    asset_out = "A_OUT"
    mid = "M0"

    # --- Float-ranking path: Q above the micro boundary. ---
    pa = _mk_pool(pool_id="PA", a0=asset_in, a1=mid, r0=1_000_000, r1=2_000_000, fee_bps=10)
    pb = _mk_pool(pool_id="PB", a0=asset_in, a1=mid, r0=1_000_000, r1=2_000_000, fee_bps=10)
    pc = _mk_pool(pool_id="PC", a0=mid, a1=asset_out, r0=2_000_000, r1=1_000_000, fee_bps=10)
    pools_float = {p.pool_id: p for p in [pa, pb, pc]}

    from src.integration.fast_quote_router_v1 import _quote_exact_out_twohop

    # Sanity: the two routes really tie on amount_in (otherwise the test proves nothing).
    via_pa = _quote_exact_out_twohop(pa, pc, asset_in=asset_in, mid=mid, asset_out=asset_out, amount_out=50_000)
    via_pb = _quote_exact_out_twohop(pb, pc, asset_in=asset_in, mid=mid, asset_out=asset_out, amount_out=50_000)
    assert via_pa is not None and via_pb is not None
    assert int(via_pa[0]) == int(via_pb[0])  # true tie on amount_in

    router = FastQuoteRouterV1(max_cache_pairs=8)
    q_float = router.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools_float,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out=50_000,
        topk_max=8,
        apply_two_hop_gate=False,
    )
    assert q_float is not None
    # Lexicographically-smaller pool_seq wins the tie: PA, not PB.
    assert q_float.legs[0].hops[0].pool_id == "PA"
    assert _quote_golden_key(q_float) == (
        ((("PA", "A_IN", "M0", 55672, 105370), ("PC", "M0", "A_OUT", 105370, 50000)),),
        55672,
        50000,
    )

    # --- Micro-enumeration path: Q <= EXACT_OUT_MICRO_AMOUNT_OUT_MAX, feasible market. ---
    pa2 = _mk_pool(pool_id="PA", a0=asset_in, a1=mid, r0=8_000_000, r1=8_000_000, fee_bps=0)
    pb2 = _mk_pool(pool_id="PB", a0=asset_in, a1=mid, r0=8_000_000, r1=8_000_000, fee_bps=0)
    pc2 = _mk_pool(pool_id="PC", a0=mid, a1=asset_out, r0=8_000_000, r1=8_000_000, fee_bps=0)
    pools_micro = {p.pool_id: p for p in [pa2, pb2, pc2]}

    via_pa_m = _quote_exact_out_twohop(pa2, pc2, asset_in=asset_in, mid=mid, asset_out=asset_out, amount_out=10)
    via_pb_m = _quote_exact_out_twohop(pb2, pc2, asset_in=asset_in, mid=mid, asset_out=asset_out, amount_out=10)
    assert via_pa_m is not None and via_pb_m is not None
    assert int(via_pa_m[0]) == int(via_pb_m[0])  # true tie on amount_in (micro)

    router_m = FastQuoteRouterV1(max_cache_pairs=8)
    q_micro = router_m.quote_exact_out_2hop_fast_v1(
        pools_by_id=pools_micro,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out=10,
        topk_max=8,
        apply_two_hop_gate=False,
    )
    assert q_micro is not None
    assert q_micro.legs[0].hops[0].pool_id == "PA"
    assert _quote_golden_key(q_micro) == (
        ((("PA", "A_IN", "M0", 12, 11), ("PC", "M0", "A_OUT", 11, 10)),),
        12,
        10,
    )
