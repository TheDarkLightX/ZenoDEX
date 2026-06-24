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


def test_fast_v1_amount_in_kernel_domain_boundary_values() -> None:
    pytest.importorskip("numpy")
    from src.core.domain_limits import DEX_POOL_RESERVE_MAX
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
    max_valid_amount_in = int(DEX_POOL_RESERVE_MAX) - 1_000_000
    assert int(SAFE_GROSS_FOR_INT64_FEE) > max_valid_amount_in

    # just below / exactly at the CPMM reserve-growth boundary
    for amount_in in [max_valid_amount_in - 1, max_valid_amount_in]:
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

    q = router.quote_exact_in_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=max_valid_amount_in + 1,
        topk_max=8,
    )
    assert q is None


def test_fast_v1_exact_in_suppresses_domain_value_error(monkeypatch: pytest.MonkeyPatch) -> None:
    pytest.importorskip("numpy")
    import src.integration.fast_quote_router_v1 as fast_router

    asset_in = "A_IN"
    asset_out = "A_OUT"
    pool = _mk_pool(pool_id="P0", a0=asset_in, a1=asset_out, r0=1_000_000, r1=1_000_000, fee_bps=30)
    pools_by_id = {pool.pool_id: pool}

    def _domain_reject(*_args, **_kwargs):
        raise ValueError("domain reject")

    monkeypatch.setattr(fast_router, "swap_exact_in_for_pool", _domain_reject)

    router = FastQuoteRouterV1(max_cache_pairs=8)
    assert router.quote_exact_in_2hop_fast_v1(
        pools_by_id=pools_by_id,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_in=100,
        topk_max=8,
    ) is None


def test_fast_v1_exact_in_propagates_unexpected_quote_error(monkeypatch: pytest.MonkeyPatch) -> None:
    pytest.importorskip("numpy")
    import src.integration.fast_quote_router_v1 as fast_router

    asset_in = "A_IN"
    asset_out = "A_OUT"
    pool = _mk_pool(pool_id="P0", a0=asset_in, a1=asset_out, r0=1_000_000, r1=1_000_000, fee_bps=30)
    pools_by_id = {pool.pool_id: pool}

    def _programming_error(*_args, **_kwargs):
        raise RuntimeError("programming bug")

    monkeypatch.setattr(fast_router, "swap_exact_in_for_pool", _programming_error)

    router = FastQuoteRouterV1(max_cache_pairs=8)
    with pytest.raises(RuntimeError, match="programming bug"):
        router.quote_exact_in_2hop_fast_v1(
            pools_by_id=pools_by_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=100,
            topk_max=8,
        )


def test_fast_v1_exact_out_propagates_unexpected_quote_error(monkeypatch: pytest.MonkeyPatch) -> None:
    pytest.importorskip("numpy")
    import src.integration.fast_quote_router_v1 as fast_router

    asset_in = "A_IN"
    asset_out = "A_OUT"
    pool = _mk_pool(pool_id="P0", a0=asset_in, a1=asset_out, r0=1_000_000, r1=1_000_000, fee_bps=30)
    pools_by_id = {pool.pool_id: pool}

    def _programming_error(*_args, **_kwargs):
        raise RuntimeError("programming bug")

    monkeypatch.setattr(fast_router, "swap_exact_out_for_pool", _programming_error)

    router = FastQuoteRouterV1(max_cache_pairs=8)
    with pytest.raises(RuntimeError, match="programming bug"):
        router.quote_exact_out_2hop_fast_v1(
            pools_by_id=pools_by_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out=100,
            topk_max=8,
            apply_two_hop_gate=False,
        )


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
            except ValueError:
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
                except ValueError:
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
            except ValueError:
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
            except ValueError:
                continue
            for p2 in by_asset.get(mid, []):
                if p2.pool_id == p1.pool_id:
                    continue
                if asset_out not in (p2.asset0, p2.asset1):
                    continue
                try:
                    rin2, rout2 = (int(p2.reserve0), int(p2.reserve1)) if mid == p2.asset0 else (int(p2.reserve1), int(p2.reserve0))
                    out_final, _ = swap_exact_in_for_pool(p2, reserve_in=rin2, reserve_out=rout2, amount_in=int(out_mid))
                except ValueError:
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
