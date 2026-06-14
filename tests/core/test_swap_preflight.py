from __future__ import annotations

import pytest

import src.core.cpmm as cpmm
import src.core.swap_preflight as swap_preflight
from src.core.amm_dispatch import (
    CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
    swap_exact_out_for_pool,
)
from src.core.swap_preflight import preflight_swap_exact_in, preflight_swap_exact_out
from src.state.pools import PoolState, PoolStatus


def _pool(*, r0: int, r1: int, fee_bps: int = 0) -> PoolState:
    return PoolState(
        pool_id="p",
        asset0="A",
        asset1="B",
        reserve0=int(r0),
        reserve1=int(r1),
        fee_bps=int(fee_bps),
        lp_supply=1,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )


def test_preflight_exact_in_ok() -> None:
    p = _pool(r0=1000, r1=1000, fee_bps=30)
    res = preflight_swap_exact_in(
        pool=p,
        asset_in="A",
        asset_out="B",
        amount_in=100,
        min_amount_out=0,
        suggested_slippage_bps=50,
    )
    assert res.ok is True
    assert res.reason == "ok"
    assert res.amount_out_quote > 0
    assert res.suggested_min_amount_out is not None
    assert 0 <= res.suggested_min_amount_out <= res.amount_out_quote


def test_preflight_exact_in_rejects_min_out_too_high() -> None:
    p = _pool(r0=1000, r1=1000, fee_bps=0)
    ok = preflight_swap_exact_in(
        pool=p,
        asset_in="A",
        asset_out="B",
        amount_in=100,
        min_amount_out=0,
        suggested_slippage_bps=0,
    )
    assert ok.ok is True

    bad = preflight_swap_exact_in(
        pool=p,
        asset_in="A",
        asset_out="B",
        amount_in=100,
        min_amount_out=ok.amount_out_quote + 1,
        suggested_slippage_bps=0,
    )
    assert bad.ok is False
    assert bad.reason == "min_amount_out_too_high"
    assert bad.suggested_min_amount_out is not None
    assert bad.suggested_min_amount_out <= ok.amount_out_quote


def test_preflight_exact_out_ok() -> None:
    p = _pool(r0=1000, r1=1000, fee_bps=0)
    req_in, _ = swap_exact_out_for_pool(p, reserve_in=int(p.reserve0), reserve_out=int(p.reserve1), amount_out=300)

    res = preflight_swap_exact_out(
        pool=p,
        asset_in="A",
        asset_out="B",
        amount_out=300,
        max_amount_in=int(req_in),
        suggested_slippage_bps=50,
    )
    assert res.ok is True
    assert res.reason == "ok"
    assert res.amount_in_quote == int(req_in)
    assert res.suggested_max_amount_in is not None
    assert res.suggested_max_amount_in >= int(req_in)


def test_preflight_exact_out_rejects_max_in_too_low() -> None:
    p = _pool(r0=1000, r1=1000, fee_bps=0)
    req_in, _ = swap_exact_out_for_pool(p, reserve_in=int(p.reserve0), reserve_out=int(p.reserve1), amount_out=300)

    res = preflight_swap_exact_out(
        pool=p,
        asset_in="A",
        asset_out="B",
        amount_out=300,
        max_amount_in=int(req_in) - 1,
        suggested_slippage_bps=50,
    )
    assert res.ok is False
    assert res.reason == "max_amount_in_too_low"
    assert res.suggested_max_amount_in is not None
    assert res.suggested_max_amount_in >= int(req_in)


def test_preflight_exact_out_flags_overdelivery_policy_case() -> None:
    # Witness regime from cpmm_overdelivery_diagnosis.json:
    # reserve_in=1,reserve_out=4, amount_out=1 => exact-in output would be 2 (gap=1 => 10_000 bps).
    p = _pool(r0=1, r1=4, fee_bps=0)

    res = preflight_swap_exact_out(
        pool=p,
        asset_in="A",
        asset_out="B",
        amount_out=1,
        max_amount_in=10_000,
        suggested_slippage_bps=50,
        policy_max_overdelivery_gap_bps=CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
    )
    assert res.ok is False
    assert res.reason == "exact_out_overdelivery_policy"
    assert res.overdelivery_gap == 1
    assert res.overdelivery_gap_bps == 10_000


def test_preflight_exact_in_rejects_inactive_pool() -> None:
    p = _pool(r0=1000, r1=1000, fee_bps=0)
    p.status = PoolStatus.FROZEN
    res = preflight_swap_exact_in(pool=p, asset_in="A", asset_out="B", amount_in=10, min_amount_out=0)
    assert res.ok is False
    assert res.reason == "pool_inactive"


def test_preflight_exact_in_returns_swap_error_for_domain_reject() -> None:
    p = _pool(r0=0, r1=1000, fee_bps=0)

    res = preflight_swap_exact_in(pool=p, asset_in="A", asset_out="B", amount_in=10, min_amount_out=0)

    assert res.ok is False
    assert res.reason == "swap_error"


def test_preflight_exact_in_propagates_unexpected_kernel_fault(monkeypatch: pytest.MonkeyPatch) -> None:
    p = _pool(r0=1000, r1=1000, fee_bps=0)

    def broken_swap_exact_in_for_pool(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise RuntimeError("exact-in implementation fault")

    monkeypatch.setattr(swap_preflight, "swap_exact_in_for_pool", broken_swap_exact_in_for_pool)

    with pytest.raises(RuntimeError, match="exact-in implementation fault"):
        preflight_swap_exact_in(pool=p, asset_in="A", asset_out="B", amount_in=10, min_amount_out=0)


def test_preflight_exact_out_gap_domain_reject_still_attempts_quote(monkeypatch: pytest.MonkeyPatch) -> None:
    p = _pool(r0=1000, r1=1000, fee_bps=0)

    def rejected_gap_analysis(*_args: object, **_kwargs: object) -> object:
        raise ValueError("gap analysis domain reject")

    monkeypatch.setattr(swap_preflight, "_cpmm_exact_out_kernel_v8", rejected_gap_analysis)

    res = preflight_swap_exact_out(
        pool=p,
        asset_in="A",
        asset_out="B",
        amount_out=100,
        max_amount_in=200,
    )

    assert res.ok is True
    assert res.reason == "ok"
    assert res.overdelivery_gap is None
    assert res.overdelivery_gap_bps is None


def test_preflight_exact_out_propagates_gap_analysis_fault(monkeypatch: pytest.MonkeyPatch) -> None:
    p = _pool(r0=1000, r1=1000, fee_bps=0)

    def broken_gap_analysis(*_args: object, **_kwargs: object) -> object:
        raise RuntimeError("gap analysis implementation fault")

    monkeypatch.setattr(swap_preflight, "_cpmm_exact_out_kernel_v8", broken_gap_analysis)

    with pytest.raises(RuntimeError, match="gap analysis implementation fault"):
        preflight_swap_exact_out(
            pool=p,
            asset_in="A",
            asset_out="B",
            amount_out=100,
            max_amount_in=200,
        )


def test_preflight_exact_out_propagates_unexpected_quote_fault(monkeypatch: pytest.MonkeyPatch) -> None:
    p = _pool(r0=1000, r1=1000, fee_bps=0)

    def broken_swap_exact_out(*_args: object, **_kwargs: object) -> tuple[int, tuple[int, int]]:
        raise RuntimeError("exact-out implementation fault")

    monkeypatch.setattr(cpmm, "swap_exact_out", broken_swap_exact_out)

    with pytest.raises(RuntimeError, match="exact-out implementation fault"):
        preflight_swap_exact_out(
            pool=p,
            asset_in="A",
            asset_out="B",
            amount_out=100,
            max_amount_in=200,
        )


def test_preflight_exact_out_validates_slippage_bps() -> None:
    p = _pool(r0=1000, r1=1000, fee_bps=0)
    with pytest.raises(ValueError, match="suggested_slippage_bps"):
        _ = preflight_swap_exact_out(
            pool=p,
            asset_in="A",
            asset_out="B",
            amount_out=1,
            max_amount_in=10,
            suggested_slippage_bps=10_001,
        )
