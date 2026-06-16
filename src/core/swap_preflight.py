"""Deterministic swap preflight (UX + security + automation).

Goal: explain *why* a swap would fail and provide the smallest useful
"next action" hints (suggested min_out / max_in) without changing consensus
semantics.

This module is intentionally pure and deterministic so it can be used by:
- UI: instant error explanations + parameter suggestions
- deterministic agents: fail-closed gating before intent submission
"""

from __future__ import annotations

from dataclasses import dataclass

from ..kernels.python.cpmm_swap_v8 import swap_exact_out as _cpmm_exact_out_kernel_v8
from ..state.balances import Amount, AssetId
from ..state.pools import CURVE_TAG_CPMM, PoolState
from .amm_dispatch import (
    CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
    swap_exact_in_for_pool,
    swap_exact_out_for_pool,
)


@dataclass(frozen=True)
class SwapPreflightResult:
    ok: bool
    reason: str
    kind: str  # "exact_in" or "exact_out"

    amount_in_quote: int
    amount_out_quote: int

    suggested_min_amount_out: int | None
    suggested_max_amount_in: int | None

    # Exact-out only (CPMM): gap when interpreting the exact-out quote as exact-in.
    overdelivery_gap: int | None
    overdelivery_gap_bps: int | None
    policy_max_overdelivery_gap_bps: int | None


@dataclass(frozen=True)
class _ExactOutGapAnalysis:
    amount_in_quote: int | None
    overdelivery_gap: int | None
    overdelivery_gap_bps: int | None


@dataclass(frozen=True)
class _ExactInPreflightRequest:
    pool: PoolState
    asset_in: AssetId
    asset_out: AssetId
    amount_in: Amount
    min_amount_out: Amount
    suggested_slippage_bps: int


@dataclass(frozen=True)
class _ExactOutPreflightRequest:
    pool: PoolState
    asset_in: AssetId
    asset_out: AssetId
    amount_out: Amount
    max_amount_in: Amount
    suggested_slippage_bps: int
    policy_max_overdelivery_gap_bps: int


def _preflight_result(
    *,
    ok: bool,
    reason: str,
    kind: str,
    amount_in_quote: int = 0,
    amount_out_quote: int = 0,
    suggested_min_amount_out: int | None = None,
    suggested_max_amount_in: int | None = None,
    overdelivery_gap: int | None = None,
    overdelivery_gap_bps: int | None = None,
    policy_max_overdelivery_gap_bps: int | None = None,
) -> SwapPreflightResult:
    return SwapPreflightResult(
        ok=ok,
        reason=reason,
        kind=kind,
        amount_in_quote=int(amount_in_quote),
        amount_out_quote=int(amount_out_quote),
        suggested_min_amount_out=suggested_min_amount_out,
        suggested_max_amount_in=suggested_max_amount_in,
        overdelivery_gap=overdelivery_gap,
        overdelivery_gap_bps=overdelivery_gap_bps,
        policy_max_overdelivery_gap_bps=policy_max_overdelivery_gap_bps,
    )


def _validate_bps_value(name: str, value: int) -> None:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be int")
    if value < 0 or value > 10_000:
        raise ValueError(f"{name} must be in [0, 10_000]")


def _reserves_for_direction(
    pool: PoolState,
    *,
    asset_in: AssetId,
    asset_out: AssetId,
) -> tuple[Amount, Amount] | None:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def _analyze_cpmm_exact_out_gap(
    *,
    pool: PoolState,
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
) -> _ExactOutGapAnalysis:
    if pool.curve_tag != CURVE_TAG_CPMM:
        return _ExactOutGapAnalysis(
            amount_in_quote=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
        )
    try:
        result = _cpmm_exact_out_kernel_v8(
            reserve_in=int(reserve_in),
            reserve_out=int(reserve_out),
            amount_out=int(amount_out),
            fee_bps=int(pool.fee_bps),
        )
    except (TypeError, ValueError, OverflowError):
        return _ExactOutGapAnalysis(
            amount_in_quote=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
        )
    overdelivery_gap = int(result.overdelivery_gap)
    overdelivery_gap_bps = ((overdelivery_gap * 10_000) + int(amount_out) - 1) // int(amount_out)
    return _ExactOutGapAnalysis(
        amount_in_quote=int(result.amount_in),
        overdelivery_gap=overdelivery_gap,
        overdelivery_gap_bps=overdelivery_gap_bps,
    )


def _quote_exact_out_required_input(
    *,
    pool: PoolState,
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
    policy_max_overdelivery_gap_bps: int,
) -> tuple[bool, str, int | None]:
    try:
        if pool.curve_tag == CURVE_TAG_CPMM:
            # Use the same kernel as `swap_exact_out_for_pool` but allow a configurable policy threshold.
            from .cpmm import swap_exact_out as _cpmm_swap_exact_out

            required_in, _ = _cpmm_swap_exact_out(
                reserve_in=int(reserve_in),
                reserve_out=int(reserve_out),
                amount_out=int(amount_out),
                fee_bps=int(pool.fee_bps),
                max_overdelivery_gap_bps=int(policy_max_overdelivery_gap_bps),
            )
        else:
            required_in, _ = swap_exact_out_for_pool(
                pool,
                reserve_in=reserve_in,
                reserve_out=reserve_out,
                amount_out=int(amount_out),
            )
    except ValueError as exc:
        reason = "exact_out_overdelivery_policy" if "overdelivery gap exceeds" in str(exc) else "swap_error"
        return False, reason, None
    except (TypeError, OverflowError):
        return False, "swap_error", None
    return True, "ok", int(required_in)


def _preflight_exact_in_with_reserves(
    req: _ExactInPreflightRequest,
    reserves: tuple[Amount, Amount],
) -> SwapPreflightResult:
    reserve_in, reserve_out = reserves
    try:
        out, _ = swap_exact_in_for_pool(
            req.pool,
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=int(req.amount_in),
        )
    except (TypeError, ValueError, OverflowError):
        return _preflight_result(
            ok=False,
            reason="swap_error",
            kind="exact_in",
            amount_in_quote=int(req.amount_in),
        )

    amount_out_quote = int(out)
    suggested_min_out = (amount_out_quote * (10_000 - req.suggested_slippage_bps)) // 10_000
    if int(req.min_amount_out) > amount_out_quote:
        return _preflight_result(
            ok=False,
            reason="min_amount_out_too_high",
            kind="exact_in",
            amount_in_quote=int(req.amount_in),
            amount_out_quote=amount_out_quote,
            suggested_min_amount_out=int(suggested_min_out),
        )

    return _preflight_result(
        ok=True,
        reason="ok",
        kind="exact_in",
        amount_in_quote=int(req.amount_in),
        amount_out_quote=amount_out_quote,
        suggested_min_amount_out=int(suggested_min_out),
    )


def _preflight_swap_exact_in_checked(req: _ExactInPreflightRequest) -> SwapPreflightResult:
    if req.pool.status.value != "ACTIVE":
        return _preflight_result(ok=False, reason="pool_inactive", kind="exact_in")
    if req.amount_in <= 0:
        return _preflight_result(ok=False, reason="bad_amount_in", kind="exact_in")
    if req.min_amount_out < 0:
        return _preflight_result(
            ok=False,
            reason="bad_min_amount_out",
            kind="exact_in",
            amount_in_quote=int(req.amount_in),
        )
    _validate_bps_value("suggested_slippage_bps", req.suggested_slippage_bps)

    reserves = _reserves_for_direction(req.pool, asset_in=req.asset_in, asset_out=req.asset_out)
    if reserves is None:
        return _preflight_result(
            ok=False,
            reason="bad_assets",
            kind="exact_in",
            amount_in_quote=int(req.amount_in),
        )
    return _preflight_exact_in_with_reserves(req, reserves)


def _exact_out_failure_result(
    *,
    reason: str,
    req: _ExactOutPreflightRequest,
    amount_in_quote: int = 0,
    gap: _ExactOutGapAnalysis | None = None,
) -> SwapPreflightResult:
    return _preflight_result(
        ok=False,
        reason=reason,
        kind="exact_out",
        amount_in_quote=int(amount_in_quote),
        amount_out_quote=int(req.amount_out),
        overdelivery_gap=None if gap is None else gap.overdelivery_gap,
        overdelivery_gap_bps=None if gap is None else gap.overdelivery_gap_bps,
        policy_max_overdelivery_gap_bps=int(req.policy_max_overdelivery_gap_bps),
    )


def _preflight_exact_out_with_reserves(
    req: _ExactOutPreflightRequest,
    reserves: tuple[Amount, Amount],
) -> SwapPreflightResult:
    reserve_in, reserve_out = reserves
    gap = _analyze_cpmm_exact_out_gap(
        pool=req.pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=req.amount_out,
    )
    quote_ok, quote_err, required_in = _quote_exact_out_required_input(
        pool=req.pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=req.amount_out,
        policy_max_overdelivery_gap_bps=int(req.policy_max_overdelivery_gap_bps),
    )
    if not quote_ok or required_in is None:
        return _exact_out_failure_result(
            reason=quote_err,
            req=req,
            amount_in_quote=int(gap.amount_in_quote or 0),
            gap=gap,
        )

    required_in_i = int(required_in)
    suggested_max_in = (required_in_i * (10_000 + req.suggested_slippage_bps) + 9_999) // 10_000
    if required_in_i > int(req.max_amount_in):
        return _preflight_result(
            ok=False,
            reason="max_amount_in_too_low",
            kind="exact_out",
            amount_in_quote=required_in_i,
            amount_out_quote=int(req.amount_out),
            suggested_max_amount_in=int(suggested_max_in),
            overdelivery_gap=gap.overdelivery_gap,
            overdelivery_gap_bps=gap.overdelivery_gap_bps,
            policy_max_overdelivery_gap_bps=int(req.policy_max_overdelivery_gap_bps),
        )

    return _preflight_result(
        ok=True,
        reason="ok",
        kind="exact_out",
        amount_in_quote=required_in_i,
        amount_out_quote=int(req.amount_out),
        suggested_max_amount_in=int(suggested_max_in),
        overdelivery_gap=gap.overdelivery_gap,
        overdelivery_gap_bps=gap.overdelivery_gap_bps,
        policy_max_overdelivery_gap_bps=int(req.policy_max_overdelivery_gap_bps),
    )


def _preflight_swap_exact_out_checked(req: _ExactOutPreflightRequest) -> SwapPreflightResult:
    if req.pool.status.value != "ACTIVE":
        return _preflight_result(
            ok=False,
            reason="pool_inactive",
            kind="exact_out",
            policy_max_overdelivery_gap_bps=int(req.policy_max_overdelivery_gap_bps),
        )
    if req.amount_out <= 0:
        return _exact_out_failure_result(reason="bad_amount_out", req=req)
    if req.max_amount_in < 0:
        return _exact_out_failure_result(
            reason="bad_max_amount_in",
            req=req,
            amount_in_quote=int(req.max_amount_in),
        )
    _validate_bps_value("suggested_slippage_bps", req.suggested_slippage_bps)
    _validate_bps_value("policy_max_overdelivery_gap_bps", req.policy_max_overdelivery_gap_bps)

    reserves = _reserves_for_direction(req.pool, asset_in=req.asset_in, asset_out=req.asset_out)
    if reserves is None:
        return _exact_out_failure_result(
            reason="bad_assets",
            req=req,
            amount_in_quote=int(req.max_amount_in),
        )
    return _preflight_exact_out_with_reserves(req, reserves)


def preflight_swap_exact_in(
    *,
    pool: PoolState,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: Amount,
    min_amount_out: Amount,
    suggested_slippage_bps: int = 50,
) -> SwapPreflightResult:
    """Preflight an exact-in swap against the given pool snapshot."""
    return _preflight_swap_exact_in_checked(
        _ExactInPreflightRequest(
            pool=pool,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            min_amount_out=min_amount_out,
            suggested_slippage_bps=suggested_slippage_bps,
        )
    )


def preflight_swap_exact_out(
    *,
    pool: PoolState,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_out: Amount,
    max_amount_in: Amount,
    suggested_slippage_bps: int = 50,
    policy_max_overdelivery_gap_bps: int = CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
) -> SwapPreflightResult:
    """Preflight an exact-out swap against the given pool snapshot."""
    return _preflight_swap_exact_out_checked(
        _ExactOutPreflightRequest(
            pool=pool,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out=amount_out,
            max_amount_in=max_amount_in,
            suggested_slippage_bps=suggested_slippage_bps,
            policy_max_overdelivery_gap_bps=policy_max_overdelivery_gap_bps,
        )
    )
