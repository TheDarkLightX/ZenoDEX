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
    if pool.status.value != "ACTIVE":
        return SwapPreflightResult(
            ok=False,
            reason="pool_inactive",
            kind="exact_in",
            amount_in_quote=0,
            amount_out_quote=0,
            suggested_min_amount_out=None,
            suggested_max_amount_in=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
            policy_max_overdelivery_gap_bps=None,
        )
    if amount_in <= 0:
        return SwapPreflightResult(
            ok=False,
            reason="bad_amount_in",
            kind="exact_in",
            amount_in_quote=0,
            amount_out_quote=0,
            suggested_min_amount_out=None,
            suggested_max_amount_in=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
            policy_max_overdelivery_gap_bps=None,
        )
    if min_amount_out < 0:
        return SwapPreflightResult(
            ok=False,
            reason="bad_min_amount_out",
            kind="exact_in",
            amount_in_quote=int(amount_in),
            amount_out_quote=0,
            suggested_min_amount_out=None,
            suggested_max_amount_in=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
            policy_max_overdelivery_gap_bps=None,
        )
    if not isinstance(suggested_slippage_bps, int) or isinstance(suggested_slippage_bps, bool):
        raise TypeError("suggested_slippage_bps must be int")
    if suggested_slippage_bps < 0 or suggested_slippage_bps > 10_000:
        raise ValueError("suggested_slippage_bps must be in [0, 10_000]")

    reserves = _reserves_for_direction(pool, asset_in=asset_in, asset_out=asset_out)
    if reserves is None:
        return SwapPreflightResult(
            ok=False,
            reason="bad_assets",
            kind="exact_in",
            amount_in_quote=int(amount_in),
            amount_out_quote=0,
            suggested_min_amount_out=None,
            suggested_max_amount_in=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
            policy_max_overdelivery_gap_bps=None,
        )

    rin, rout = reserves
    try:
        out, _ = swap_exact_in_for_pool(pool, reserve_in=rin, reserve_out=rout, amount_in=int(amount_in))
    except ValueError:
        return SwapPreflightResult(
            ok=False,
            reason="swap_error",
            kind="exact_in",
            amount_in_quote=int(amount_in),
            amount_out_quote=0,
            suggested_min_amount_out=None,
            suggested_max_amount_in=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
            policy_max_overdelivery_gap_bps=None,
        )

    amount_out_quote = int(out)
    suggested_min_out = (amount_out_quote * (10_000 - suggested_slippage_bps)) // 10_000
    if int(min_amount_out) > amount_out_quote:
        return SwapPreflightResult(
            ok=False,
            reason="min_amount_out_too_high",
            kind="exact_in",
            amount_in_quote=int(amount_in),
            amount_out_quote=amount_out_quote,
            suggested_min_amount_out=int(suggested_min_out),
            suggested_max_amount_in=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
            policy_max_overdelivery_gap_bps=None,
        )

    return SwapPreflightResult(
        ok=True,
        reason="ok",
        kind="exact_in",
        amount_in_quote=int(amount_in),
        amount_out_quote=amount_out_quote,
        suggested_min_amount_out=int(suggested_min_out),
        suggested_max_amount_in=None,
        overdelivery_gap=None,
        overdelivery_gap_bps=None,
        policy_max_overdelivery_gap_bps=None,
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
    if pool.status.value != "ACTIVE":
        return SwapPreflightResult(
            ok=False,
            reason="pool_inactive",
            kind="exact_out",
            amount_in_quote=0,
            amount_out_quote=0,
            suggested_min_amount_out=None,
            suggested_max_amount_in=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
            policy_max_overdelivery_gap_bps=int(policy_max_overdelivery_gap_bps),
        )
    if amount_out <= 0:
        return SwapPreflightResult(
            ok=False,
            reason="bad_amount_out",
            kind="exact_out",
            amount_in_quote=0,
            amount_out_quote=int(amount_out),
            suggested_min_amount_out=None,
            suggested_max_amount_in=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
            policy_max_overdelivery_gap_bps=int(policy_max_overdelivery_gap_bps),
        )
    if max_amount_in < 0:
        return SwapPreflightResult(
            ok=False,
            reason="bad_max_amount_in",
            kind="exact_out",
            amount_in_quote=int(max_amount_in),
            amount_out_quote=int(amount_out),
            suggested_min_amount_out=None,
            suggested_max_amount_in=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
            policy_max_overdelivery_gap_bps=int(policy_max_overdelivery_gap_bps),
        )
    if not isinstance(suggested_slippage_bps, int) or isinstance(suggested_slippage_bps, bool):
        raise TypeError("suggested_slippage_bps must be int")
    if suggested_slippage_bps < 0 or suggested_slippage_bps > 10_000:
        raise ValueError("suggested_slippage_bps must be in [0, 10_000]")
    if not isinstance(policy_max_overdelivery_gap_bps, int) or isinstance(policy_max_overdelivery_gap_bps, bool):
        raise TypeError("policy_max_overdelivery_gap_bps must be int")
    if policy_max_overdelivery_gap_bps < 0 or policy_max_overdelivery_gap_bps > 10_000:
        raise ValueError("policy_max_overdelivery_gap_bps must be in [0, 10_000]")

    reserves = _reserves_for_direction(pool, asset_in=asset_in, asset_out=asset_out)
    if reserves is None:
        return SwapPreflightResult(
            ok=False,
            reason="bad_assets",
            kind="exact_out",
            amount_in_quote=int(max_amount_in),
            amount_out_quote=int(amount_out),
            suggested_min_amount_out=None,
            suggested_max_amount_in=None,
            overdelivery_gap=None,
            overdelivery_gap_bps=None,
            policy_max_overdelivery_gap_bps=int(policy_max_overdelivery_gap_bps),
        )
    rin, rout = reserves

    overdelivery_gap: int | None = None
    overdelivery_gap_bps: int | None = None
    amount_in_quote: int | None = None

    if pool.curve_tag == CURVE_TAG_CPMM:
        try:
            # Compute raw gap info using the audited v8 kernel.
            r = _cpmm_exact_out_kernel_v8(
                reserve_in=int(rin),
                reserve_out=int(rout),
                amount_out=int(amount_out),
                fee_bps=int(pool.fee_bps),
            )
            amount_in_quote = int(r.amount_in)
            overdelivery_gap = int(r.overdelivery_gap)
            overdelivery_gap_bps = ((overdelivery_gap * 10_000) + int(amount_out) - 1) // int(amount_out)
        except ValueError:
            # If gap analysis fails, stay fail-closed but still attempt the quote below.
            overdelivery_gap = None
            overdelivery_gap_bps = None
            amount_in_quote = None

    try:
        if pool.curve_tag == CURVE_TAG_CPMM:
            # Use the same kernel as `swap_exact_out_for_pool` but allow a configurable policy threshold.
            from .cpmm import swap_exact_out as _cpmm_swap_exact_out

            req_in, _ = _cpmm_swap_exact_out(
                reserve_in=int(rin),
                reserve_out=int(rout),
                amount_out=int(amount_out),
                fee_bps=int(pool.fee_bps),
                max_overdelivery_gap_bps=int(policy_max_overdelivery_gap_bps),
            )
        else:
            req_in, _ = swap_exact_out_for_pool(pool, reserve_in=rin, reserve_out=rout, amount_out=int(amount_out))
    except ValueError as exc:
        msg = str(exc)
        reason = "swap_error"
        if "overdelivery gap exceeds" in msg:
            reason = "exact_out_overdelivery_policy"
        return SwapPreflightResult(
            ok=False,
            reason=reason,
            kind="exact_out",
            amount_in_quote=int(amount_in_quote or 0),
            amount_out_quote=int(amount_out),
            suggested_min_amount_out=None,
            suggested_max_amount_in=None,
            overdelivery_gap=overdelivery_gap,
            overdelivery_gap_bps=overdelivery_gap_bps,
            policy_max_overdelivery_gap_bps=int(policy_max_overdelivery_gap_bps),
        )

    req_in_i = int(req_in)
    suggested_max_in = (req_in_i * (10_000 + suggested_slippage_bps) + 9_999) // 10_000
    if req_in_i > int(max_amount_in):
        return SwapPreflightResult(
            ok=False,
            reason="max_amount_in_too_low",
            kind="exact_out",
            amount_in_quote=req_in_i,
            amount_out_quote=int(amount_out),
            suggested_min_amount_out=None,
            suggested_max_amount_in=int(suggested_max_in),
            overdelivery_gap=overdelivery_gap,
            overdelivery_gap_bps=overdelivery_gap_bps,
            policy_max_overdelivery_gap_bps=int(policy_max_overdelivery_gap_bps),
        )

    return SwapPreflightResult(
        ok=True,
        reason="ok",
        kind="exact_out",
        amount_in_quote=req_in_i,
        amount_out_quote=int(amount_out),
        suggested_min_amount_out=None,
        suggested_max_amount_in=int(suggested_max_in),
        overdelivery_gap=overdelivery_gap,
        overdelivery_gap_bps=overdelivery_gap_bps,
        policy_max_overdelivery_gap_bps=int(policy_max_overdelivery_gap_bps),
    )
