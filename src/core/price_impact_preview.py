"""Deterministic price-impact preview utilities.

This module provides pure integer math helpers for pre-trade UX:
- isolated output quote and fee
- spot/effective price impact
- best/worst execution bounds given pending same-direction volume
- conservative `min_out` recommendation
"""

from __future__ import annotations

from dataclasses import dataclass

PRICE_SCALE: int = 100_000_000  # e8 fixed-point
BPS_SCALE: int = 10_000


@dataclass(frozen=True)
class PriceImpactPreview:
    """Pre-trade preview package."""

    amount_out_isolated: int
    fee_amount: int
    price_impact_bps: int
    effective_price_e8: int
    spot_price_e8: int
    amount_out_best_case: int
    amount_out_worst_case: int
    recommended_min_out: int
    pending_volume_same_direction: int
    confidence_bps: int
    pending_volume_at_confidence: int
    amount_out_at_confidence: int


@dataclass(frozen=True)
class _PreviewQuoteContext:
    reserve_in: int
    reserve_out: int
    amount_in: int
    fee_bps: int


@dataclass(frozen=True)
class _BasePreviewQuotes:
    amount_out_isolated: int
    fee_amount: int
    spot_price_e8: int
    effective_price_e8: int
    impact_bps: int


def compute_spot_price_e8(reserve_in: int, reserve_out: int) -> int:
    """Compute spot price as `reserve_out / reserve_in` in e8 fixed-point."""
    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError(f"Reserves must be positive: ({reserve_in}, {reserve_out})")
    return reserve_out * PRICE_SCALE // reserve_in


def compute_isolated_output(
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
) -> tuple[int, int]:
    """Compute isolated exact-in output and fee.

    Rounding:
    - fee = ceil(amount_in * fee_bps / 10_000)
    - amount_out = floor(reserve_out * net_in / (reserve_in + net_in))
    """
    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError(f"Reserves must be positive: ({reserve_in}, {reserve_out})")
    if amount_in <= 0:
        raise ValueError(f"amount_in must be positive: {amount_in}")
    if not (0 <= fee_bps <= BPS_SCALE):
        raise ValueError(f"fee_bps must be in [0, {BPS_SCALE}]: {fee_bps}")

    fee_amount = (amount_in * fee_bps + BPS_SCALE - 1) // BPS_SCALE
    net_in = amount_in - fee_amount
    if net_in <= 0:
        return 0, fee_amount
    amount_out = reserve_out * net_in // (reserve_in + net_in)
    return amount_out, fee_amount


def compute_price_impact_bps(
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
) -> int:
    """Compute price impact in bps relative to spot (excluding fee).

    We separate fee from impact:
    - `compute_isolated_output` returns (amount_out, fee_amount).
    - Here we measure *slippage* by comparing the net-execution price to spot:
        impact = 1 - (amount_out / net_in) / (reserve_out / reserve_in)

    This matches the Lean/ESSO definition used by UX proofs:
      i(a) = α*a / (x + α*a) where α = (BPS - fee) / BPS.
    """
    amount_out, fee_amount = compute_isolated_output(reserve_in, reserve_out, amount_in, fee_bps)
    net_in = int(amount_in) - int(fee_amount)
    if amount_out <= 0 or net_in <= 0:
        return BPS_SCALE

    numerator = (net_in * reserve_out) - (amount_out * reserve_in)
    denominator = net_in * reserve_out
    return max(0, min(BPS_SCALE, numerator * BPS_SCALE // denominator))


def _reserves_after_pending(ctx: _PreviewQuoteContext, pending_volume: int) -> tuple[int, int]:
    if pending_volume <= 0:
        return int(ctx.reserve_in), int(ctx.reserve_out)
    pending_out, _ = compute_isolated_output(
        reserve_in=ctx.reserve_in,
        reserve_out=ctx.reserve_out,
        amount_in=int(pending_volume),
        fee_bps=ctx.fee_bps,
    )
    return int(ctx.reserve_in) + int(pending_volume), int(ctx.reserve_out) - int(pending_out)


def _amount_out_after_pending(
    ctx: _PreviewQuoteContext,
    *,
    pending_volume: int,
    fallback_out: int,
) -> int:
    if pending_volume == 0:
        return int(fallback_out)
    reserve_in_after, reserve_out_after = _reserves_after_pending(ctx, int(pending_volume))
    amount_out, _ = compute_isolated_output(
        reserve_in=int(reserve_in_after),
        reserve_out=int(reserve_out_after),
        amount_in=ctx.amount_in,
        fee_bps=ctx.fee_bps,
    )
    return int(amount_out)


def _clamp_confidence_output(*, amount_out: int, best_case: int, worst_case: int) -> int:
    return max(int(worst_case), min(int(best_case), int(amount_out)))


def _compute_base_preview_quotes(ctx: _PreviewQuoteContext) -> _BasePreviewQuotes:
    amount_out_isolated, fee_amount = compute_isolated_output(
        reserve_in=ctx.reserve_in,
        reserve_out=ctx.reserve_out,
        amount_in=ctx.amount_in,
        fee_bps=ctx.fee_bps,
    )
    return _BasePreviewQuotes(
        amount_out_isolated=amount_out_isolated,
        fee_amount=fee_amount,
        spot_price_e8=compute_spot_price_e8(ctx.reserve_in, ctx.reserve_out),
        effective_price_e8=amount_out_isolated * PRICE_SCALE // ctx.amount_in if ctx.amount_in > 0 else 0,
        impact_bps=compute_price_impact_bps(
            reserve_in=ctx.reserve_in,
            reserve_out=ctx.reserve_out,
            amount_in=ctx.amount_in,
            fee_bps=ctx.fee_bps,
        ),
    )


def _pending_preview_outputs(
    ctx: _PreviewQuoteContext,
    *,
    amount_out_best_case: int,
    pending_volume_same_direction: int,
    confidence_bps: int,
) -> tuple[int, int, int]:
    amount_out_worst_case = _amount_out_after_pending(
        ctx,
        pending_volume=int(pending_volume_same_direction),
        fallback_out=amount_out_best_case,
    )
    pending_volume_at_confidence = int(pending_volume_same_direction) * int(confidence_bps) // BPS_SCALE
    amount_out_at_confidence = _amount_out_after_pending(
        ctx,
        pending_volume=int(pending_volume_at_confidence),
        fallback_out=amount_out_best_case,
    )
    return (
        amount_out_worst_case,
        pending_volume_at_confidence,
        _clamp_confidence_output(
            amount_out=amount_out_at_confidence,
            best_case=amount_out_best_case,
            worst_case=amount_out_worst_case,
        ),
    )


def price_impact_preview(
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    pending_volume_same_direction: int = 0,
    confidence_bps: int = 9500,
) -> PriceImpactPreview:
    """Build full preview for UI/wallet checks.

    `confidence_bps` controls how much pending volume is simulated before the
    user trade. We evaluate that CPMM state directly because linear interpolation
    between best/worst can be too optimistic under integer semantics.
    """
    if pending_volume_same_direction < 0:
        raise ValueError(
            "pending_volume_same_direction must be non-negative: "
            f"{pending_volume_same_direction}"
        )
    if not (0 <= confidence_bps <= BPS_SCALE):
        raise ValueError(f"confidence_bps must be in [0, {BPS_SCALE}]: {confidence_bps}")

    quote_ctx = _PreviewQuoteContext(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )
    base = _compute_base_preview_quotes(quote_ctx)
    amount_out_worst_case, pending_volume_at_confidence, amount_out_at_confidence = _pending_preview_outputs(
        quote_ctx,
        amount_out_best_case=base.amount_out_isolated,
        pending_volume_same_direction=int(pending_volume_same_direction),
        confidence_bps=int(confidence_bps),
    )
    recommended_min_out = int(amount_out_at_confidence)

    return PriceImpactPreview(
        amount_out_isolated=base.amount_out_isolated,
        fee_amount=base.fee_amount,
        price_impact_bps=base.impact_bps,
        effective_price_e8=base.effective_price_e8,
        spot_price_e8=base.spot_price_e8,
        amount_out_best_case=base.amount_out_isolated,
        amount_out_worst_case=amount_out_worst_case,
        recommended_min_out=recommended_min_out,
        pending_volume_same_direction=pending_volume_same_direction,
        confidence_bps=int(confidence_bps),
        pending_volume_at_confidence=int(pending_volume_at_confidence),
        amount_out_at_confidence=int(amount_out_at_confidence),
    )
