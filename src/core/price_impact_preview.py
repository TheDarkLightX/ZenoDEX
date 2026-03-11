"""Deterministic price-impact preview utilities."""

from __future__ import annotations

from dataclasses import dataclass


PRICE_SCALE: int = 100_000_000
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


def compute_spot_price_e8(reserve_in: int, reserve_out: int) -> int:
    """Compute spot price as reserve_out / reserve_in in e8 fixed-point."""
    if reserve_in <= 0 or reserve_out <= 0:
        raise ValueError(f"Reserves must be positive: ({reserve_in}, {reserve_out})")
    return reserve_out * PRICE_SCALE // reserve_in


def compute_isolated_output(
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
) -> tuple[int, int]:
    """Compute isolated exact-in output and fee."""
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
    """Compute price impact in bps relative to spot, excluding fee."""
    amount_out, fee_amount = compute_isolated_output(reserve_in, reserve_out, amount_in, fee_bps)
    net_in = int(amount_in) - int(fee_amount)
    if amount_out <= 0 or net_in <= 0:
        return BPS_SCALE

    numerator = (net_in * reserve_out) - (amount_out * reserve_in)
    denominator = net_in * reserve_out
    return max(0, min(BPS_SCALE, numerator * BPS_SCALE // denominator))


def price_impact_preview(
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
    pending_volume_same_direction: int = 0,
    confidence_bps: int = 9500,
) -> PriceImpactPreview:
    """Build a conservative full preview for UI and wallet checks."""
    if pending_volume_same_direction < 0:
        raise ValueError(
            "pending_volume_same_direction must be non-negative: "
            f"{pending_volume_same_direction}"
        )
    if not (0 <= confidence_bps <= BPS_SCALE):
        raise ValueError(f"confidence_bps must be in [0, {BPS_SCALE}]: {confidence_bps}")

    def _after_pending(*, pending_volume: int) -> tuple[int, int]:
        if pending_volume <= 0:
            return int(reserve_in), int(reserve_out)
        pending_out, _ = compute_isolated_output(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=int(pending_volume),
            fee_bps=fee_bps,
        )
        return int(reserve_in) + int(pending_volume), int(reserve_out) - int(pending_out)

    amount_out_isolated, fee_amount = compute_isolated_output(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )
    spot_price_e8 = compute_spot_price_e8(reserve_in, reserve_out)
    effective_price_e8 = amount_out_isolated * PRICE_SCALE // amount_in if amount_in > 0 else 0
    impact_bps = compute_price_impact_bps(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )

    amount_out_best_case = amount_out_isolated
    reserve_in_after, reserve_out_after = _after_pending(pending_volume=int(pending_volume_same_direction))
    if pending_volume_same_direction == 0:
        amount_out_worst_case = amount_out_best_case
    else:
        amount_out_worst_case, _ = compute_isolated_output(
            reserve_in=int(reserve_in_after),
            reserve_out=int(reserve_out_after),
            amount_in=amount_in,
            fee_bps=fee_bps,
        )

    pending_volume_at_confidence = int(pending_volume_same_direction) * int(confidence_bps) // BPS_SCALE
    reserve_in_conf, reserve_out_conf = _after_pending(pending_volume=int(pending_volume_at_confidence))
    if pending_volume_at_confidence == 0:
        amount_out_at_confidence = amount_out_best_case
    else:
        amount_out_at_confidence, _ = compute_isolated_output(
            reserve_in=int(reserve_in_conf),
            reserve_out=int(reserve_out_conf),
            amount_in=amount_in,
            fee_bps=fee_bps,
        )
    amount_out_at_confidence = max(
        int(amount_out_worst_case),
        min(int(amount_out_best_case), int(amount_out_at_confidence)),
    )

    return PriceImpactPreview(
        amount_out_isolated=amount_out_isolated,
        fee_amount=fee_amount,
        price_impact_bps=impact_bps,
        effective_price_e8=effective_price_e8,
        spot_price_e8=spot_price_e8,
        amount_out_best_case=amount_out_best_case,
        amount_out_worst_case=amount_out_worst_case,
        recommended_min_out=int(amount_out_at_confidence),
        pending_volume_same_direction=int(pending_volume_same_direction),
        confidence_bps=int(confidence_bps),
        pending_volume_at_confidence=int(pending_volume_at_confidence),
        amount_out_at_confidence=int(amount_out_at_confidence),
    )
