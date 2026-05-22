"""Deterministic slippage advice (UX + security + automation).

This module turns multiple UX/security signals into a small, explainable
"slippage frontier":
- revert safety at a confidence-adjusted pending-volume level (CAPIB-style)
- sandwich profit exposure under a bounded, deterministic MEV model

Design posture:
- deterministic integer-only math
- explicit bounds and INCONCLUSIVE semantics (never treat unknown as safe)
"""

from __future__ import annotations

from dataclasses import dataclass

from .price_impact_preview import BPS_SCALE, price_impact_preview
from .sandwich_risk import max_sandwich_profit_exact_in_cpmm_bounded


@dataclass(frozen=True)
class SlippageOptionAssessment:
    slippage_bps: int
    min_amount_out: int

    # Revert-safety proxy at the confidence-adjusted pending volume level:
    # min_amount_out <= amount_out_at_confidence.
    is_revert_safe_at_confidence: bool

    # Sandwich model result (bounded; may be inconclusive).
    sandwich_status: str  # "ok" | "victim_reverts" | "inconclusive"
    sandwich_max_profit: int
    sandwich_attacker_amount_in: int
    sandwich_victim_amount_out: int
    sandwich_scanned_max_attacker_amount_in: int


@dataclass(frozen=True)
class SlippageAdvice:
    # Core preview numbers.
    best_amount_out: int
    price_impact_bps: int
    amount_out_at_confidence: int
    pending_volume_at_confidence: int
    confidence_bps: int

    # Minimal slippage in bps (ceil) needed so that:
    # best_out * (BPS - slippage) / BPS <= amount_out_at_confidence.
    required_slippage_bps: int

    # Evaluations for each candidate slippage choice.
    options: list[SlippageOptionAssessment]

    # Derived recommendations among the provided `options` set.
    recommended_slippage_bps_revert_safe: int | None
    recommended_slippage_bps_mev_safe: int | None
    recommended_slippage_bps: int | None

    # Summary status / reason codes for UIs/agents.
    status: str  # "ok" | "mev_conflict" | "inconclusive_mev" | "no_revert_safe_option"


def _ceil_div(n: int, d: int) -> int:
    if d <= 0:
        raise ValueError("denominator must be positive")
    return (int(n) + int(d) - 1) // int(d)


def slippage_advice_exact_in_cpmm(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    amount_in: int,
    pending_volume_same_direction: int = 0,
    confidence_bps: int = 9500,
    slippage_options_bps: list[int] | None = None,
    max_attacker_amount_in: int = 5_000,
) -> SlippageAdvice:
    """Compute slippage advice for a CPMM exact-in swap.

    The caller provides a discrete set of `slippage_options_bps` (e.g. UI buttons).
    We evaluate each option and return:
    - the smallest option that is revert-safe at `confidence_bps`
    - the largest option that is MEV-safe (only if the sandwich scan is conclusive)

    Note: The MEV-safe condition is intentionally strict:
      sandwich_status must be "ok" and sandwich_max_profit <= 0.
    """
    if slippage_options_bps is None:
        slippage_options_bps = [10, 50, 100, 300]

    if not isinstance(max_attacker_amount_in, int) or isinstance(max_attacker_amount_in, bool):
        raise TypeError("max_attacker_amount_in must be int")
    if max_attacker_amount_in < 0:
        raise ValueError("max_attacker_amount_in must be non-negative")

    # Normalize options deterministically.
    opts: list[int] = []
    seen = set()
    for raw in slippage_options_bps:
        if not isinstance(raw, int) or isinstance(raw, bool):
            continue
        if raw < 0 or raw > BPS_SCALE:
            continue
        if raw in seen:
            continue
        seen.add(int(raw))
        opts.append(int(raw))
    opts.sort()
    if not opts:
        raise ValueError("no valid slippage_options_bps")

    preview = price_impact_preview(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        amount_in=int(amount_in),
        fee_bps=int(fee_bps),
        pending_volume_same_direction=int(pending_volume_same_direction),
        confidence_bps=int(confidence_bps),
    )
    best_out = int(preview.amount_out_best_case)
    out_conf = int(preview.amount_out_at_confidence)
    pv_conf = int(preview.pending_volume_at_confidence)

    if best_out <= 0:
        # Degenerate; return a fail-closed object.
        return SlippageAdvice(
            best_amount_out=best_out,
            price_impact_bps=BPS_SCALE,
            amount_out_at_confidence=out_conf,
            pending_volume_at_confidence=pv_conf,
            confidence_bps=int(confidence_bps),
            required_slippage_bps=BPS_SCALE,
            options=[],
            recommended_slippage_bps_revert_safe=None,
            recommended_slippage_bps_mev_safe=None,
            recommended_slippage_bps=None,
            status="no_revert_safe_option",
        )

    gap = max(0, best_out - out_conf)
    required_slip = _ceil_div(gap * BPS_SCALE, best_out) if gap > 0 else 0
    required_slip = max(0, min(BPS_SCALE, int(required_slip)))

    assessments: list[SlippageOptionAssessment] = []
    for slip_bps in opts:
        min_out = (best_out * (BPS_SCALE - int(slip_bps))) // BPS_SCALE
        is_safe = bool(int(min_out) <= int(out_conf))
        risk = max_sandwich_profit_exact_in_cpmm_bounded(
            reserve_in=int(reserve_in),
            reserve_out=int(reserve_out),
            fee_bps=int(fee_bps),
            victim_amount_in=int(amount_in),
            victim_min_out=int(min_out),
            max_attacker_amount_in=int(max_attacker_amount_in),
        )
        assessments.append(
            SlippageOptionAssessment(
                slippage_bps=int(slip_bps),
                min_amount_out=int(min_out),
                is_revert_safe_at_confidence=bool(is_safe),
                sandwich_status=str(risk.status),
                sandwich_max_profit=int(risk.max_profit),
                sandwich_attacker_amount_in=int(risk.attacker_amount_in),
                sandwich_victim_amount_out=int(risk.victim_amount_out),
                sandwich_scanned_max_attacker_amount_in=int(risk.scanned_max_attacker_amount_in),
            )
        )

    # Revert-safe recommendation among options.
    rec_revert_safe: int | None = None
    for a in assessments:
        if a.is_revert_safe_at_confidence:
            rec_revert_safe = int(a.slippage_bps)
            break

    # MEV-safe ceiling among options (only with conclusive scan).
    rec_mev_safe: int | None = None
    for a in assessments:
        if a.sandwich_status == "ok" and a.sandwich_max_profit <= 0:
            rec_mev_safe = int(a.slippage_bps)
        else:
            # Since profit is monotone in slippage when the scan is conclusive,
            # and we require conclusive scans for MEV-safe, this is a safe stop.
            continue

    status = "ok"
    recommended: int | None = rec_revert_safe
    if rec_revert_safe is None:
        status = "no_revert_safe_option"
        recommended = None
    else:
        rec_assessment = next(a for a in assessments if int(a.slippage_bps) == int(rec_revert_safe))
        if rec_assessment.sandwich_status != "ok":
            status = "inconclusive_mev"
        elif rec_assessment.sandwich_max_profit > 0:
            status = "mev_conflict"

    return SlippageAdvice(
        best_amount_out=best_out,
        price_impact_bps=int(preview.price_impact_bps),
        amount_out_at_confidence=out_conf,
        pending_volume_at_confidence=pv_conf,
        confidence_bps=int(confidence_bps),
        required_slippage_bps=int(required_slip),
        options=assessments,
        recommended_slippage_bps_revert_safe=rec_revert_safe,
        recommended_slippage_bps_mev_safe=rec_mev_safe,
        recommended_slippage_bps=recommended,
        status=str(status),
    )
