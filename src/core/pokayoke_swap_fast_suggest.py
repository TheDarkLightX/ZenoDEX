"""Fast deterministic swap-size suggestions for UX guardrails."""

from __future__ import annotations

from dataclasses import dataclass

from .price_impact_preview import BPS_SCALE, price_impact_preview


@dataclass(frozen=True)
class FastSwapAmountSuggestion:
    kind: str  # "impact_lt_bps" | "required_slippage_le_bps"
    target_bps: int
    suggested_amount_in: int | None
    status: str  # "ok" | "not_found" | "invalid"
    eval_count: int
    baseline_value_bps: int
    suggested_value_bps: int | None


def _ceil_div(n: int, d: int) -> int:
    if d <= 0:
        raise ValueError("denominator must be positive")
    return (int(n) + int(d) - 1) // int(d)


def suggest_amount_in_for_impact_lt_bps(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    amount_in: int,
    target_impact_bps: int,
    window: int = 128,
) -> FastSwapAmountSuggestion:
    """Suggest amount_in such that price_impact_bps < target_impact_bps."""
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if target_impact_bps <= 0 or target_impact_bps > BPS_SCALE:
        return FastSwapAmountSuggestion(
            kind="impact_lt_bps",
            target_bps=int(target_impact_bps),
            suggested_amount_in=None,
            status="invalid",
            eval_count=0,
            baseline_value_bps=0,
            suggested_value_bps=None,
        )
    if window < 0:
        raise ValueError("window must be non-negative")

    def _impact(a: int) -> int:
        pv = price_impact_preview(
            reserve_in=int(reserve_in),
            reserve_out=int(reserve_out),
            amount_in=int(a),
            fee_bps=int(fee_bps),
            pending_volume_same_direction=0,
            confidence_bps=0,
        )
        return int(pv.price_impact_bps)

    baseline = _impact(int(amount_in))
    if baseline < int(target_impact_bps):
        return FastSwapAmountSuggestion(
            kind="impact_lt_bps",
            target_bps=int(target_impact_bps),
            suggested_amount_in=int(amount_in),
            status="ok",
            eval_count=1,
            baseline_value_bps=int(baseline),
            suggested_value_bps=int(baseline),
        )

    f = 10_000 - int(fee_bps)
    guess = None
    if 0 < int(target_impact_bps) < 10_000 and f > 0:
        denom = int(f) * (10_000 - int(target_impact_bps))
        if denom > 0:
            guess = max(1, (int(reserve_in) * int(target_impact_bps) * 10_000) // denom)

    center = int(guess) if guess is not None else int(amount_in)
    lo = max(1, int(center) - int(window))
    hi = min(int(amount_in), int(center) + int(window))

    evals = 1
    for a in range(int(hi), int(lo) - 1, -1):
        if a == int(amount_in):
            continue
        evals += 1
        imp = _impact(int(a))
        if imp < int(target_impact_bps):
            return FastSwapAmountSuggestion(
                kind="impact_lt_bps",
                target_bps=int(target_impact_bps),
                suggested_amount_in=int(a),
                status="ok",
                eval_count=int(evals),
                baseline_value_bps=int(baseline),
                suggested_value_bps=int(imp),
            )

    return FastSwapAmountSuggestion(
        kind="impact_lt_bps",
        target_bps=int(target_impact_bps),
        suggested_amount_in=None,
        status="not_found",
        eval_count=int(evals),
        baseline_value_bps=int(baseline),
        suggested_value_bps=None,
    )


def suggest_amount_in_for_required_slippage_le_bps(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    amount_in: int,
    pending_volume_same_direction: int,
    confidence_bps: int,
    target_required_slippage_bps: int,
    window: int = 128,
) -> FastSwapAmountSuggestion:
    """Suggest amount_in such that required_slippage_bps <= target_required_slippage_bps."""
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    if target_required_slippage_bps < 0 or target_required_slippage_bps > BPS_SCALE:
        return FastSwapAmountSuggestion(
            kind="required_slippage_le_bps",
            target_bps=int(target_required_slippage_bps),
            suggested_amount_in=None,
            status="invalid",
            eval_count=0,
            baseline_value_bps=0,
            suggested_value_bps=None,
        )
    if window < 0:
        raise ValueError("window must be non-negative")

    def _required(a: int) -> int:
        pv = price_impact_preview(
            reserve_in=int(reserve_in),
            reserve_out=int(reserve_out),
            amount_in=int(a),
            fee_bps=int(fee_bps),
            pending_volume_same_direction=int(pending_volume_same_direction),
            confidence_bps=int(confidence_bps),
        )
        best = int(pv.amount_out_best_case)
        out_conf = int(pv.amount_out_at_confidence)
        if best <= 0:
            return BPS_SCALE
        gap = max(0, best - out_conf)
        return _ceil_div(gap * BPS_SCALE, best) if gap > 0 else 0

    baseline = _required(int(amount_in))
    if int(baseline) <= int(target_required_slippage_bps):
        return FastSwapAmountSuggestion(
            kind="required_slippage_le_bps",
            target_bps=int(target_required_slippage_bps),
            suggested_amount_in=int(amount_in),
            status="ok",
            eval_count=1,
            baseline_value_bps=int(baseline),
            suggested_value_bps=int(baseline),
        )

    evals = 1
    cand = None
    for num, den in (
        (3, 4),
        (1, 2),
        (1, 3),
        (1, 4),
        (1, 5),
        (3, 20),
        (1, 10),
        (3, 40),
        (1, 20),
        (1, 40),
        (1, 100),
    ):
        a = max(1, (int(amount_in) * int(num)) // int(den))
        if a >= int(amount_in):
            continue
        evals += 1
        req = _required(int(a))
        if int(req) <= int(target_required_slippage_bps):
            cand = int(a)
            baseline = int(baseline)
            break

    if cand is None:
        return FastSwapAmountSuggestion(
            kind="required_slippage_le_bps",
            target_bps=int(target_required_slippage_bps),
            suggested_amount_in=None,
            status="not_found",
            eval_count=int(evals),
            baseline_value_bps=int(baseline),
            suggested_value_bps=None,
        )

    lo = max(1, int(cand) - int(window))
    hi = min(int(amount_in), int(cand) + int(window))
    for a in range(int(hi), int(lo) - 1, -1):
        evals += 1
        req = _required(int(a))
        if int(req) <= int(target_required_slippage_bps):
            return FastSwapAmountSuggestion(
                kind="required_slippage_le_bps",
                target_bps=int(target_required_slippage_bps),
                suggested_amount_in=int(a),
                status="ok",
                eval_count=int(evals),
                baseline_value_bps=int(baseline),
                suggested_value_bps=int(req),
            )

    return FastSwapAmountSuggestion(
        kind="required_slippage_le_bps",
        target_bps=int(target_required_slippage_bps),
        suggested_amount_in=int(cand),
        status="ok",
        eval_count=int(evals),
        baseline_value_bps=int(baseline),
        suggested_value_bps=_required(int(cand)),
    )
