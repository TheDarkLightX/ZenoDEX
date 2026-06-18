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


_REQUIRED_SLIPPAGE_REDUCTION_FRACS: tuple[tuple[int, int], ...] = (
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
)


@dataclass(frozen=True)
class _ImpactSearch:
    reserve_in: int
    reserve_out: int
    fee_bps: int

    def impact_bps(self, amount_in: int) -> int:
        pv = price_impact_preview(
            reserve_in=int(self.reserve_in),
            reserve_out=int(self.reserve_out),
            amount_in=int(amount_in),
            fee_bps=int(self.fee_bps),
            pending_volume_same_direction=0,
            confidence_bps=0,
        )
        return int(pv.price_impact_bps)


@dataclass(frozen=True)
class _RequiredSlippageSearch:
    reserve_in: int
    reserve_out: int
    fee_bps: int
    pending_volume_same_direction: int
    confidence_bps: int

    def required_slippage_bps(self, amount_in: int) -> int:
        pv = price_impact_preview(
            reserve_in=int(self.reserve_in),
            reserve_out=int(self.reserve_out),
            amount_in=int(amount_in),
            fee_bps=int(self.fee_bps),
            pending_volume_same_direction=int(self.pending_volume_same_direction),
            confidence_bps=int(self.confidence_bps),
        )
        best = int(pv.amount_out_best_case)
        out_conf = int(pv.amount_out_at_confidence)
        if best <= 0:
            return BPS_SCALE
        gap = max(0, best - out_conf)
        return _ceil_div(gap * BPS_SCALE, best) if gap > 0 else 0


def _ceil_div(n: int, d: int) -> int:
    if d <= 0:
        raise ValueError("denominator must be positive")
    return (int(n) + int(d) - 1) // int(d)


def _validate_positive_amount(amount_in: int) -> None:
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")


def _validate_nonnegative_window(window: int) -> None:
    if window < 0:
        raise ValueError("window must be non-negative")


def _invalid_suggestion(*, kind: str, target_bps: int) -> FastSwapAmountSuggestion:
    return FastSwapAmountSuggestion(
        kind=kind,
        target_bps=int(target_bps),
        suggested_amount_in=None,
        status="invalid",
        eval_count=0,
        baseline_value_bps=0,
        suggested_value_bps=None,
    )


def _ok_suggestion(
    *,
    kind: str,
    target_bps: int,
    amount_in: int,
    eval_count: int,
    baseline_value_bps: int,
    suggested_value_bps: int,
) -> FastSwapAmountSuggestion:
    return FastSwapAmountSuggestion(
        kind=kind,
        target_bps=int(target_bps),
        suggested_amount_in=int(amount_in),
        status="ok",
        eval_count=int(eval_count),
        baseline_value_bps=int(baseline_value_bps),
        suggested_value_bps=int(suggested_value_bps),
    )


def _not_found_suggestion(
    *,
    kind: str,
    target_bps: int,
    eval_count: int,
    baseline_value_bps: int,
) -> FastSwapAmountSuggestion:
    return FastSwapAmountSuggestion(
        kind=kind,
        target_bps=int(target_bps),
        suggested_amount_in=None,
        status="not_found",
        eval_count=int(eval_count),
        baseline_value_bps=int(baseline_value_bps),
        suggested_value_bps=None,
    )


def _impact_guess_amount_in(*, reserve_in: int, fee_bps: int, target_impact_bps: int) -> int | None:
    f = 10_000 - int(fee_bps)
    if not (0 < int(target_impact_bps) < 10_000) or f <= 0:
        return None
    denom = int(f) * (10_000 - int(target_impact_bps))
    if denom <= 0:
        return None
    return max(1, (int(reserve_in) * int(target_impact_bps) * 10_000) // denom)


def _window_bounds(*, amount_in: int, center: int, window: int) -> tuple[int, int]:
    lo = max(1, int(center) - int(window))
    hi = min(int(amount_in), int(center) + int(window))
    return int(lo), int(hi)


def _scan_impact_window(
    *,
    search: _ImpactSearch,
    amount_in: int,
    target_impact_bps: int,
    lo: int,
    hi: int,
) -> tuple[int | None, int | None, int]:
    evals = 1
    for candidate in range(int(hi), int(lo) - 1, -1):
        if candidate == int(amount_in):
            continue
        evals += 1
        impact_bps = search.impact_bps(int(candidate))
        if impact_bps < int(target_impact_bps):
            return int(candidate), int(impact_bps), int(evals)
    return None, None, int(evals)


def _required_slippage_reduction_candidates(amount_in: int) -> list[int]:
    return [
        max(1, (int(amount_in) * int(num)) // int(den))
        for num, den in _REQUIRED_SLIPPAGE_REDUCTION_FRACS
    ]


def _find_required_slippage_coarse_candidate(
    *,
    search: _RequiredSlippageSearch,
    amount_in: int,
    target_required_slippage_bps: int,
) -> tuple[int | None, int]:
    evals = 1
    for candidate in _required_slippage_reduction_candidates(amount_in):
        if candidate >= int(amount_in):
            continue
        evals += 1
        req_bps = search.required_slippage_bps(int(candidate))
        if int(req_bps) <= int(target_required_slippage_bps):
            return int(candidate), int(evals)
    return None, int(evals)


def _scan_required_slippage_window(
    *,
    search: _RequiredSlippageSearch,
    target_required_slippage_bps: int,
    amount_in: int,
    candidate: int,
    window: int,
    evals: int,
    baseline_bps: int,
) -> FastSwapAmountSuggestion:
    lo, hi = _window_bounds(amount_in=amount_in, center=candidate, window=window)
    for probe in range(int(hi), int(lo) - 1, -1):
        evals += 1
        req_bps = search.required_slippage_bps(int(probe))
        if int(req_bps) <= int(target_required_slippage_bps):
            return _ok_suggestion(
                kind="required_slippage_le_bps",
                target_bps=target_required_slippage_bps,
                amount_in=probe,
                eval_count=evals,
                baseline_value_bps=baseline_bps,
                suggested_value_bps=req_bps,
            )

    return _ok_suggestion(
        kind="required_slippage_le_bps",
        target_bps=target_required_slippage_bps,
        amount_in=candidate,
        eval_count=evals,
        baseline_value_bps=baseline_bps,
        suggested_value_bps=search.required_slippage_bps(int(candidate)),
    )


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
    _validate_positive_amount(amount_in)
    if target_impact_bps <= 0 or target_impact_bps > BPS_SCALE:
        return _invalid_suggestion(kind="impact_lt_bps", target_bps=target_impact_bps)
    _validate_nonnegative_window(window)

    search = _ImpactSearch(reserve_in=reserve_in, reserve_out=reserve_out, fee_bps=fee_bps)
    baseline = search.impact_bps(int(amount_in))
    if baseline < int(target_impact_bps):
        return _ok_suggestion(
            kind="impact_lt_bps",
            target_bps=int(target_impact_bps),
            amount_in=int(amount_in),
            eval_count=1,
            baseline_value_bps=int(baseline),
            suggested_value_bps=int(baseline),
        )

    guess = _impact_guess_amount_in(
        reserve_in=reserve_in,
        fee_bps=fee_bps,
        target_impact_bps=target_impact_bps,
    )
    center = int(guess) if guess is not None else int(amount_in)
    lo, hi = _window_bounds(amount_in=amount_in, center=center, window=window)
    suggested_amount, suggested_bps, evals = _scan_impact_window(
        search=search,
        amount_in=amount_in,
        target_impact_bps=target_impact_bps,
        lo=lo,
        hi=hi,
    )
    if suggested_amount is not None and suggested_bps is not None:
        return _ok_suggestion(
            kind="impact_lt_bps",
            target_bps=int(target_impact_bps),
            amount_in=suggested_amount,
            eval_count=evals,
            baseline_value_bps=int(baseline),
            suggested_value_bps=suggested_bps,
        )

    return _not_found_suggestion(
        kind="impact_lt_bps",
        target_bps=int(target_impact_bps),
        eval_count=int(evals),
        baseline_value_bps=int(baseline),
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
    _validate_positive_amount(amount_in)
    if target_required_slippage_bps < 0 or target_required_slippage_bps > BPS_SCALE:
        return _invalid_suggestion(kind="required_slippage_le_bps", target_bps=target_required_slippage_bps)
    _validate_nonnegative_window(window)

    search = _RequiredSlippageSearch(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        fee_bps=fee_bps,
        pending_volume_same_direction=pending_volume_same_direction,
        confidence_bps=confidence_bps,
    )
    baseline = search.required_slippage_bps(int(amount_in))
    if int(baseline) <= int(target_required_slippage_bps):
        return _ok_suggestion(
            kind="required_slippage_le_bps",
            target_bps=int(target_required_slippage_bps),
            amount_in=int(amount_in),
            eval_count=1,
            baseline_value_bps=int(baseline),
            suggested_value_bps=int(baseline),
        )

    candidate, evals = _find_required_slippage_coarse_candidate(
        search=search,
        amount_in=amount_in,
        target_required_slippage_bps=target_required_slippage_bps,
    )
    if candidate is None:
        return _not_found_suggestion(
            kind="required_slippage_le_bps",
            target_bps=int(target_required_slippage_bps),
            eval_count=int(evals),
            baseline_value_bps=int(baseline),
        )

    return _scan_required_slippage_window(
        search=search,
        target_required_slippage_bps=target_required_slippage_bps,
        amount_in=amount_in,
        candidate=candidate,
        window=window,
        evals=evals,
        baseline_bps=int(baseline),
    )
