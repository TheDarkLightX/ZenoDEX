"""Poka-yoke swap sizing suggestions (UX-only, deterministic).

This module proposes smaller `amount_in` values that reduce interlock severity
for the current deterministic guardrail policy.

Important:
- This is an *experiment* tool for UX and automation. It does not change
  consensus semantics.
- The search is explicitly budgeted and may return INCONCLUSIVE.
"""

from __future__ import annotations

from dataclasses import dataclass

from .pokayoke_swap_fast_suggest import (
    FastSwapAmountSuggestion,
    suggest_amount_in_for_impact_lt_bps,
    suggest_amount_in_for_required_slippage_le_bps,
)
from .pokayoke_swap_guardrails import (
    SwapGuardrailContext,
    SwapGuardrailDecision,
    decide_swap_guardrails,
)
from .slippage_advisor import SlippageAdvice, slippage_advice_exact_in_cpmm

__all__ = (
    "FastSwapAmountSuggestion",
    "SwapAmountSuggestion",
    "suggest_amount_in_exact_in_cpmm",
    "suggest_amount_in_for_impact_lt_bps",
    "suggest_amount_in_for_required_slippage_le_bps",
)

_IMPACT_REDUCTION_FRACS: tuple[tuple[int, int], ...] = (
    (1, 4),
    (1, 5),
    (3, 20),
    (1, 10),
    (3, 40),
    (1, 20),
    (1, 25),
    (3, 100),
    (1, 40),
    (1, 50),
    (3, 200),
    (1, 100),
)

_GENERIC_REDUCTION_FRACS: tuple[tuple[int, int], ...] = (
    (1, 2),
    (1, 3),
    (1, 4),
    (1, 5),
    (3, 20),
    (1, 10),
    (3, 40),
    (1, 20),
    (1, 25),
    (3, 100),
    (1, 40),
    (1, 50),
    (3, 200),
    (1, 100),
)


@dataclass(frozen=True)
class SwapAmountSuggestion:
    target_action: str  # "allow" | "confirm"
    suggested_amount_in: int | None
    status: str  # "ok" | "not_found" | "invalid"
    eval_count: int

    # Debug/evidence hooks (deterministic summaries).
    baseline_action: str
    suggested_action: str | None
    baseline_reasons: tuple[str, ...]
    suggested_reasons: tuple[str, ...] | None


def _action_severity(action: str) -> int:
    a = str(action or "").strip().lower()
    if a == "allow":
        return 0
    if a == "confirm":
        return 1
    if a == "typed_confirm":
        return 2
    if a == "block":
        return 3
    # Unknown action is treated as worst (fail-closed).
    return 9


def _mk_ctx(advice: SlippageAdvice) -> SwapGuardrailContext:
    return SwapGuardrailContext(
        price_impact_bps=int(advice.price_impact_bps),
        slippage_advice_status=str(advice.status),
        required_slippage_bps=int(advice.required_slippage_bps),
        recommended_slippage_bps_revert_safe=(
            int(advice.recommended_slippage_bps_revert_safe) if advice.recommended_slippage_bps_revert_safe is not None else None
        ),
        recommended_slippage_bps_mev_safe=(
            int(advice.recommended_slippage_bps_mev_safe) if advice.recommended_slippage_bps_mev_safe is not None else None
        ),
        recommended_slippage_bps=(
            int(advice.recommended_slippage_bps) if advice.recommended_slippage_bps is not None else None
        ),
    )


def _eval_amount(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    amount_in: int,
    pending_volume_same_direction: int,
    confidence_bps: int,
    slippage_options_bps: list[int] | None,
    max_attacker_amount_in: int,
    user_slippage_bps: int,
) -> tuple[SlippageAdvice, SwapGuardrailDecision]:
    advice = slippage_advice_exact_in_cpmm(
        reserve_in=int(reserve_in),
        reserve_out=int(reserve_out),
        fee_bps=int(fee_bps),
        amount_in=int(amount_in),
        pending_volume_same_direction=int(pending_volume_same_direction),
        confidence_bps=int(confidence_bps),
        slippage_options_bps=slippage_options_bps,
        max_attacker_amount_in=int(max_attacker_amount_in),
    )
    decision = decide_swap_guardrails(ctx=_mk_ctx(advice), user_slippage_bps=int(user_slippage_bps))
    return advice, decision


@dataclass(frozen=True)
class _EvalParams:
    reserve_in: int
    reserve_out: int
    fee_bps: int
    pending_volume_same_direction: int
    confidence_bps: int
    slippage_options_bps: list[int] | None
    max_attacker_amount_in: int
    user_slippage_bps: int

    def eval_amount(self, amount_in: int) -> tuple[SlippageAdvice, SwapGuardrailDecision]:
        return _eval_amount(
            reserve_in=self.reserve_in,
            reserve_out=self.reserve_out,
            fee_bps=self.fee_bps,
            amount_in=int(amount_in),
            pending_volume_same_direction=self.pending_volume_same_direction,
            confidence_bps=self.confidence_bps,
            slippage_options_bps=self.slippage_options_bps,
            max_attacker_amount_in=self.max_attacker_amount_in,
            user_slippage_bps=self.user_slippage_bps,
        )


@dataclass(frozen=True)
class _SearchParams:
    eval_params: _EvalParams
    candidates: list[int]
    amount_in: int
    max_evals: int
    baseline_action: str
    baseline_reasons: tuple[str, ...]


def _impact_guess_amount_in(*, reserve_in: int, fee_bps: int, impact_bps: int) -> int | None:
    """Continuous CPMM impact inversion guess for deterministic probe ordering.

    This is a search heuristic only; the final guardrail decision is still
    evaluated with integer runtime math.
    """
    if impact_bps <= 0 or impact_bps >= 10_000:
        return None
    f = 10_000 - int(fee_bps)
    if f <= 0:
        return None
    denom = int(f) * (10_000 - int(impact_bps))
    if denom <= 0:
        return None
    num = int(reserve_in) * int(impact_bps) * 10_000
    if num <= 0:
        return None
    return max(1, num // denom)


def _push_unique_candidate(
    candidates: list[int],
    seen: set[int],
    *,
    amount_in: int,
    candidate: int,
) -> None:
    if candidate < 1 or candidate > int(amount_in):
        return
    if candidate in seen:
        return
    seen.add(int(candidate))
    candidates.append(int(candidate))


def _append_guess_window(
    candidates: list[int],
    seen: set[int],
    *,
    amount_in: int,
    guess: int | None,
) -> None:
    if guess is None:
        return
    for delta in range(12, -13, -1):
        _push_unique_candidate(
            candidates,
            seen,
            amount_in=amount_in,
            candidate=int(guess + delta),
        )


def _candidate_amount_schedule(
    *,
    reserve_in: int,
    fee_bps: int,
    amount_in: int,
    baseline_reasons: tuple[str, ...],
) -> list[int]:
    """Build the deterministic probe schedule used by the suggestion search."""
    seen: set[int] = set()
    candidates: list[int] = []

    base_has_high_impact = "high_price_impact" in baseline_reasons
    base_has_moderate_impact = "moderate_price_impact" in baseline_reasons

    if base_has_high_impact:
        _append_guess_window(
            candidates,
            seen,
            amount_in=amount_in,
            guess=_impact_guess_amount_in(reserve_in=reserve_in, fee_bps=fee_bps, impact_bps=500),
        )

    if base_has_moderate_impact and not base_has_high_impact:
        _append_guess_window(
            candidates,
            seen,
            amount_in=amount_in,
            guess=_impact_guess_amount_in(reserve_in=reserve_in, fee_bps=fee_bps, impact_bps=100),
        )

    if base_has_high_impact or base_has_moderate_impact:
        fracs = _IMPACT_REDUCTION_FRACS
    else:
        fracs = _GENERIC_REDUCTION_FRACS
    for num, den in fracs:
        _push_unique_candidate(
            candidates,
            seen,
            amount_in=amount_in,
            candidate=int(max(1, (int(amount_in) * int(num)) // int(den))),
        )

    for candidate in (1, 2, 5, 10):
        _push_unique_candidate(candidates, seen, amount_in=amount_in, candidate=int(candidate))

    return candidates


def _find_suggested_candidate(
    *,
    eval_params: _EvalParams,
    candidates: list[int],
    amount_in: int,
    max_evals: int,
    target_sev: int,
) -> tuple[int | None, str | None, tuple[str, ...] | None, int]:
    eval_count = 1
    for cand in candidates:
        if cand == int(amount_in):
            continue
        if eval_count >= int(max_evals):
            break
        eval_count += 1
        try:
            _, decision = eval_params.eval_amount(int(cand))
        except (TypeError, ValueError, OverflowError):
            continue
        if _action_severity(str(decision.action)) <= target_sev:
            return (
                int(cand),
                str(decision.action),
                tuple(decision.reasons),
                int(eval_count),
            )
    return None, None, None, int(eval_count)


def _build_search_params(
    *,
    eval_params: _EvalParams,
    amount_in: int,
    max_evals: int,
) -> _SearchParams:
    # Baseline evaluation counts toward the search budget.
    _, base_decision = eval_params.eval_amount(amount_in)
    baseline_action = str(base_decision.action)
    baseline_reasons = tuple(base_decision.reasons)
    candidates = _candidate_amount_schedule(
        reserve_in=eval_params.reserve_in,
        fee_bps=eval_params.fee_bps,
        amount_in=amount_in,
        baseline_reasons=baseline_reasons,
    )
    return _SearchParams(
        eval_params=eval_params,
        candidates=candidates,
        amount_in=amount_in,
        max_evals=max_evals,
        baseline_action=baseline_action,
        baseline_reasons=baseline_reasons,
    )


def _already_satisfied_suggestion(
    *,
    target_action: str,
    amount_in: int,
    baseline_action: str,
    baseline_reasons: tuple[str, ...],
) -> SwapAmountSuggestion:
    return SwapAmountSuggestion(
        target_action=str(target_action),
        suggested_amount_in=int(amount_in),
        status="ok",
        eval_count=1,
        baseline_action=baseline_action,
        suggested_action=baseline_action,
        baseline_reasons=baseline_reasons,
        suggested_reasons=baseline_reasons,
    )


def _suggest_for_target(
    *,
    target_action: str,
    search_params: _SearchParams,
) -> SwapAmountSuggestion:
    target_sev = _action_severity(str(target_action))
    if _action_severity(search_params.baseline_action) <= target_sev:
        return _already_satisfied_suggestion(
            target_action=str(target_action),
            amount_in=search_params.amount_in,
            baseline_action=search_params.baseline_action,
            baseline_reasons=search_params.baseline_reasons,
        )
    return _search_suggestion_for_target(
        target_action=str(target_action),
        target_sev=target_sev,
        search_params=search_params,
    )


def _search_suggestion_for_target(
    *,
    target_action: str,
    target_sev: int,
    search_params: _SearchParams,
) -> SwapAmountSuggestion:
    suggested_amount, suggested_action, suggested_reasons, eval_count = _find_suggested_candidate(
        eval_params=search_params.eval_params,
        candidates=search_params.candidates,
        amount_in=search_params.amount_in,
        max_evals=search_params.max_evals,
        target_sev=target_sev,
    )
    return SwapAmountSuggestion(
        target_action=str(target_action),
        suggested_amount_in=suggested_amount,
        status="ok" if suggested_amount is not None else "not_found",
        eval_count=int(eval_count),
        baseline_action=search_params.baseline_action,
        suggested_action=suggested_action,
        baseline_reasons=search_params.baseline_reasons,
        suggested_reasons=suggested_reasons,
    )


def suggest_amount_in_exact_in_cpmm(
    *,
    reserve_in: int,
    reserve_out: int,
    fee_bps: int,
    amount_in: int,
    pending_volume_same_direction: int = 0,
    confidence_bps: int = 9500,
    slippage_options_bps: list[int] | None = None,
    max_attacker_amount_in: int = 2_000,
    user_slippage_bps: int,
    max_evals: int = 12,
    target_actions: tuple[str, ...] = ("confirm", "allow"),
) -> list[SwapAmountSuggestion]:
    """Suggest smaller amount_in values for each target action.

    Search strategy (deterministic, budgeted):
    - Evaluate a fixed geometric reduction schedule (descending amounts).
    - Return the first amount that achieves severity <= target severity.

    Rationale:
    - The full guardrail decision is not guaranteed monotone in amount_in due to
      integer rounding and bounded MEV status. We therefore avoid binary search.
    """
    if not isinstance(max_evals, int) or isinstance(max_evals, bool):
        raise TypeError("max_evals must be int")
    if max_evals <= 0:
        raise ValueError("max_evals must be positive")
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")

    eval_params = _EvalParams(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        fee_bps=fee_bps,
        pending_volume_same_direction=pending_volume_same_direction,
        confidence_bps=confidence_bps,
        slippage_options_bps=slippage_options_bps,
        max_attacker_amount_in=max_attacker_amount_in,
        user_slippage_bps=user_slippage_bps,
    )
    search_params = _build_search_params(
        eval_params=eval_params,
        amount_in=amount_in,
        max_evals=max_evals,
    )
    return [
        _suggest_for_target(
            target_action=str(target_action),
            search_params=search_params,
        )
        for target_action in target_actions
    ]
