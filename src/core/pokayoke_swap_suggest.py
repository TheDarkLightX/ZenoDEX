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

    # Baseline evaluation (counts toward budget).
    _, base_decision = _eval_amount(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        fee_bps=fee_bps,
        amount_in=amount_in,
        pending_volume_same_direction=pending_volume_same_direction,
        confidence_bps=confidence_bps,
        slippage_options_bps=slippage_options_bps,
        max_attacker_amount_in=max_attacker_amount_in,
        user_slippage_bps=user_slippage_bps,
    )
    baseline_action = str(base_decision.action)
    baseline_reasons = tuple(base_decision.reasons)

    def _impact_guess_amount_in(*, impact_bps: int) -> int | None:
        """Continuous CPMM impact inversion guess (analysis-only heuristic).

        For fee_rate = fee_bps/10_000 and net_in ~= amount_in*(1-fee_rate):
          impact ~= net_in / (reserve_in + net_in)

        Solve for amount_in at target impact (bps):
          amount_in ~= reserve_in * impact_bps * 10_000 / ((10_000-fee_bps) * (10_000-impact_bps))
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

    # Build a deterministic probe schedule without assuming monotonicity.
    #
    # We prioritize candidates likely to cross the policy thresholds:
    # - high_price_impact: probe near the continuous 5% (500 bps) impact inversion guess
    # - moderate_price_impact: probe near the 1% (100 bps) guess
    # Then fall back to a coarse geometric ladder.
    seen: set[int] = set()
    candidates: list[int] = []

    def _push(a: int) -> None:
        if a < 1 or a > int(amount_in):
            return
        if a in seen:
            return
        seen.add(int(a))
        candidates.append(int(a))

    base_has_high_impact = "high_price_impact" in baseline_reasons
    base_has_moderate_impact = "moderate_price_impact" in baseline_reasons

    if base_has_high_impact:
        g = _impact_guess_amount_in(impact_bps=500)
        if g is not None:
            for delta in range(12, -13, -1):
                _push(int(g + delta))

    if base_has_moderate_impact and not base_has_high_impact:
        g = _impact_guess_amount_in(impact_bps=100)
        if g is not None:
            for delta in range(12, -13, -1):
                _push(int(g + delta))

    # Generic ladder: rapid reductions to find a safe-ish regime.
    # If we already probed near an impact threshold guess, skip obviously-too-large fractions.
    fracs: tuple[tuple[int, int], ...]
    if base_has_high_impact or base_has_moderate_impact:
        fracs = (
            (1, 4),   # 0.25
            (1, 5),   # 0.2
            (3, 20),  # 0.15
            (1, 10),  # 0.1
            (3, 40),  # 0.075
            (1, 20),  # 0.05
            (1, 25),  # 0.04
            (3, 100), # 0.03
            (1, 40),  # 0.025
            (1, 50),  # 0.02
            (3, 200), # 0.015
            (1, 100), # 0.01
        )
    else:
        fracs = (
            (1, 2),   # 0.5
            (1, 3),   # ~0.33
            (1, 4),   # 0.25
            (1, 5),   # 0.2
            (3, 20),  # 0.15
            (1, 10),  # 0.1
            (3, 40),  # 0.075
            (1, 20),  # 0.05
            (1, 25),  # 0.04
            (3, 100), # 0.03
            (1, 40),  # 0.025
            (1, 50),  # 0.02
            (3, 200), # 0.015
            (1, 100), # 0.01
        )
    for num, den in fracs:
        _push(int(max(1, (int(amount_in) * int(num)) // int(den))))

    # Always keep a tiny absolute fallback.
    for a in (1, 2, 5, 10):
        _push(int(a))

    out: list[SwapAmountSuggestion] = []
    for target_action in target_actions:
        target_sev = _action_severity(str(target_action))
        if _action_severity(baseline_action) <= target_sev:
            out.append(
                SwapAmountSuggestion(
                    target_action=str(target_action),
                    suggested_amount_in=int(amount_in),
                    status="ok",
                    eval_count=1,
                    baseline_action=baseline_action,
                    suggested_action=baseline_action,
                    baseline_reasons=baseline_reasons,
                    suggested_reasons=baseline_reasons,
                )
            )
            continue

        eval_count = 1
        suggested_amount: int | None = None
        suggested_action: str | None = None
        suggested_reasons: tuple[str, ...] | None = None

        # Skip the baseline amount (already evaluated). Evaluate candidates in descending order
        # so the first success is the largest among our deterministic probe set.
        for cand in candidates:
            if cand == int(amount_in):
                continue
            if eval_count >= int(max_evals):
                break
            eval_count += 1
            try:
                _, d = _eval_amount(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    fee_bps=fee_bps,
                    amount_in=int(cand),
                    pending_volume_same_direction=pending_volume_same_direction,
                    confidence_bps=confidence_bps,
                    slippage_options_bps=slippage_options_bps,
                    max_attacker_amount_in=max_attacker_amount_in,
                    user_slippage_bps=user_slippage_bps,
                )
            except (TypeError, ValueError, OverflowError):
                continue
            if _action_severity(str(d.action)) <= target_sev:
                suggested_amount = int(cand)
                suggested_action = str(d.action)
                suggested_reasons = tuple(d.reasons)
                break

        out.append(
            SwapAmountSuggestion(
                target_action=str(target_action),
                suggested_amount_in=suggested_amount,
                status="ok" if suggested_amount is not None else "not_found",
                eval_count=int(eval_count),
                baseline_action=baseline_action,
                suggested_action=suggested_action,
                baseline_reasons=baseline_reasons,
                suggested_reasons=suggested_reasons,
            )
        )

    return out
