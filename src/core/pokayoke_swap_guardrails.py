"""Poka-yoke swap guardrails (UX-only, deterministic).

This module is an *experiment* layer: it does not change swap semantics.
It turns existing deterministic signals (price impact preview + slippage advice)
into a small, explainable interlock decision for UIs and deterministic agents.

Design posture:
- deterministic integer-only inputs (bps)
- explicit fail-closed handling for unknown statuses
- policy is intentionally simple and tiered; refine via evidence (counterexamples + BVA)
"""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class SwapGuardrailContext:
    # Deterministic risk signals (all in bps).
    price_impact_bps: int

    slippage_advice_status: str  # "ok" | "mev_conflict" | "inconclusive_mev" | "no_revert_safe_option" | other
    required_slippage_bps: int

    recommended_slippage_bps_revert_safe: int | None
    recommended_slippage_bps_mev_safe: int | None
    recommended_slippage_bps: int | None


@dataclass(frozen=True)
class SwapGuardrailDecision:
    # Interlock action for the UI/agent.
    action: str  # "allow" | "confirm" | "typed_confirm" | "block"

    # Deterministic reason codes (stable API surface).
    reasons: tuple[str, ...]

    # Human-facing messages (best-effort; not consensus-critical).
    messages: tuple[str, ...]

    # When action == typed_confirm, require the user to type this phrase.
    typed_confirm_phrase: str | None


def _validate_bps(name: str, v: int) -> int:
    if not isinstance(v, int) or isinstance(v, bool):
        raise TypeError(f"{name} must be int")
    if v < 0 or v > 10_000:
        raise ValueError(f"{name} must be in [0, 10_000]")
    return int(v)


def _bps_to_percent_str(bps: int) -> str:
    """
    Format a bps value as a percentage string without using floats.

    Examples:
      0 -> "0.00%"
      100 -> "1.00%"
      1234 -> "12.34%"
      10_000 -> "100.00%"
    """
    whole = int(bps) // 100
    frac = int(bps) % 100
    return f"{whole}.{frac:02d}%"


def decide_swap_guardrails(
    *,
    ctx: SwapGuardrailContext,
    user_slippage_bps: int,
) -> SwapGuardrailDecision:
    """Decide a UX interlock tier from deterministic signals.

    Policy v1:
    - Always fail-closed on MEV conflict and no-revert-safe: require typed confirm.
    - Inconclusive MEV: require confirm (unknown is not treated as safe).
    - Price impact tiers: confirm at >= 1%, typed confirm at >= 5%.
    - User slippage below revert-safe recommendation: typed confirm.
    - User slippage above MEV-safe ceiling (when known): confirm.
    """
    user_slip = _validate_bps("user_slippage_bps", user_slippage_bps)
    impact = _validate_bps("price_impact_bps", ctx.price_impact_bps)
    required = _validate_bps("required_slippage_bps", ctx.required_slippage_bps)

    st = str(ctx.slippage_advice_status or "").strip() or "unknown"

    reasons: list[str] = []
    messages: list[str] = []

    # Status-driven gating (fail-closed posture).
    if st == "mev_conflict":
        reasons.append("mev_conflict")
        messages.append("MEV/revert conflict: revert-safe slippage appears sandwich-profitable under the bounded model.")
    elif st == "inconclusive_mev":
        reasons.append("inconclusive_mev")
        messages.append("MEV risk is inconclusive under the scan cap. Treat as unknown (fail-closed).")
    elif st == "no_revert_safe_option":
        reasons.append("no_revert_safe_option")
        messages.append("No provided slippage option is revert-safe at the confidence bound; the swap may revert.")
    elif st != "ok":
        reasons.append(f"status_{st}")
        messages.append(f"Slippage advisor returned status={st}.")

    # Price impact tiers (1% -> confirm, 5% -> typed confirm).
    if impact >= 500:
        reasons.append("high_price_impact")
        messages.append(f"High price impact: {_bps_to_percent_str(impact)}. Consider trading a smaller amount.")
    elif impact >= 100:
        reasons.append("moderate_price_impact")
        messages.append(f"Moderate price impact: {_bps_to_percent_str(impact)}.")

    # User setting vs revert-safe requirement.
    rec_revert = ctx.recommended_slippage_bps_revert_safe
    if rec_revert is not None:
        _validate_bps("recommended_slippage_bps_revert_safe", int(rec_revert))
        if user_slip < int(rec_revert):
            reasons.append("slippage_below_revert_safe")
            messages.append(
                f"Your slippage ({_bps_to_percent_str(user_slip)}) is below the smallest revert-safe option ({_bps_to_percent_str(int(rec_revert))}) at the confidence bound."
            )
    else:
        # If we couldn't find a revert-safe option, make the required slippage visible.
        if required > 0:
            messages.append(f"Required slippage at confidence (ceil): {_bps_to_percent_str(required)}.")

    rec_mev = ctx.recommended_slippage_bps_mev_safe
    if rec_mev is not None:
        _validate_bps("recommended_slippage_bps_mev_safe", int(rec_mev))
        if user_slip > int(rec_mev):
            reasons.append("slippage_above_mev_safe")
            messages.append(
                f"Your slippage ({_bps_to_percent_str(user_slip)}) is above the MEV-safe ceiling ({_bps_to_percent_str(int(rec_mev))}) for the bounded model."
            )

    # Decision tiering.
    action = "allow"
    typed_phrase: str | None = None

    # Hard blocks: reserve for true impossibilities (none in v1; keep experimental).
    # if ...:
    #   action = "block"

    typed_triggers = {"mev_conflict", "no_revert_safe_option", "high_price_impact", "slippage_below_revert_safe"}
    confirm_triggers = {"inconclusive_mev", "moderate_price_impact", "slippage_above_mev_safe"}

    if any(r in typed_triggers for r in reasons):
        action = "typed_confirm"
        typed_phrase = "PROCEED"
    elif any(r in confirm_triggers for r in reasons) or any(r.startswith("status_") for r in reasons):
        action = "confirm"

    return SwapGuardrailDecision(
        action=str(action),
        reasons=tuple(reasons),
        messages=tuple(messages),
        typed_confirm_phrase=typed_phrase,
    )
