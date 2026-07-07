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

from .zeno_ux_certificate import (
    CERT_SCHEMA,
    MINIMAX_REGRET_POLICY_SCHEMA,
    ZenoUXCertificate,
    ZenoUXMinimaxRegretCertificate,
    ZenoUXMinimaxRegretPolicy,
    build_zeno_ux_minimax_regret_certificate,
    choose_minimax_regret_zeno_ux_certificate,
)


_SWAP_PROOFUX_POLICY_ID = "swap_execution_minimax_v1"
_SWAP_PROOFUX_SURFACE = "swap_execution"
_SWAP_PROOFUX_SCENARIO = "pokayoke_exact_in"
_SWAP_PROOFUX_EVIDENCE_REF = "runtime:pokayoke_swap_guardrails"
_ACTION_COGNITIVE_STEPS: dict[str, int] = {
    "allow": 0,
    "confirm": 1,
    "typed_confirm": 2,
    "block": 3,
    "wait_or_requote": 1,
}
_ACTION_LATENCY_MS: dict[str, int] = {
    "allow": 0,
    "confirm": 2_000,
    "typed_confirm": 10_000,
    "block": 0,
    "wait_or_requote": 30_000,
}


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


@dataclass(frozen=True)
class SwapProofUXDecision:
    selected_action: str
    legacy_action: str
    regret_within_limit_ok: bool
    inaction_regret_bps: int
    candidate_ids: tuple[str, ...]
    minimax_certificate: ZenoUXMinimaxRegretCertificate


@dataclass
class _GuardrailNotes:
    reasons: list[str]
    messages: list[str]


def _validate_bps(name: str, v: int) -> int:
    if not isinstance(v, int) or isinstance(v, bool):
        raise TypeError(f"{name} must be int")
    if v < 0 or v > 10_000:
        raise ValueError(f"{name} must be in [0, 10_000]")
    return int(v)


def _validate_optional_bps(name: str, v: int | None) -> int | None:
    if v is None:
        return None
    return _validate_bps(name, v)


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


def _append_status_reasons(status: str, notes: _GuardrailNotes) -> None:
    if status == "mev_conflict":
        notes.reasons.append("mev_conflict")
        notes.messages.append(
            "MEV/revert conflict: revert-safe slippage appears sandwich-profitable under the bounded model."
        )
    elif status == "inconclusive_mev":
        notes.reasons.append("inconclusive_mev")
        notes.messages.append("MEV risk is inconclusive under the scan cap. Treat as unknown (fail-closed).")
    elif status == "no_revert_safe_option":
        notes.reasons.append("no_revert_safe_option")
        notes.messages.append("No provided slippage option is revert-safe at the confidence bound; the swap may revert.")
    elif status != "ok":
        notes.reasons.append(f"status_{status}")
        notes.messages.append(f"Slippage advisor returned status={status}.")


def _append_price_impact_reasons(impact_bps: int, notes: _GuardrailNotes) -> None:
    if impact_bps >= 500:
        notes.reasons.append("high_price_impact")
        notes.messages.append(f"High price impact: {_bps_to_percent_str(impact_bps)}. Consider trading a smaller amount.")
    elif impact_bps >= 100:
        notes.reasons.append("moderate_price_impact")
        notes.messages.append(f"Moderate price impact: {_bps_to_percent_str(impact_bps)}.")


def _append_revert_safe_reasons(
    *,
    ctx: SwapGuardrailContext,
    user_slippage_bps: int,
    required_slippage_bps: int,
    notes: _GuardrailNotes,
) -> None:
    rec_revert = ctx.recommended_slippage_bps_revert_safe
    if rec_revert is None:
        if required_slippage_bps > 0:
            notes.messages.append(f"Required slippage at confidence (ceil): {_bps_to_percent_str(required_slippage_bps)}.")
        return

    _validate_bps("recommended_slippage_bps_revert_safe", int(rec_revert))
    if user_slippage_bps < int(rec_revert):
        notes.reasons.append("slippage_below_revert_safe")
        notes.messages.append(
            f"Your slippage ({_bps_to_percent_str(user_slippage_bps)}) is below the smallest revert-safe option ({_bps_to_percent_str(int(rec_revert))}) at the confidence bound."
        )


def _append_mev_safe_reasons(
    *,
    ctx: SwapGuardrailContext,
    user_slippage_bps: int,
    notes: _GuardrailNotes,
) -> None:
    rec_mev = ctx.recommended_slippage_bps_mev_safe
    if rec_mev is None:
        return

    _validate_bps("recommended_slippage_bps_mev_safe", int(rec_mev))
    if user_slippage_bps > int(rec_mev):
        notes.reasons.append("slippage_above_mev_safe")
        notes.messages.append(
            f"Your slippage ({_bps_to_percent_str(user_slippage_bps)}) is above the MEV-safe ceiling ({_bps_to_percent_str(int(rec_mev))}) for the bounded model."
        )


def _guardrail_action_for_reasons(reasons: list[str]) -> tuple[str, str | None]:
    typed_triggers = {"mev_conflict", "no_revert_safe_option", "high_price_impact", "slippage_below_revert_safe"}
    confirm_triggers = {"inconclusive_mev", "moderate_price_impact", "slippage_above_mev_safe"}

    if any(r in typed_triggers for r in reasons):
        return "typed_confirm", "PROCEED"
    if any(r in confirm_triggers for r in reasons) or any(r.startswith("status_") for r in reasons):
        return "confirm", None
    return "allow", None


def default_swap_proofux_minimax_policy(
    *,
    max_value_loss_bps: int | None = None,
    max_mev_exposure_bps: int | None = None,
    max_capital_at_risk_bps: int | None = None,
) -> ZenoUXMinimaxRegretPolicy:
    budgets: list[tuple[str, int]] = []
    value_budget = _validate_optional_bps("max_value_loss_bps", max_value_loss_bps)
    mev_budget = _validate_optional_bps("max_mev_exposure_bps", max_mev_exposure_bps)
    capital_budget = _validate_optional_bps(
        "max_capital_at_risk_bps",
        max_capital_at_risk_bps,
    )
    if value_budget is not None:
        budgets.append(("value_loss_bound_bps", value_budget))
    if mev_budget is not None:
        budgets.append(("mev_exposure_bound_bps", mev_budget))
    if capital_budget is not None:
        budgets.append(("capital_at_risk_bps", capital_budget))
    return ZenoUXMinimaxRegretPolicy(
        schema=MINIMAX_REGRET_POLICY_SCHEMA,
        policy_id=_SWAP_PROOFUX_POLICY_ID,
        safety_axes=(
            "value_loss_bound_bps",
            "mev_exposure_bound_bps",
            "capital_at_risk_bps",
        ),
        safety_budgets=tuple(budgets),
        friction_weights={
            "cognitive_steps": 250,
            "latency_bound_ms": 1,
        },
        max_safety_regret=0,
        max_friction_score=0,
    )


def _action_cognitive_steps(action: str) -> int:
    return _ACTION_COGNITIVE_STEPS.get(str(action), 9)


def _action_latency_ms(action: str) -> int:
    return _ACTION_LATENCY_MS.get(str(action), 30_000)


def _execution_mev_exposure_bps(
    *,
    ctx: SwapGuardrailContext,
    user_slippage_bps: int,
    reasons: tuple[str, ...],
) -> int:
    rec_mev = ctx.recommended_slippage_bps_mev_safe
    if rec_mev is not None:
        safe = _validate_bps("recommended_slippage_bps_mev_safe", int(rec_mev))
        return max(0, int(user_slippage_bps) - safe)
    if "mev_conflict" in reasons or "inconclusive_mev" in reasons:
        return 10_000
    return 0


def _execution_value_loss_bps(
    *,
    ctx: SwapGuardrailContext,
    user_slippage_bps: int,
) -> int:
    required_gap = max(0, int(ctx.required_slippage_bps) - int(user_slippage_bps))
    return max(int(ctx.price_impact_bps), required_gap)


def _execution_capital_at_risk_bps(reasons: tuple[str, ...]) -> int:
    if "no_revert_safe_option" in reasons:
        return 10_000
    return 0


def _proofux_certificate(
    *,
    certificate_id: str,
    next_action: str,
    decision_class: str,
    latency_bound_ms: int,
    value_loss_bound_bps: int,
    mev_exposure_bound_bps: int,
    capital_at_risk_bps: int,
    cognitive_steps: int,
    explanation_code: str,
    evidence_refs: tuple[str, ...],
) -> ZenoUXCertificate:
    return ZenoUXCertificate(
        schema=CERT_SCHEMA,
        certificate_id=certificate_id,
        surface=_SWAP_PROOFUX_SURFACE,
        scenario_id=_SWAP_PROOFUX_SCENARIO,
        decision_class=decision_class,
        latency_bound_ms=int(latency_bound_ms),
        value_loss_bound_bps=value_loss_bound_bps,
        mev_exposure_bound_bps=mev_exposure_bound_bps,
        finality_bound_blocks=0,
        capital_at_risk_bps=capital_at_risk_bps,
        privacy_leakage_bits=0,
        cognitive_steps=int(cognitive_steps),
        explanation_code=explanation_code,
        next_action=next_action,
        evidence_refs=evidence_refs,
    )


def build_swap_proofux_regret_decision(
    *,
    ctx: SwapGuardrailContext,
    user_slippage_bps: int,
    inaction_regret_bps: int = 0,
    policy: ZenoUXMinimaxRegretPolicy | None = None,
) -> SwapProofUXDecision:
    """Compare current execution against wait/requote using ProofUX minimax regret.

    This is UX-only. It does not mutate swap state or authorize settlement.
    """
    user_slip = _validate_bps("user_slippage_bps", user_slippage_bps)
    inaction = _validate_bps("inaction_regret_bps", inaction_regret_bps)
    legacy = decide_swap_guardrails(ctx=ctx, user_slippage_bps=user_slip)
    reasons = tuple(legacy.reasons)
    execution = _proofux_certificate(
        certificate_id=f"execute_{legacy.action}",
        next_action=str(legacy.action),
        decision_class="certified_approx",
        latency_bound_ms=_action_latency_ms(legacy.action),
        value_loss_bound_bps=_execution_value_loss_bps(
            ctx=ctx,
            user_slippage_bps=user_slip,
        ),
        mev_exposure_bound_bps=_execution_mev_exposure_bps(
            ctx=ctx,
            user_slippage_bps=user_slip,
            reasons=reasons,
        ),
        capital_at_risk_bps=_execution_capital_at_risk_bps(reasons),
        cognitive_steps=_action_cognitive_steps(legacy.action),
        explanation_code="swap_execute_current",
        evidence_refs=(_SWAP_PROOFUX_EVIDENCE_REF,),
    )
    wait = _proofux_certificate(
        certificate_id="wait_or_requote",
        next_action="wait_or_requote",
        decision_class="deferred",
        latency_bound_ms=_action_latency_ms("wait_or_requote"),
        value_loss_bound_bps=inaction,
        mev_exposure_bound_bps=0,
        capital_at_risk_bps=0,
        cognitive_steps=_action_cognitive_steps("wait_or_requote"),
        explanation_code="swap_wait_or_requote",
        evidence_refs=(),
    )
    candidates = (execution, wait)
    active_policy = policy or default_swap_proofux_minimax_policy()
    selected = choose_minimax_regret_zeno_ux_certificate(
        candidates,
        policy=active_policy,
    )
    certificate = build_zeno_ux_minimax_regret_certificate(
        candidates,
        chosen_certificate_id=execution.certificate_id,
        policy=active_policy,
        evidence_refs=(_SWAP_PROOFUX_EVIDENCE_REF,),
    )
    return SwapProofUXDecision(
        selected_action=str(selected.next_action),
        legacy_action=str(legacy.action),
        regret_within_limit_ok=bool(certificate.regret_ok),
        inaction_regret_bps=inaction,
        candidate_ids=tuple(candidate.certificate_id for candidate in candidates),
        minimax_certificate=certificate,
    )


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

    notes = _GuardrailNotes(reasons=[], messages=[])

    _append_status_reasons(st, notes)
    _append_price_impact_reasons(impact, notes)
    _append_revert_safe_reasons(
        ctx=ctx,
        user_slippage_bps=user_slip,
        required_slippage_bps=required,
        notes=notes,
    )
    _append_mev_safe_reasons(ctx=ctx, user_slippage_bps=user_slip, notes=notes)
    action, typed_phrase = _guardrail_action_for_reasons(notes.reasons)

    return SwapGuardrailDecision(
        action=str(action),
        reasons=tuple(notes.reasons),
        messages=tuple(notes.messages),
        typed_confirm_phrase=typed_phrase,
    )
