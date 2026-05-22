"""Bounded conversational advisor for AutoTrader strategies.

The advisor is a hybrid interface:

* a tiny bounded language bridge maps a user sentence into advisory features;
* an EBRM control search proposes lower-tension counterfactual parameters;
* local AutoTrader guards decide whether the proposal is policy-valid;
* KRR advice explains which checks matter for the current strategy surface.

The module deliberately does not execute trades, sign intents, mutate ledger
state, or authorize settlement. It produces a candidate explanation packet.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Literal, Mapping, Sequence

from ..energy.autotrader_energy import (
    AUTOTRADER_FEATURE_NAMES,
    autotrader_candidate_row_from_features,
    autotrader_feature_map,
    autotrader_label_from_features,
    hand_energy_from_autotrader_row,
)
from ..energy.autotrader_ux import build_autotrader_advisory_card
from ..energy.zeno_jepa import (
    AUTOTRADER_CONTROL_IDS,
    apply_autotrader_control,
    score_autotrader_future_tension,
)
from ..integration.autotrader_signals import (
    AutoTraderObservationPacket,
    build_autotrader_observation_packet,
)
from .autotrader_local_guard_evaluator import (
    AutoTraderLocalGuardEvaluation,
    AutoTraderLocalGuardInputs,
    evaluate_autotrader_local_guards,
)
from .autotrader_llm_provider import (
    AutoTraderLanguageProvider,
    AutoTraderLanguageProviderResult,
)
from .krr_policy_advisor import AutoTraderKRRPhase, advise_autotrader_krr
from .strategy_ir import StrategyIR

AUTOTRADER_CHATBOT_ADVISOR_SCHEMA = "zenodex/agents/autotrader_chatbot_advisor/v1"
AUTOTRADER_CHATBOT_LANGUAGE_SCHEMA = "zenodex/agents/autotrader_chat_language_bridge/v1"
AUTOTRADER_CHATBOT_REFINEMENT_SCHEMA = "zenodex/agents/autotrader_chat_ebrm_refinement/v1"

SecurityStatus = Literal["clean", "blocked_by_security_policy"]
AdvisorStatus = Literal[
    "blocked_by_security_policy",
    "blocked_by_policy_guard",
    "needs_risk_review",
    "policy_valid_with_caution",
    "policy_valid_candidate",
]

_SECURITY_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "ignore_previous_instructions",
        re.compile(r"\bignore\b.{0,48}\b(previous|system|developer|instructions?)\b"),
    ),
    (
        "bypass_policy_guard",
        re.compile(r"\b(bypass|override|disable|skip|turn\s+off)\b.{0,56}\b(guard|policy|safety|limit|checker|control)s?\b"),
    ),
    (
        "execute_without_guard",
        re.compile(r"\bexecute\b.{0,80}\b(without|regardless|no)\b.{0,40}\b(guard|limit|check|policy)s?\b"),
    ),
    ("emergency_dump_all", re.compile(r"\bemergency[_\s-]*dump[_\s-]*all\b|\bdump\s+all\b")),
    ("secret_exfiltration", re.compile(r"\b(private\s+key|seed\s+phrase|system\s+prompt|developer\s+message)\b")),
    ("jailbreak_mode", re.compile(r"\b(jailbreak|developer\s+mode|god\s+mode)\b")),
)


@dataclass(frozen=True)
class AutoTraderChatbotConfig:
    """Runtime bounds for the local language bridge and EBRM refiner."""

    max_prompt_chars: int = 2_048
    max_token_estimate: int = 512
    refinement_steps: int = 5
    order_amount_scale: float = 2.0
    krr_backend: str = "python"

    def __post_init__(self) -> None:
        if self.max_prompt_chars <= 0:
            raise ValueError("max_prompt_chars must be positive")
        if self.max_token_estimate <= 0:
            raise ValueError("max_token_estimate must be positive")
        if self.refinement_steps < 0:
            raise ValueError("refinement_steps must be nonnegative")
        if self.order_amount_scale <= 0.0:
            raise ValueError("order_amount_scale must be positive")
        if not isinstance(self.krr_backend, str) or not self.krr_backend:
            raise ValueError("krr_backend must be non-empty")


@dataclass(frozen=True)
class _LanguageParse:
    raw_query: str
    normalized_query: str
    prompt_chars: int
    token_estimate: int
    within_budget: bool
    security_status: SecurityStatus
    security_flags: tuple[str, ...]
    intent_tags: tuple[str, ...]
    requested_controls: tuple[str, ...]
    features: dict[str, float]
    provider: str = "bounded_local_language_bridge"
    llm_calls: int = 0
    provider_local_only: bool = True
    provider_model: str | None = None
    provider_schema_valid: bool = True
    provider_error: str | None = None
    provider_fallback_used: bool = False
    provider_explanation: str = ""
    raw_response_chars: int = 0

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": AUTOTRADER_CHATBOT_LANGUAGE_SCHEMA,
            "provider": self.provider,
            "llm_calls": self.llm_calls,
            "provider_local_only": self.provider_local_only,
            "provider_model": self.provider_model,
            "provider_schema_valid": self.provider_schema_valid,
            "provider_error": self.provider_error,
            "provider_fallback_used": self.provider_fallback_used,
            "provider_explanation": self.provider_explanation,
            "raw_response_chars": self.raw_response_chars,
            "llm_authorizes_trade": False,
            "raw_prompt_chars": self.prompt_chars,
            "token_estimate": self.token_estimate,
            "within_budget": self.within_budget,
            "security_status": self.security_status,
            "security_flags": list(self.security_flags),
            "intent_tags": list(self.intent_tags),
            "requested_controls": list(self.requested_controls),
            "parsed_features": dict(self.features),
        }


class ZenoAutoTraderChatbotAdvisor:
    """High-assurance conversational advisor for AutoTrader proposals."""

    def __init__(
        self,
        config: AutoTraderChatbotConfig | None = None,
        *,
        language_provider: AutoTraderLanguageProvider | None = None,
    ) -> None:
        self.config = config or AutoTraderChatbotConfig()
        self.language_provider = language_provider

    def handle_user_query(
        self,
        query: str,
        *,
        strategy: StrategyIR,
        guard_inputs: AutoTraderLocalGuardInputs,
        initial_features: Mapping[str, float] | Sequence[float] | None = None,
        phase: AutoTraderKRRPhase = "shadow",
        observation_packet: AutoTraderObservationPacket | None = None,
        history_check_stats: Mapping[str, object] | None = None,
        quote_receipt: Mapping[str, Any] | None = None,
        pools_by_id: Mapping[str, Any] | None = None,
    ) -> dict[str, Any]:
        """Return one advisory packet for a user query and strategy state."""

        if not isinstance(strategy, StrategyIR):
            raise TypeError("strategy must be a StrategyIR")
        if not isinstance(guard_inputs, AutoTraderLocalGuardInputs):
            raise TypeError("guard_inputs must be AutoTraderLocalGuardInputs")
        base_features = (
            _features_from_guard_inputs(strategy=strategy, inputs=guard_inputs)
            if initial_features is None
            else autotrader_feature_map(initial_features)
        )
        parsed = self._parse_language(query, base_features)
        if parsed.security_status == "blocked_by_security_policy":
            return self._security_rejection(parsed)

        refinement = self._refine_features(parsed.features, parsed.requested_controls)
        proposed_inputs = _guard_inputs_from_features(
            strategy=strategy,
            base_inputs=guard_inputs,
            features=refinement["features"],
            order_amount_scale=self.config.order_amount_scale,
        )
        guard_evaluation = evaluate_autotrader_local_guards(
            strategy=strategy,
            inputs=proposed_inputs,
        )
        krr_advice = self._advise_krr(
            strategy=strategy,
            phase=phase,
            inputs=proposed_inputs,
            observation_packet=observation_packet,
            history_check_stats=history_check_stats,
            quote_receipt=quote_receipt,
            pools_by_id=pools_by_id,
        )
        card = build_autotrader_advisory_card(
            refinement["features"],
            candidate_id=f"{strategy.strategy_id}:chatbot-proposal",
        )
        card = _merge_guard_status_into_card(card, guard_evaluation)
        status = _overall_status(card=card, guard_evaluation=guard_evaluation)

        return {
            "schema": AUTOTRADER_CHATBOT_ADVISOR_SCHEMA,
            "status": status,
            "conversation_reply": _conversation_reply(
                status=status,
                guard_evaluation=guard_evaluation,
                card=card,
                krr_advice=krr_advice,
            ),
            "language_bridge": parsed.to_dict(),
            "initial_features": base_features,
            "refined_features": dict(refinement["features"]),
            "refinement": {
                "schema": AUTOTRADER_CHATBOT_REFINEMENT_SCHEMA,
                "method": "bounded_future_tension_control_search",
                "steps_run": len(refinement["trace"]),
                "trace": refinement["trace"],
                "initial_future_tension": refinement["initial_future_tension"],
                "final_future_tension": refinement["final_future_tension"],
                "future_tension_delta": refinement["future_tension_delta"],
                "initial_hand_energy": refinement["initial_hand_energy"],
                "final_hand_energy": refinement["final_hand_energy"],
                "hand_energy_delta": refinement["hand_energy_delta"],
                "ebrm_authorizes_trade": False,
            },
            "proposal_inputs": proposed_inputs.to_dict(),
            "guard_evaluation": guard_evaluation.to_dict(),
            "krr_advice": krr_advice,
            "advisory_card": card,
            "authority": _authority_packet(),
        }

    def _parse_language(
        self,
        query: str,
        base_features: Mapping[str, float],
    ) -> _LanguageParse:
        if not isinstance(query, str):
            raise TypeError("query must be a string")
        prompt_chars = len(query)
        token_estimate = max(1, (prompt_chars + 3) // 4)
        normalized = _normalize_query(query)
        security_flags = list(_security_flags(normalized))
        if prompt_chars > self.config.max_prompt_chars:
            security_flags.append("prompt_char_budget_exceeded")
        if token_estimate > self.config.max_token_estimate:
            security_flags.append("prompt_token_budget_exceeded")
        features = dict(base_features)
        intent_tags: list[str] = []
        requested_controls: list[str] = []
        if not security_flags:
            _apply_language_hints(
                normalized=normalized,
                features=features,
                intent_tags=intent_tags,
                requested_controls=requested_controls,
            )
        provider_result: AutoTraderLanguageProviderResult | None = None
        if not security_flags and self.language_provider is not None:
            provider_result = self.language_provider.parse(
                query=query,
                normalized_query=normalized,
                base_features=features,
                requested_controls=requested_controls,
                intent_tags=intent_tags,
            )
            if provider_result.schema_valid:
                features.update(provider_result.feature_updates)
                intent_tags[:] = list(provider_result.intent_tags)
                requested_controls[:] = list(provider_result.requested_controls)
        return _LanguageParse(
            raw_query=query,
            normalized_query=normalized,
            prompt_chars=prompt_chars,
            token_estimate=token_estimate,
            within_budget=not (
                prompt_chars > self.config.max_prompt_chars
                or token_estimate > self.config.max_token_estimate
            ),
            security_status="blocked_by_security_policy" if security_flags else "clean",
            security_flags=tuple(dict.fromkeys(security_flags)),
            intent_tags=tuple(dict.fromkeys(intent_tags)),
            requested_controls=tuple(
                control
                for control in dict.fromkeys(requested_controls)
                if control in AUTOTRADER_CONTROL_IDS
            ),
            features=autotrader_feature_map(features),
            provider=(
                "bounded_local_language_bridge"
                if provider_result is None
                else provider_result.provider
            ),
            llm_calls=0 if provider_result is None else provider_result.llm_calls,
            provider_local_only=True if provider_result is None else provider_result.local_only,
            provider_model=None if provider_result is None else provider_result.model,
            provider_schema_valid=True if provider_result is None else provider_result.schema_valid,
            provider_error=None if provider_result is None else provider_result.error,
            provider_fallback_used=(
                False
                if provider_result is None
                else provider_result.fallback_provider_used or not provider_result.schema_valid
            ),
            provider_explanation="" if provider_result is None else provider_result.explanation,
            raw_response_chars=0 if provider_result is None else provider_result.raw_response_chars,
        )

    def _refine_features(
        self,
        features: Mapping[str, float],
        requested_controls: Sequence[str],
    ) -> dict[str, Any]:
        current = autotrader_feature_map(features)
        initial_tension = score_autotrader_future_tension(current)
        initial_energy = _hand_energy(current)
        trace: list[dict[str, Any]] = []
        control_order = _control_order(requested_controls)
        for step_index in range(self.config.refinement_steps):
            best_control: str | None = None
            best_features = current
            best_score = _refinement_score(current)
            for control_id in control_order:
                candidate = apply_autotrader_control(current, control_id)
                score = _refinement_score(candidate)
                if score < best_score:
                    best_score = score
                    best_control = control_id
                    best_features = candidate
            if best_control is None:
                break
            before_tension = score_autotrader_future_tension(current)
            after_tension = score_autotrader_future_tension(best_features)
            before_energy = _hand_energy(current)
            after_energy = _hand_energy(best_features)
            trace.append(
                {
                    "step": step_index + 1,
                    "control_id": best_control,
                    "future_tension_before": before_tension,
                    "future_tension_after": after_tension,
                    "future_tension_delta": after_tension - before_tension,
                    "hand_energy_before": before_energy,
                    "hand_energy_after": after_energy,
                    "hand_energy_delta": after_energy - before_energy,
                    "control_authorizes_trade": False,
                }
            )
            current = best_features
        final_tension = score_autotrader_future_tension(current)
        final_energy = _hand_energy(current)
        return {
            "features": current,
            "trace": trace,
            "initial_future_tension": initial_tension,
            "final_future_tension": final_tension,
            "future_tension_delta": final_tension - initial_tension,
            "initial_hand_energy": initial_energy,
            "final_hand_energy": final_energy,
            "hand_energy_delta": final_energy - initial_energy,
        }

    def _advise_krr(
        self,
        *,
        strategy: StrategyIR,
        phase: AutoTraderKRRPhase,
        inputs: AutoTraderLocalGuardInputs,
        observation_packet: AutoTraderObservationPacket | None,
        history_check_stats: Mapping[str, object] | None,
        quote_receipt: Mapping[str, Any] | None,
        pools_by_id: Mapping[str, Any] | None,
    ) -> dict[str, Any]:
        effective_observation_packet = observation_packet
        if effective_observation_packet is None and inputs.signal_packet is not None:
            effective_observation_packet = build_autotrader_observation_packet(
                primary_signal=inputs.signal_packet,
            )
        try:
            advice = advise_autotrader_krr(
                strategy=strategy,
                phase=phase,
                current_epoch=inputs.current_epoch,
                backend=self.config.krr_backend,
                history_check_stats=history_check_stats,
                spent_in_window=inputs.spent_in_window,
                lifetime_spent=inputs.lifetime_spent,
                live_orders=max(0, inputs.projected_live_orders - 1),
                observation_packet=effective_observation_packet,
                quote_receipt=quote_receipt,
                pools_by_id=pools_by_id,  # type: ignore[arg-type]
            )
        except Exception as exc:  # KRR is advisory, so failures are exposed without authorizing.
            return {
                "schema": "zenodex/agents/autotrader_chat_krr_advice/v1",
                "status": "unavailable",
                "error": str(exc),
                "krr_authorizes_trade": False,
            }
        if advice is None:
            return {
                "schema": "zenodex/agents/autotrader_chat_krr_advice/v1",
                "status": "off",
                "krr_authorizes_trade": False,
            }
        return {
            "schema": "zenodex/agents/autotrader_chat_krr_advice/v1",
            "status": "available",
            "phase": advice.get("phase"),
            "confidence": advice.get("confidence"),
            "confidence_cap": advice.get("confidence_cap"),
            "preferred_checks": list(advice.get("preferred_checks", [])),
            "candidate_checks": list(advice.get("candidate_checks", [])),
            "advisory_risk_flags": list(advice.get("advisory_risk_flags", [])),
            "surface_support_summary": advice.get("surface_support_summary"),
            "observation_summary": advice.get("observation_summary"),
            "explain": list(advice.get("explain", [])),
            "krr_authorizes_trade": False,
        }

    def _security_rejection(self, parsed: _LanguageParse) -> dict[str, Any]:
        return {
            "schema": AUTOTRADER_CHATBOT_ADVISOR_SCHEMA,
            "status": "blocked_by_security_policy",
            "conversation_reply": (
                "I blocked this request before advisory refinement because it asked to bypass "
                "or expose protected controls. Rewrite the request as bounded trade preferences."
            ),
            "language_bridge": parsed.to_dict(),
            "initial_features": parsed.features,
            "refined_features": parsed.features,
            "refinement": {
                "schema": AUTOTRADER_CHATBOT_REFINEMENT_SCHEMA,
                "method": "not_run_security_block",
                "steps_run": 0,
                "trace": [],
                "ebrm_authorizes_trade": False,
            },
            "proposal_inputs": None,
            "guard_evaluation": None,
            "krr_advice": {
                "schema": "zenodex/agents/autotrader_chat_krr_advice/v1",
                "status": "not_run_security_block",
                "krr_authorizes_trade": False,
            },
            "advisory_card": {
                "schema": "zenodex/energy/autotrader_advisory_card/v1",
                "status": "blocked_by_policy_guard",
                "risk_level": "critical",
                "blocked_reasons": list(parsed.security_flags),
                "suggested_controls": ["Reset the conversational request with explicit limits."],
                "authority": _authority_packet(),
            },
            "authority": _authority_packet(),
        }


def _features_from_guard_inputs(
    *,
    strategy: StrategyIR,
    inputs: AutoTraderLocalGuardInputs,
) -> dict[str, float]:
    signal = inputs.signal_packet
    quote_epoch = inputs.resolved_quote_epoch()
    quote_age = 1.0
    if quote_epoch is not None:
        quote_age = max(0.0, inputs.current_epoch - quote_epoch) / max(
            1.0,
            strategy.risk_limits.max_oracle_staleness_epochs * 2.0,
        )
    budget_denominator = max(1.0, strategy.notional_caps.per_order_max * 2.0)
    slippage_bps = (
        strategy.risk_limits.max_slippage_bps if inputs.slippage_bps is None else inputs.slippage_bps
    )
    signal_verified = bool(
        signal is not None
        and signal.quote_receipt_present
        and signal.quote_receipt_verified
        and signal.source_available
        and signal.auth_ok
        and signal.binding_ok
    )
    values = {
        "insufficient_balance_flag": 0.0,
        "stale_signal_flag": 1.0 if quote_age > 0.5 else 0.0,
        "budget_violation_flag": 1.0 if inputs.order_amount > strategy.notional_caps.per_order_max else 0.0,
        "cooldown_violation_flag": 0.0,
        "slippage_violation_flag": 1.0 if slippage_bps > strategy.risk_limits.max_slippage_bps else 0.0,
        "route_violation_flag": 0.0 if signal_verified else 1.0,
        "missing_capability_flag": 0.0,
        "nonce_violation_flag": 0.0,
        "expected_edge_norm": 0.55,
        "signal_strength_norm": 0.75 if signal_verified else 0.25,
        "liquidity_score_norm": 0.60,
        "hedge_coverage_norm": 0.45,
        "execution_urgency_norm": 0.40,
        "drawdown_risk_norm": 0.30,
        "slippage_bps_norm": min(1.0, max(0.0, slippage_bps / 100.0)),
        "fee_bps_norm": 0.10,
        "budget_used_norm": min(1.0, max(0.0, inputs.order_amount / budget_denominator)),
        "price_deviation_norm": 0.30,
        "position_pressure_norm": min(1.0, max(0.0, inputs.order_amount / budget_denominator)),
        "nonce_age_norm": min(1.0, max(0.0, quote_age)),
    }
    if inputs.kill_switch_active:
        values["missing_capability_flag"] = 1.0
    return autotrader_feature_map(values)


def _apply_language_hints(
    *,
    normalized: str,
    features: dict[str, float],
    intent_tags: list[str],
    requested_controls: list[str],
) -> None:
    def tag(name: str) -> None:
        intent_tags.append(name)

    if _has_any(normalized, ("urgent", "urgency", "fast", "now", "quick")):
        features["execution_urgency_norm"] = max(features["execution_urgency_norm"], 0.82)
        tag("urgency_requested")
    if _has_any(normalized, ("slow", "patient", "wait", "careful timing")):
        features["execution_urgency_norm"] = min(features["execution_urgency_norm"], 0.25)
        requested_controls.append("slow_execution")
        tag("patient_execution_requested")
    if _has_any(normalized, ("volatile", "volatility", "turbulent", "choppy")):
        features["drawdown_risk_norm"] = max(features["drawdown_risk_norm"], 0.70)
        features["price_deviation_norm"] = max(features["price_deviation_norm"], 0.68)
        features["slippage_bps_norm"] = max(features["slippage_bps_norm"], 0.65)
        requested_controls.append("improve_route")
        tag("volatility_context")
    if _has_any(normalized, ("low slippage", "less slippage", "tight slippage", "reduce slippage")):
        features["slippage_bps_norm"] = min(features["slippage_bps_norm"], 0.28)
        requested_controls.append("improve_route")
        tag("slippage_reduction_requested")
    if _has_any(normalized, ("large", "bigger", "size up", "max budget", "high budget")):
        features["budget_used_norm"] = max(features["budget_used_norm"], 0.78)
        features["position_pressure_norm"] = max(features["position_pressure_norm"], 0.70)
        tag("larger_notional_requested")
    if _has_any(normalized, ("small", "smaller", "reduce size", "reduce notional", "less notional")):
        features["budget_used_norm"] = min(features["budget_used_norm"], 0.35)
        features["position_pressure_norm"] = min(features["position_pressure_norm"], 0.35)
        requested_controls.append("reduce_notional")
        tag("notional_reduction_requested")
    if _has_any(normalized, ("conservative", "safer", "safe", "protect capital")):
        features["budget_used_norm"] = min(features["budget_used_norm"], 0.35)
        features["slippage_bps_norm"] = min(features["slippage_bps_norm"], 0.30)
        features["execution_urgency_norm"] = min(features["execution_urgency_norm"], 0.35)
        requested_controls.extend(("reduce_notional", "slow_execution", "improve_route"))
        tag("conservative_requested")
    if _has_any(normalized, ("refresh", "new quote", "fresh quote", "new receipt")):
        requested_controls.append("refresh_receipts")
        tag("fresh_receipt_requested")
    slippage_match = re.search(r"\b(\d{1,4})\s*bps\b", normalized)
    if slippage_match is not None:
        bps = int(slippage_match.group(1))
        features["slippage_bps_norm"] = min(1.0, max(0.0, bps / 100.0))
        tag("explicit_slippage_bps")


def _guard_inputs_from_features(
    *,
    strategy: StrategyIR,
    base_inputs: AutoTraderLocalGuardInputs,
    features: Mapping[str, float],
    order_amount_scale: float,
) -> AutoTraderLocalGuardInputs:
    mapped = autotrader_feature_map(features)
    order_scale = max(1, int(round(strategy.notional_caps.per_order_max * order_amount_scale)))
    order_amount = max(1, int(round(mapped["budget_used_norm"] * order_scale)))
    slippage_bps = max(0, int(round(mapped["slippage_bps_norm"] * 100.0)))
    return AutoTraderLocalGuardInputs(
        current_epoch=base_inputs.current_epoch,
        order_amount=order_amount,
        projected_live_orders=base_inputs.projected_live_orders,
        lifetime_spent=base_inputs.lifetime_spent,
        spent_in_window=base_inputs.spent_in_window,
        budget_window_id=base_inputs.budget_window_id,
        kill_switch_active=base_inputs.kill_switch_active,
        last_action_epoch=base_inputs.last_action_epoch,
        slippage_bps=slippage_bps,
        quote_epoch=base_inputs.quote_epoch,
        signal_packet=base_inputs.signal_packet,
    )


def _merge_guard_status_into_card(
    card: dict[str, Any],
    guard_evaluation: AutoTraderLocalGuardEvaluation,
) -> dict[str, Any]:
    out = dict(card)
    authority = dict(out.get("authority", {}))
    authority.update(_authority_packet())
    out["authority"] = authority
    if guard_evaluation.ok:
        return out
    out["status"] = "blocked_by_policy_guard"
    out["risk_level"] = "high"
    blocked = list(out.get("blocked_reasons", []))
    for family, code in zip(
        guard_evaluation.blocking_families,
        guard_evaluation.blocking_reason_codes,
        strict=False,
    ):
        blocked.append(f"{family}:{code}")
    out["blocked_reasons"] = list(dict.fromkeys(blocked))
    reasons = list(out.get("reasons", []))
    if guard_evaluation.first_blocking_reason:
        reasons.insert(0, f"Local guard rejected the proposal: {guard_evaluation.first_blocking_reason}.")
    out["reasons"] = reasons
    return out


def _overall_status(
    *,
    card: Mapping[str, Any],
    guard_evaluation: AutoTraderLocalGuardEvaluation,
) -> AdvisorStatus:
    if not guard_evaluation.ok:
        return "blocked_by_policy_guard"
    status = str(card.get("status", "policy_valid_candidate"))
    if status in {"needs_risk_review", "policy_valid_with_caution", "policy_valid_candidate"}:
        return status  # type: ignore[return-value]
    return "policy_valid_candidate"


def _conversation_reply(
    *,
    status: AdvisorStatus,
    guard_evaluation: AutoTraderLocalGuardEvaluation,
    card: Mapping[str, Any],
    krr_advice: Mapping[str, Any],
) -> str:
    if status == "blocked_by_policy_guard":
        families = ", ".join(guard_evaluation.blocking_families) or "policy guard"
        reason = guard_evaluation.first_blocking_reason or "local guard rejection"
        controls = ", ".join(str(value) for value in card.get("suggested_controls", [])[:2])
        return (
            f"The proposal is blocked by local guard families: {families}. "
            f"Reason: {reason}. Suggested controls: {controls}."
        )
    checks = ", ".join(str(value) for value in krr_advice.get("preferred_checks", [])[:3])
    primary = str(card.get("display", {}).get("primary", "Policy-valid advisory proposal."))
    if checks:
        return f"{primary} KRR prioritizes these checks before promotion: {checks}."
    return primary


def _security_flags(normalized: str) -> tuple[str, ...]:
    return tuple(code for code, pattern in _SECURITY_PATTERNS if pattern.search(normalized))


def _normalize_query(query: str) -> str:
    return " ".join(query.lower().strip().split())


def _has_any(normalized: str, needles: Sequence[str]) -> bool:
    return any(needle in normalized for needle in needles)


def _control_order(requested_controls: Sequence[str]) -> tuple[str, ...]:
    ordered = [control for control in requested_controls if control in AUTOTRADER_CONTROL_IDS]
    ordered.extend(control for control in AUTOTRADER_CONTROL_IDS if control not in ordered)
    return tuple(ordered)


def _refinement_score(features: Mapping[str, float]) -> tuple[int, float, float, str]:
    mapped = autotrader_feature_map(features)
    label = autotrader_label_from_features(mapped)
    flag_count = sum(1 for name in AUTOTRADER_FEATURE_NAMES[:8] if mapped[name] >= 0.5)
    guard_penalty = 0 if bool(label["valid"]) else 1
    return (
        guard_penalty + flag_count,
        score_autotrader_future_tension(mapped),
        _hand_energy(mapped),
        _feature_fingerprint(mapped),
    )


def _hand_energy(features: Mapping[str, float]) -> float:
    row = autotrader_candidate_row_from_features(
        features,
        batch_id="chatbot",
        candidate_index=0,
    )
    return hand_energy_from_autotrader_row(row)


def _feature_fingerprint(features: Mapping[str, float]) -> str:
    return "|".join(f"{name}={features[name]:.6f}" for name in AUTOTRADER_FEATURE_NAMES)


def _authority_packet() -> dict[str, bool]:
    return {
        "llm_authorizes_trade": False,
        "ebrm_authorizes_trade": False,
        "krr_authorizes_trade": False,
        "ux_card_authorizes_trade": False,
        "deterministic_policy_guards_authoritative": True,
        "chatbot_executes_trade": False,
        "chatbot_signs_intent": False,
        "chatbot_mutates_ledger_state": False,
    }


ZenoChatbotAdvisor = ZenoAutoTraderChatbotAdvisor

__all__ = [
    "AUTOTRADER_CHATBOT_ADVISOR_SCHEMA",
    "AUTOTRADER_CHATBOT_LANGUAGE_SCHEMA",
    "AUTOTRADER_CHATBOT_REFINEMENT_SCHEMA",
    "AutoTraderChatbotConfig",
    "ZenoAutoTraderChatbotAdvisor",
    "ZenoChatbotAdvisor",
]
