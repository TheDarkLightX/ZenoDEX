"""UX-facing advisory receipts for AutoTraderEnergy.

These helpers turn policy labels, energy scores, and future-tension diagnostics
into compact user-facing cards. They do not make an executable trade decision.
"""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from .autotrader_energy import (
    autotrader_candidate_row_from_features,
    autotrader_feature_map,
    autotrader_label_from_features,
    hand_energy_from_autotrader_row,
)
from .zeno_jepa import (
    AUTOTRADER_CONTROL_IDS,
    ZenoJepaLinearWorldModel,
    autotrader_control_effect,
    project_autotrader_future_stress,
    score_autotrader_future_tension,
)

AUTOTRADER_FLAG_LABELS: dict[str, str] = {
    "insufficient_balance_flag": "insufficient balance",
    "stale_signal_flag": "stale signal or quote",
    "budget_violation_flag": "budget limit",
    "cooldown_violation_flag": "cooldown",
    "slippage_violation_flag": "slippage limit",
    "route_violation_flag": "route or quote binding",
    "missing_capability_flag": "wallet capability",
    "nonce_violation_flag": "nonce freshness",
}


def build_autotrader_advisory_card(
    features: Mapping[str, float] | Sequence[float],
    *,
    candidate_id: str = "proposal",
    model: ZenoJepaLinearWorldModel | None = None,
    future_caution_threshold: float = 2.50,
    future_warning_threshold: float = 3.50,
) -> dict[str, Any]:
    """Build a deterministic explanation card for one proposal."""

    mapped = autotrader_feature_map(features)
    label = autotrader_label_from_features(mapped)
    row = autotrader_candidate_row_from_features(
        mapped,
        batch_id="ux",
        candidate_index=_stable_candidate_index(candidate_id),
    )
    energy = hand_energy_from_autotrader_row(row)
    future_tension = score_autotrader_future_tension(mapped, model=model)
    future_stress = project_autotrader_future_stress(mapped)
    blocked_reasons = _blocked_reasons(mapped)
    future_level = _future_level(
        future_tension,
        caution_threshold=future_caution_threshold,
        warning_threshold=future_warning_threshold,
    )
    risk_level = _risk_level(mapped, future_level=future_level)
    badges = _badges(mapped, valid=bool(label["valid"]), future_level=future_level)
    reasons = _reasons(mapped, valid=bool(label["valid"]), future_level=future_level)
    suggested_control_ids = _suggested_control_ids(
        mapped,
        blocked_reasons=blocked_reasons,
        future_level=future_level,
        future_stress=future_stress,
    )
    control_effects = [
        autotrader_control_effect(mapped, control_id, model=model)
        | {"label": _control_label(control_id)}
        for control_id in suggested_control_ids
    ]
    suggested_controls = [_control_label(control_id) for control_id in suggested_control_ids]

    if not bool(label["valid"]):
        status = "blocked_by_policy_guard"
    elif future_level == "high":
        status = "needs_risk_review"
    elif future_level == "medium":
        status = "policy_valid_with_caution"
    else:
        status = "policy_valid_candidate"

    return {
        "schema": "zenodex/energy/autotrader_advisory_card/v1",
        "candidate_id": candidate_id,
        "status": status,
        "risk_level": risk_level,
        "badges": badges,
        "blocked_reasons": blocked_reasons,
        "reasons": reasons,
        "suggested_controls": suggested_controls,
        "scores": {
            "hand_energy": energy,
            "deterministic_objective": float(label["objective"]),
            "future_tension": future_tension,
            "future_tension_level": future_level,
            "future_stress": future_stress,
        },
        "authority": {
            "policy_guard_required": True,
            "deterministic_policy_guards_authoritative": True,
            "model_authorizes_trade": False,
            "future_tension_authorizes_trade": False,
            "ux_card_authorizes_trade": False,
        },
        "display": {
            "primary": _primary_message(status, blocked_reasons, future_level),
            "secondary": _secondary_message(mapped, future_tension),
        },
        "control_effects": control_effects,
    }


def build_autotrader_batch_ux(
    rows: Sequence[Mapping[str, Any]],
    *,
    model: ZenoJepaLinearWorldModel | None = None,
    max_cards: int = 3,
) -> dict[str, Any]:
    """Summarize a ranked batch into the UX payload a client can display."""

    if max_cards <= 0:
        raise ValueError("max_cards must be positive")
    ranked = sorted(
        rows,
        key=lambda row: (
            0 if bool(row["label"].get("valid", False)) else 1,
            score_autotrader_future_tension(row["features"], model=model),
            float(row["label"].get("hand_energy", 0.0)),
            str(row["candidate_hash"]),
        ),
    )
    cards = [
        build_autotrader_advisory_card(
            row["features"],
            candidate_id=str(row.get("candidate_id", row.get("candidate_hash", index))),
            model=model,
        )
        for index, row in enumerate(ranked[:max_cards])
    ]
    valid_count = sum(1 for row in rows if bool(row["label"].get("valid", False)))
    blocked_count = len(rows) - valid_count
    high_future_count = sum(
        1
        for row in rows
        if score_autotrader_future_tension(row["features"], model=model) >= 1.85
    )
    return {
        "schema": "zenodex/energy/autotrader_batch_ux/v1",
        "candidate_count": len(rows),
        "valid_count": valid_count,
        "blocked_count": blocked_count,
        "high_future_tension_count": high_future_count,
        "cards": cards,
        "authority": {
            "policy_guard_required": True,
            "deterministic_policy_guards_authoritative": True,
            "model_authorizes_trade": False,
            "ux_card_authorizes_trade": False,
        },
    }


def _blocked_reasons(features: Mapping[str, float]) -> list[str]:
    reasons = []
    for name, label in AUTOTRADER_FLAG_LABELS.items():
        if features.get(name, 0.0) >= 0.5:
            reasons.append(label)
    return reasons


def _badges(features: Mapping[str, float], *, valid: bool, future_level: str) -> list[str]:
    badges = ["policy-valid" if valid else "policy-blocked"]
    if features["expected_edge_norm"] >= 0.7:
        badges.append("strong-edge")
    if features["liquidity_score_norm"] >= 0.7:
        badges.append("deep-liquidity")
    if features["slippage_bps_norm"] <= 0.25:
        badges.append("low-slippage")
    if features["drawdown_risk_norm"] >= 0.65:
        badges.append("drawdown-risk")
    badges.append(f"future-{future_level}")
    return badges


def _reasons(features: Mapping[str, float], *, valid: bool, future_level: str) -> list[str]:
    if not valid:
        reasons = ["Deterministic policy flags must clear before execution."]
    else:
        reasons = ["Deterministic policy flags are clear for this proposal."]
    if features["expected_edge_norm"] >= 0.7:
        reasons.append("Expected edge is high relative to the synthetic policy scale.")
    if features["slippage_bps_norm"] >= 0.6:
        reasons.append("Slippage pressure is elevated.")
    if features["budget_used_norm"] >= 0.75:
        reasons.append("Budget usage is close to the configured limit.")
    if features["liquidity_score_norm"] <= 0.35:
        reasons.append("Liquidity score is thin, so future fragility can rise.")
    if future_level == "high":
        reasons.append("Predicted post-action future tension is high.")
    elif future_level == "medium":
        reasons.append("Predicted post-action future tension is moderate.")
    else:
        reasons.append("Predicted post-action future tension is low.")
    return reasons


def _suggested_control_ids(
    features: Mapping[str, float],
    *,
    blocked_reasons: Sequence[str],
    future_level: str,
    future_stress: Mapping[str, Any],
) -> list[str]:
    controls: list[str] = []
    if blocked_reasons:
        controls.append("refresh_receipts")
    if "stale signal or quote" in blocked_reasons:
        controls.append("refresh_receipts")
    if "route or quote binding" in blocked_reasons:
        controls.append("improve_route")
    if "slippage limit" in blocked_reasons or features["slippage_bps_norm"] >= 0.6:
        controls.append("improve_route")
        controls.append("reduce_notional")
    if "budget limit" in blocked_reasons or features["budget_used_norm"] >= 0.75:
        controls.append("reduce_notional")
        controls.append("wait_budget_recovery")
    later_failures = future_stress["later_failures"]
    if later_failures["next_slippage_failure"]:
        controls.append("improve_route")
        controls.append("reduce_notional")
    if later_failures["next_budget_failure"]:
        controls.append("wait_budget_recovery")
    if later_failures["next_drawdown_failure"]:
        controls.append("reduce_notional")
        controls.append("slow_execution")
    if future_level == "high":
        controls.append("slow_execution")
    if not controls:
        controls.append("refresh_receipts")
    deduped = []
    for control_id in controls:
        if control_id in AUTOTRADER_CONTROL_IDS and control_id not in deduped:
            deduped.append(control_id)
    return deduped


def _control_label(control_id: str) -> str:
    return {
        "refresh_receipts": "Refresh oracle and quote receipts.",
        "improve_route": "Tighten route selection to reduce slippage.",
        "reduce_notional": "Reduce notional size.",
        "slow_execution": "Prefer a slower execution plan.",
        "wait_budget_recovery": "Wait for budget recovery.",
    }[control_id]


def _future_level(
    value: float,
    *,
    caution_threshold: float,
    warning_threshold: float,
) -> str:
    if value >= warning_threshold:
        return "high"
    if value >= caution_threshold:
        return "medium"
    return "low"


def _risk_level(features: Mapping[str, float], *, future_level: str) -> str:
    if (
        future_level == "high"
        or features["drawdown_risk_norm"] >= 0.75
        or features["slippage_bps_norm"] >= 0.75
    ):
        return "high"
    if (
        future_level == "medium"
        or features["drawdown_risk_norm"] >= 0.5
        or features["budget_used_norm"] >= 0.75
    ):
        return "medium"
    return "low"


def _primary_message(status: str, blocked_reasons: Sequence[str], future_level: str) -> str:
    if status == "blocked_by_policy_guard":
        joined = ", ".join(blocked_reasons[:3]) if blocked_reasons else "policy guard"
        return f"Blocked before execution: {joined}."
    if status == "needs_risk_review":
        return "Policy-valid proposal with high future-tension risk."
    if status == "policy_valid_with_caution":
        return "Policy-valid proposal with moderate future-tension risk."
    if future_level == "low":
        return "Policy-valid proposal with low predicted future tension."
    return "Policy-valid proposal ready for deterministic policy check."


def _secondary_message(features: Mapping[str, float], future_tension: float) -> str:
    return (
        "Edge "
        f"{features['expected_edge_norm']:.2f}, liquidity {features['liquidity_score_norm']:.2f}, "
        f"slippage {features['slippage_bps_norm']:.2f}, future tension {future_tension:.2f}."
    )


def _stable_candidate_index(candidate_id: str) -> int:
    total = 0
    for char in candidate_id:
        total = (total * 131 + ord(char)) % 1_000_000
    return total
