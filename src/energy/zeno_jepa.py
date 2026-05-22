"""Advisory JEPA-style future-tension scoring for ZenoEnergy.

The model predicts a bounded latent post-action tension score. It can rank,
explain, or flag proposals for deterministic checks. It cannot authorize an
AutoTrader action or a settlement.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from hashlib import sha256
from statistics import mean
from typing import Any, Mapping, Sequence

from .autotrader_energy import (
    AutoTraderLinearEnergyModel,
    autotrader_feature_map,
    canonical_autotrader_features,
    hand_energy_from_autotrader_row,
)

ZENO_JEPA_STATE_FEATURE_NAMES: tuple[str, ...] = (
    "liquidity_gap_norm",
    "drawdown_risk_norm",
    "price_deviation_norm",
    "position_pressure_norm",
    "budget_used_norm",
    "nonce_age_norm",
)

ZENO_JEPA_ACTION_FEATURE_NAMES: tuple[str, ...] = (
    "edge_gap_norm",
    "execution_urgency_norm",
    "slippage_bps_norm",
    "budget_used_norm",
    "price_deviation_norm",
    "position_pressure_norm",
)

AUTOTRADER_CONTROL_IDS: tuple[str, ...] = (
    "refresh_receipts",
    "improve_route",
    "reduce_notional",
    "slow_execution",
    "wait_budget_recovery",
)


@dataclass(frozen=True)
class ZenoJepaLinearWorldModel:
    """Tiny deterministic latent predictor used as an advisory scorer."""

    state_feature_names: tuple[str, ...]
    action_feature_names: tuple[str, ...]
    latent_names: tuple[str, ...]
    w_encoder: tuple[tuple[float, ...], ...]
    w_predictor: tuple[tuple[float, ...], ...]
    bias: tuple[float, ...]

    def __post_init__(self) -> None:
        latent_dim = len(self.latent_names)
        if latent_dim == 0:
            raise ValueError("latent_names must be nonempty")
        if len(self.w_encoder) != len(self.state_feature_names):
            raise ValueError("w_encoder row count must match state features")
        if any(len(row) != latent_dim for row in self.w_encoder):
            raise ValueError("w_encoder column count must match latent names")
        expected_predictor_rows = latent_dim + len(self.action_feature_names)
        if len(self.w_predictor) != expected_predictor_rows:
            raise ValueError("w_predictor row count must match latent + action features")
        if any(len(row) != latent_dim for row in self.w_predictor):
            raise ValueError("w_predictor column count must match latent names")
        if len(self.bias) != latent_dim:
            raise ValueError("bias length must match latent names")

    def encode_state(self, state_vector: Sequence[float]) -> list[float]:
        if len(state_vector) != len(self.state_feature_names):
            raise ValueError("state vector length does not match model")
        return _project(state_vector, self.w_encoder, [0.0 for _ in self.latent_names])

    def predict_next_latent(
        self,
        state_vector: Sequence[float],
        action_vector: Sequence[float],
    ) -> list[float]:
        if len(action_vector) != len(self.action_feature_names):
            raise ValueError("action vector length does not match model")
        latent = self.encode_state(state_vector)
        return _project(
            tuple(latent) + tuple(float(value) for value in action_vector),
            self.w_predictor,
            list(self.bias),
        )

    def future_tension(
        self,
        state_vector: Sequence[float],
        action_vector: Sequence[float],
    ) -> float:
        """Return L2 tension of the predicted latent post-action state."""

        predicted = self.predict_next_latent(state_vector, action_vector)
        return math.sqrt(sum(value * value for value in predicted))

    def future_tension_from_features(
        self,
        features: Mapping[str, float] | Sequence[float],
    ) -> float:
        state, action = autotrader_jepa_vectors(features)
        return self.future_tension(state, action)

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "zenodex/energy/zeno_jepa_linear_world_model/v1",
            "model_type": "linear_latent_future_tension",
            "state_feature_names": list(self.state_feature_names),
            "action_feature_names": list(self.action_feature_names),
            "latent_names": list(self.latent_names),
            "w_encoder": [list(row) for row in self.w_encoder],
            "w_predictor": [list(row) for row in self.w_predictor],
            "bias": list(self.bias),
            "model_authorizes_settlement": False,
            "model_authorizes_trade": False,
        }

    @classmethod
    def from_dict(cls, payload: Mapping[str, Any]) -> "ZenoJepaLinearWorldModel":
        if payload.get("schema") != "zenodex/energy/zeno_jepa_linear_world_model/v1":
            raise ValueError("unsupported ZenoJEPA schema")
        return cls(
            state_feature_names=tuple(str(name) for name in payload["state_feature_names"]),
            action_feature_names=tuple(str(name) for name in payload["action_feature_names"]),
            latent_names=tuple(str(name) for name in payload["latent_names"]),
            w_encoder=tuple(tuple(float(value) for value in row) for row in payload["w_encoder"]),
            w_predictor=tuple(tuple(float(value) for value in row) for row in payload["w_predictor"]),
            bias=tuple(float(value) for value in payload["bias"]),
        )


def default_autotrader_jepa_model() -> ZenoJepaLinearWorldModel:
    """Return a deterministic future-tension scorer for AutoTrader proposals."""

    return ZenoJepaLinearWorldModel(
        state_feature_names=ZENO_JEPA_STATE_FEATURE_NAMES,
        action_feature_names=ZENO_JEPA_ACTION_FEATURE_NAMES,
        latent_names=(
            "liquidity_fragility",
            "drawdown_fragility",
            "execution_fragility",
            "operational_fragility",
        ),
        w_encoder=(
            (1.00, 0.20, 0.00, 0.00),
            (0.10, 1.00, 0.10, 0.00),
            (0.00, 0.70, 0.30, 0.00),
            (0.50, 0.30, 0.20, 0.10),
            (0.00, 0.10, 0.80, 0.10),
            (0.00, 0.00, 0.10, 0.80),
        ),
        w_predictor=(
            (0.72, 0.08, 0.00, 0.00),
            (0.10, 0.74, 0.10, 0.00),
            (0.00, 0.12, 0.76, 0.05),
            (0.00, 0.00, 0.08, 0.78),
            (0.55, 0.15, 0.10, 0.00),
            (0.10, 0.15, 0.22, 0.25),
            (0.05, 0.25, 1.20, 0.05),
            (0.00, 0.10, 0.60, 0.15),
            (0.05, 0.75, 0.35, 0.05),
            (0.60, 0.38, 0.20, 0.08),
        ),
        bias=(0.02, 0.02, 0.02, 0.02),
    )


def autotrader_jepa_vectors(
    features: Mapping[str, float] | Sequence[float],
) -> tuple[list[float], list[float]]:
    """Project AutoTrader features into JEPA state and action vectors."""

    mapped = autotrader_feature_map(features)
    state = [
        _clip01(1.0 - mapped["liquidity_score_norm"]),
        _clip01(mapped["drawdown_risk_norm"]),
        _clip01(mapped["price_deviation_norm"]),
        _clip01(mapped["position_pressure_norm"]),
        _clip01(mapped["budget_used_norm"]),
        _clip01(mapped["nonce_age_norm"]),
    ]
    action = [
        _clip01(1.0 - mapped["expected_edge_norm"]),
        _clip01(mapped["execution_urgency_norm"]),
        _clip01(mapped["slippage_bps_norm"]),
        _clip01(mapped["budget_used_norm"]),
        _clip01(mapped["price_deviation_norm"]),
        _clip01(mapped["position_pressure_norm"]),
    ]
    return state, action


def score_autotrader_future_tension(
    features: Mapping[str, float] | Sequence[float],
    *,
    model: ZenoJepaLinearWorldModel | None = None,
) -> float:
    """Score predicted post-action fragility for an AutoTrader proposal."""

    effective_model = default_autotrader_jepa_model() if model is None else model
    return effective_model.future_tension_from_features(features)


def project_autotrader_future_stress(
    features: Mapping[str, float] | Sequence[float],
) -> dict[str, Any]:
    """Project next-step stress labels for AutoTrader JEPA evaluation.

    These labels are deterministic research targets for future-risk scoring.
    They are not execution predicates.
    """

    mapped = autotrader_feature_map(features)
    liquidity_gap = _clip01(1.0 - mapped["liquidity_score_norm"])
    slippage_stress = _clip01(
        0.50 * mapped["slippage_bps_norm"]
        + 0.25 * mapped["price_deviation_norm"]
        + 0.20 * liquidity_gap
        + 0.05 * mapped["execution_urgency_norm"]
    )
    budget_stress = _clip01(
        0.70 * mapped["budget_used_norm"]
        + 0.15 * mapped["execution_urgency_norm"]
        + 0.15 * mapped["position_pressure_norm"]
    )
    drawdown_stress = _clip01(
        0.50 * mapped["drawdown_risk_norm"]
        + 0.20 * mapped["price_deviation_norm"]
        + 0.20 * mapped["position_pressure_norm"]
        + 0.10 * liquidity_gap
    )
    operational_stress = _clip01(
        0.45 * mapped["nonce_age_norm"]
        + 0.25 * mapped["execution_urgency_norm"]
        + 0.20 * mapped["budget_used_norm"]
        + 0.10 * mapped["price_deviation_norm"]
    )
    current_failure_count = sum(
        1
        for name in (
            "insufficient_balance_flag",
            "stale_signal_flag",
            "budget_violation_flag",
            "cooldown_violation_flag",
            "slippage_violation_flag",
            "route_violation_flag",
            "missing_capability_flag",
            "nonce_violation_flag",
        )
        if mapped[name] >= 0.5
    )
    later_failures = {
        "next_slippage_failure": slippage_stress >= 0.62,
        "next_budget_failure": budget_stress >= 0.74,
        "next_drawdown_failure": drawdown_stress >= 0.62,
        "next_operational_failure": operational_stress >= 0.72,
    }
    return {
        "schema": "zenodex/energy/autotrader_future_stress_projection/v1",
        "slippage_stress": slippage_stress,
        "budget_stress": budget_stress,
        "drawdown_stress": drawdown_stress,
        "operational_stress": operational_stress,
        "later_failures": later_failures,
        "later_failure_count": sum(1 for value in later_failures.values() if value),
        "any_later_policy_failure": any(later_failures.values()),
        "current_policy_failure_count": current_failure_count,
        "deterministic_projection_authorizes_trade": False,
    }


def apply_autotrader_control(
    features: Mapping[str, float] | Sequence[float],
    control_id: str,
) -> dict[str, float]:
    """Apply a deterministic safer counterfactual control to features."""

    if control_id not in AUTOTRADER_CONTROL_IDS:
        raise ValueError(f"unknown AutoTrader control: {control_id}")
    mapped = autotrader_feature_map(features)
    adjusted = dict(mapped)
    if control_id == "refresh_receipts":
        adjusted["stale_signal_flag"] = 0.0
        adjusted["nonce_violation_flag"] = 0.0
        adjusted["nonce_age_norm"] = min(adjusted["nonce_age_norm"], 0.15)
        adjusted["signal_strength_norm"] = _clip01(adjusted["signal_strength_norm"] + 0.10)
        adjusted["execution_urgency_norm"] = _clip01(adjusted["execution_urgency_norm"] * 0.90)
        adjusted["price_deviation_norm"] = _clip01(adjusted["price_deviation_norm"] * 0.90)
    elif control_id == "improve_route":
        adjusted["route_violation_flag"] = 0.0
        adjusted["slippage_violation_flag"] = 0.0
        adjusted["liquidity_score_norm"] = _clip01(adjusted["liquidity_score_norm"] + 0.30)
        adjusted["slippage_bps_norm"] = _clip01(adjusted["slippage_bps_norm"] * 0.55)
        adjusted["price_deviation_norm"] = _clip01(adjusted["price_deviation_norm"] * 0.60)
    elif control_id == "reduce_notional":
        adjusted["insufficient_balance_flag"] = 0.0
        adjusted["budget_violation_flag"] = 0.0
        adjusted["slippage_violation_flag"] = 0.0
        adjusted["budget_used_norm"] = _clip01(adjusted["budget_used_norm"] * 0.60)
        adjusted["slippage_bps_norm"] = _clip01(adjusted["slippage_bps_norm"] * 0.65)
        adjusted["price_deviation_norm"] = _clip01(adjusted["price_deviation_norm"] * 0.70)
        adjusted["position_pressure_norm"] = _clip01(adjusted["position_pressure_norm"] * 0.80)
    elif control_id == "slow_execution":
        adjusted["cooldown_violation_flag"] = 0.0
        adjusted["execution_urgency_norm"] = _clip01(adjusted["execution_urgency_norm"] * 0.45)
        adjusted["slippage_bps_norm"] = _clip01(adjusted["slippage_bps_norm"] * 0.85)
        adjusted["price_deviation_norm"] = _clip01(adjusted["price_deviation_norm"] * 0.85)
    elif control_id == "wait_budget_recovery":
        adjusted["budget_violation_flag"] = 0.0
        adjusted["cooldown_violation_flag"] = 0.0
        adjusted["budget_used_norm"] = _clip01(adjusted["budget_used_norm"] * 0.45)
        adjusted["execution_urgency_norm"] = _clip01(adjusted["execution_urgency_norm"] * 0.75)
        adjusted["position_pressure_norm"] = _clip01(adjusted["position_pressure_norm"] * 0.85)
    return adjusted


def autotrader_control_effect(
    features: Mapping[str, float] | Sequence[float],
    control_id: str,
    *,
    model: ZenoJepaLinearWorldModel | None = None,
) -> dict[str, Any]:
    """Measure future-tension and stress change for one suggested control."""

    before = autotrader_feature_map(features)
    after = apply_autotrader_control(before, control_id)
    before_tension = score_autotrader_future_tension(before, model=model)
    after_tension = score_autotrader_future_tension(after, model=model)
    before_stress = project_autotrader_future_stress(before)
    after_stress = project_autotrader_future_stress(after)
    return {
        "schema": "zenodex/energy/autotrader_control_effect/v1",
        "control_id": control_id,
        "future_tension_before": before_tension,
        "future_tension_after": after_tension,
        "future_tension_delta": after_tension - before_tension,
        "later_failure_count_before": before_stress["later_failure_count"],
        "later_failure_count_after": after_stress["later_failure_count"],
        "later_failure_delta": (
            int(after_stress["later_failure_count"])
            - int(before_stress["later_failure_count"])
        ),
        "control_authorizes_trade": False,
    }


def future_aware_autotrader_energy(
    row: Mapping[str, Any],
    *,
    model: ZenoJepaLinearWorldModel | None = None,
    base_model: AutoTraderLinearEnergyModel | None = None,
    future_weight: float = 4.0,
) -> float:
    """Combine current or learned energy with predicted future tension."""

    if future_weight < 0.0:
        raise ValueError("future_weight must be nonnegative")
    current_energy = (
        hand_energy_from_autotrader_row(dict(row))
        if base_model is None
        else base_model.energy(canonical_autotrader_features(row["features"]))
    )
    future_tension = score_autotrader_future_tension(row["features"], model=model)
    return float(current_energy + future_weight * future_tension)


def rank_autotrader_rows_future_aware(
    rows: Sequence[Mapping[str, Any]],
    *,
    model: ZenoJepaLinearWorldModel | None = None,
    base_model: AutoTraderLinearEnergyModel | None = None,
    future_weight: float = 4.0,
) -> list[Mapping[str, Any]]:
    """Return rows ordered by guard barrier, future-aware energy, and hash."""

    return sorted(
        rows,
        key=lambda row: (
            _hard_guard_barrier(row),
            future_aware_autotrader_energy(
                row,
                model=model,
                base_model=base_model,
                future_weight=future_weight,
            ),
            str(row["candidate_hash"]),
        ),
    )


def evaluate_autotrader_future_aware_rows(
    rows: Sequence[Mapping[str, Any]],
    *,
    model: ZenoJepaLinearWorldModel | None = None,
    base_model: AutoTraderLinearEnergyModel | None = None,
    future_weight: float = 4.0,
) -> dict[str, Any]:
    """Evaluate future-aware ordering under deterministic guard acceptance."""

    by_batch: dict[str, list[Mapping[str, Any]]] = {}
    for row in rows:
        by_batch.setdefault(str(row["batch_id"]), []).append(row)

    batches = 0
    top_1_hits = 0
    top_5_hits = 0
    calls: list[int] = []
    invalid_top_1_count = 0
    invalid_accept_count = 0
    future_tensions: list[float] = []
    winner_tensions: list[float] = []

    for batch_rows in by_batch.values():
        winners = [row for row in batch_rows if bool(row["label"]["is_winner"])]
        if not winners:
            continue
        batches += 1
        winner_hash = str(winners[0]["candidate_hash"])
        ordered = rank_autotrader_rows_future_aware(
            batch_rows,
            model=model,
            base_model=base_model,
            future_weight=future_weight,
        )
        if ordered and not bool(ordered[0]["label"]["valid"]):
            invalid_top_1_count += 1
        for row in ordered:
            future_tensions.append(score_autotrader_future_tension(row["features"], model=model))
        for row in winners:
            winner_tensions.append(score_autotrader_future_tension(row["features"], model=model))
        winner_position = next(
            index
            for index, row in enumerate(ordered, start=1)
            if str(row["candidate_hash"]) == winner_hash
        )
        calls.append(winner_position)
        if winner_position <= 1:
            top_1_hits += 1
        if winner_position <= min(5, len(ordered)):
            top_5_hits += 1
        accepted = _first_guard_accepted(ordered)
        if accepted is not None and not bool(accepted["label"]["valid"]):
            invalid_accept_count += 1

    return {
        "schema": "zenodex/energy/autotrader_future_aware_evaluation/v1",
        "mode": "learned_future_aware" if base_model is not None else "hand_future_aware",
        "future_weight": future_weight,
        "base_model": "autotrader_linear_ranker" if base_model is not None else "hand_energy",
        "batches": batches,
        "top_1_recall": _ratio(top_1_hits, batches),
        "top_5_recall": _ratio(top_5_hits, batches),
        "mean_guard_calls": mean(calls) if calls else 0.0,
        "p95_guard_calls": _percentile(calls, 0.95),
        "invalid_top_1_rate": _ratio(invalid_top_1_count, batches),
        "invalid_accept_count": invalid_accept_count,
        "future_tension_mean": mean(future_tensions) if future_tensions else 0.0,
        "winner_future_tension_mean": mean(winner_tensions) if winner_tensions else 0.0,
        "policy_guards_authoritative": True,
        "model_authorizes_trade": False,
        "future_tension_authorizes_trade": False,
    }


def model_fingerprint(model: ZenoJepaLinearWorldModel) -> str:
    payload = json.dumps(model.to_dict(), sort_keys=True, separators=(",", ":"))
    return sha256(payload.encode("utf-8")).hexdigest()


def _project(
    values: Sequence[float],
    weights: Sequence[Sequence[float]],
    bias: Sequence[float],
) -> list[float]:
    out = [float(value) for value in bias]
    for value, row in zip(values, weights, strict=True):
        for index, weight in enumerate(row):
            out[index] += float(value) * float(weight)
    return out


def _hard_guard_barrier(row: Mapping[str, Any]) -> float:
    label = row.get("label", {})
    return 0.0 if bool(label.get("valid", False)) else 1_000_000.0


def _first_guard_accepted(rows: Sequence[Mapping[str, Any]]) -> Mapping[str, Any] | None:
    for row in rows:
        if bool(row["label"]["valid"]):
            return row
    return None


def _clip01(value: float) -> float:
    return min(1.0, max(0.0, float(value)))


def _ratio(numerator: int, denominator: int) -> float:
    return 0.0 if denominator == 0 else numerator / denominator


def _percentile(values: list[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(round((len(ordered) - 1) * fraction)))
    return ordered[index]
