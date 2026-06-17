"""Tiny trainable energy models for UPBA v2 ranking experiments."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

from .upba_v2_features import FEATURE_DIM, FEATURE_NAMES


def count_mlp_parameters(input_dim: int = FEATURE_DIM, hidden_dim: int = 64, hidden_layers: int = 1) -> int:
    """Count parameters for Linear/ReLU MLPs ending in one scalar energy."""

    if input_dim <= 0 or hidden_dim <= 0 or hidden_layers <= 0:
        raise ValueError("input_dim, hidden_dim, and hidden_layers must be positive")
    if hidden_layers == 1:
        return input_dim * hidden_dim + hidden_dim + hidden_dim * 1 + 1
    return (
        input_dim * hidden_dim
        + hidden_dim
        + (hidden_layers - 1) * (hidden_dim * hidden_dim + hidden_dim)
        + hidden_dim
        + 1
    )


def torch_available() -> bool:
    try:
        import torch  # noqa: F401
    except ImportError:
        return False
    return True


def build_torch_mlp(input_dim: int = FEATURE_DIM, hidden_dim: int = 64) -> Any:
    """Build the requested CPU-friendly PyTorch MLP when torch is installed."""

    try:
        import torch.nn as nn
    except ImportError as exc:  # pragma: no cover - depends on optional torch
        raise RuntimeError("PyTorch is not installed") from exc
    return nn.Sequential(nn.Linear(input_dim, hidden_dim), nn.ReLU(), nn.Linear(hidden_dim, 1))


@dataclass(frozen=True)
class LinearEnergyModel:
    """Small pure-Python linear energy model used as the no-dependency fallback."""

    feature_names: tuple[str, ...]
    weights: tuple[float, ...]
    bias: float = 0.0

    def __post_init__(self) -> None:
        if len(self.feature_names) != len(self.weights):
            raise ValueError("feature_names and weights must have the same length")

    def energy(self, features: Sequence[float]) -> float:
        if len(features) != len(self.weights):
            raise ValueError("feature length does not match model")
        return float(sum(weight * float(value) for weight, value in zip(self.weights, features, strict=True)) + self.bias)

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "zenodex/energy/linear_ranker/v1",
            "model_type": "linear_energy",
            "feature_names": list(self.feature_names),
            "weights": list(self.weights),
            "bias": float(self.bias),
        }

    @classmethod
    def from_dict(cls, payload: dict[str, Any]) -> "LinearEnergyModel":
        if payload.get("schema") != "zenodex/energy/linear_ranker/v1":
            raise ValueError("unsupported linear energy model schema")
        feature_names_obj = payload.get("feature_names")
        weights_obj = payload.get("weights")
        if not isinstance(feature_names_obj, list) or not all(isinstance(name, str) for name in feature_names_obj):
            raise TypeError("model feature_names must be a list of strings")
        if not isinstance(weights_obj, list) or not all(isinstance(weight, int | float) for weight in weights_obj):
            raise TypeError("model weights must be numeric")
        return cls(
            feature_names=tuple(feature_names_obj),
            weights=tuple(float(weight) for weight in weights_obj),
            bias=float(payload.get("bias", 0.0)),
        )


def initial_hand_weight_model() -> LinearEnergyModel:
    """Return a linear model matching the dominant hand-energy feature directions."""

    weights = {name: 0.0 for name in FEATURE_NAMES}
    weights["candidate_balance_violation_count_norm"] = 1_000_000.0
    weights["candidate_limit_violation_count_norm"] = 1_000_000.0
    weights["candidate_negative_reserve_flag"] = 1_000_000.0
    weights["candidate_invariant_violation_flag"] = 1_000_000.0
    weights["candidate_noncanonical_fill_vector_flag"] = 100_000.0
    weights["candidate_price_objective_violation_flag"] = 100_000.0
    weights["candidate_output_mismatch_count_norm"] = 100_000.0
    weights["candidate_schema_policy_mismatch_flag"] = 100_000.0
    weights["candidate_price_ratio_unreduced_flag"] = 50_000.0
    weights["candidate_fill_coverage_violation_flag"] = 100_000.0
    weights["candidate_duplicate_fill_id_flag"] = 100_000.0
    weights["candidate_unknown_fill_id_count_norm"] = 100_000.0
    weights["candidate_executed_input_over_amount_count_norm"] = 100_000.0
    weights["candidate_output_without_input_count_norm"] = 100_000.0
    weights["candidate_zero_net_input_count_norm"] = 10_000.0
    weights["candidate_dust_penalty_norm"] = 100.0
    weights["candidate_imbalance_penalty"] = 10.0
    weights["candidate_normalized_executed_volume"] = -10.0
    weights["candidate_normalized_surplus"] = -1.0
    return LinearEnergyModel(
        feature_names=FEATURE_NAMES,
        weights=tuple(weights[name] for name in FEATURE_NAMES),
    )


def save_linear_model(model: LinearEnergyModel, path: str | Path) -> None:
    Path(path).write_text(json.dumps(model.to_dict(), indent=2, sort_keys=True) + "\n", encoding="utf-8")


def load_linear_model(path: str | Path) -> LinearEnergyModel:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    return LinearEnergyModel.from_dict(payload)
