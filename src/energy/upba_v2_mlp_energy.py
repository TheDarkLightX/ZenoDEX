"""Pure-Python advisory MLP and guard models for UPBA v2 energy search."""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

from src.energy.upba_v2_energy_model import LinearEnergyModel


MLP_MODEL_SCHEMAS = {
    "zenodex/energy/mlp_ranker/v1",
    "zenodex/energy/gemini_mlp/v1",
}

GUARD_MODEL_SCHEMAS = {
    "zenodex/energy/logistic_guard/v1",
    "zenodex/guard/v1",
}


@dataclass(frozen=True)
class MlpEnergyModel:
    """Small Linear/ReLU/Linear advisory energy model with no runtime deps."""

    feature_names: tuple[str, ...]
    w1: tuple[tuple[float, ...], ...]
    b1: tuple[float, ...]
    w2: tuple[float, ...]
    b2: float = 0.0

    def __post_init__(self) -> None:
        input_dim = len(self.feature_names)
        hidden_dim = len(self.b1)
        if input_dim <= 0 or hidden_dim <= 0:
            raise ValueError("MLP input and hidden dimensions must be positive")
        if len(self.w1) != input_dim:
            raise ValueError("MLP w1 row count must match feature_names")
        if len(self.w2) != hidden_dim:
            raise ValueError("MLP w2 length must match hidden dimension")
        for row in self.w1:
            if len(row) != hidden_dim:
                raise ValueError("each MLP w1 row must match hidden dimension")

    @property
    def parameter_count(self) -> int:
        return len(self.feature_names) * len(self.b1) + len(self.b1) + len(self.w2) + 1

    def energy(self, features: Sequence[float]) -> float:
        if len(features) != len(self.feature_names):
            raise ValueError(f"expected {len(self.feature_names)} features, got {len(features)}")
        hidden: list[float] = []
        for column_index, bias in enumerate(self.b1):
            value = bias
            for feature_index, feature_value in enumerate(features):
                value += float(feature_value) * self.w1[feature_index][column_index]
            hidden.append(max(0.0, value))
        return float(sum(value * weight for value, weight in zip(hidden, self.w2, strict=True)) + self.b2)

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "zenodex/energy/mlp_ranker/v1",
            "model_type": "mlp_energy",
            "feature_names": list(self.feature_names),
            "w1": [list(row) for row in self.w1],
            "b1": list(self.b1),
            "w2": list(self.w2),
            "b2": float(self.b2),
        }

    @classmethod
    def from_dict(cls, payload: dict[str, Any]) -> "MlpEnergyModel":
        if payload.get("schema") not in MLP_MODEL_SCHEMAS:
            raise ValueError("unsupported MLP energy model schema")
        feature_names = payload.get("feature_names")
        w1 = payload.get("w1")
        b1 = payload.get("b1")
        w2 = payload.get("w2")
        if not isinstance(feature_names, list) or not all(isinstance(name, str) for name in feature_names):
            raise TypeError("MLP feature_names must be a list of strings")
        return cls(
            feature_names=tuple(feature_names),
            w1=tuple(tuple(float(value) for value in row) for row in _require_matrix(w1, "w1")),
            b1=tuple(float(value) for value in _require_vector(b1, "b1")),
            w2=tuple(float(value) for value in _require_vector(w2, "w2")),
            b2=float(payload.get("b2", 0.0)),
        )


@dataclass(frozen=True)
class LogisticGuardModel:
    """Advisory validity-probability model used only as a ranking penalty."""

    feature_names: tuple[str, ...]
    weights: tuple[float, ...]
    bias: float = 0.0

    def __post_init__(self) -> None:
        if len(self.feature_names) != len(self.weights):
            raise ValueError("guard feature_names and weights must have the same length")

    @property
    def parameter_count(self) -> int:
        return len(self.weights) + 1

    def predict_proba(self, features: Sequence[float]) -> float:
        if len(features) != len(self.weights):
            raise ValueError(f"expected {len(self.weights)} features, got {len(features)}")
        logit = self.bias + sum(weight * float(value) for weight, value in zip(self.weights, features, strict=True))
        try:
            return 1.0 / (1.0 + math.exp(-logit))
        except OverflowError:
            return 0.0 if logit < 0.0 else 1.0

    @classmethod
    def from_dict(cls, payload: dict[str, Any]) -> "LogisticGuardModel":
        if payload.get("schema") not in GUARD_MODEL_SCHEMAS:
            raise ValueError("unsupported logistic guard model schema")
        feature_names = payload.get("feature_names")
        weights = payload.get("weights")
        if not isinstance(feature_names, list) or not all(isinstance(name, str) for name in feature_names):
            raise TypeError("guard feature_names must be a list of strings")
        return cls(
            feature_names=tuple(feature_names),
            weights=tuple(float(value) for value in _require_vector(weights, "weights")),
            bias=float(payload.get("bias", 0.0)),
        )


def load_mlp_model(path: str | Path) -> MlpEnergyModel:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    return MlpEnergyModel.from_dict(payload)


def load_logistic_guard_model(path: str | Path) -> LogisticGuardModel:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    return LogisticGuardModel.from_dict(payload)


def load_advisory_energy_model(path: str | Path) -> LinearEnergyModel | MlpEnergyModel:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    schema = payload.get("schema")
    if schema == "zenodex/energy/linear_ranker/v1":
        return LinearEnergyModel.from_dict(payload)
    if schema in MLP_MODEL_SCHEMAS:
        return MlpEnergyModel.from_dict(payload)
    raise ValueError(f"unsupported advisory energy model schema: {schema!r}")


def _require_vector(value: Any, name: str) -> list[int | float]:
    if not isinstance(value, list) or not all(isinstance(item, int | float) for item in value):
        raise TypeError(f"{name} must be a numeric list")
    return value

def _require_matrix(value: Any, name: str) -> list[list[int | float]]:
    if not isinstance(value, list) or not all(isinstance(row, list) for row in value):
        raise TypeError(f"{name} must be a numeric matrix")
    for row in value:
        if not all(isinstance(item, int | float) for item in row):
            raise TypeError(f"{name} must be a numeric matrix")
    return value
