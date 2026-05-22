"""
ZenoGuard: Advisory Safety Predictor.
Predicts the probability that a candidate will pass the verifier.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

@dataclass(frozen=True)
class ZenoGuardModel:
    """Logistic Regression model for safety prediction."""

    feature_names: tuple[str, ...]
    weights: list[float]
    bias: float

    def predict_proba(self, features: Sequence[float]) -> float:
        """Predict the probability of 'valid' (0.0 to 1.0)."""
        if len(features) != len(self.weights):
            raise ValueError("feature length mismatch")

        z = self.bias
        for w, x in zip(self.weights, features):
            z += w * x

        # Sigmoid
        try:
            return 1.0 / (1.0 + math.exp(-z))
        except OverflowError:
            return 0.0 if z < 0 else 1.0

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "zenodex/guard/v1",
            "feature_names": list(self.feature_names),
            "weights": self.weights,
            "bias": float(self.bias),
        }

    @classmethod
    def from_dict(cls, payload: dict[str, Any]) -> "ZenoGuardModel":
        return cls(
            feature_names=tuple(payload["feature_names"]),
            weights=payload["weights"],
            bias=payload["bias"],
        )

def save_guard_model(model: ZenoGuardModel, path: str | Path) -> None:
    Path(path).write_text(json.dumps(model.to_dict(), indent=2) + "\n", encoding="utf-8")

def load_guard_model(path: str | Path) -> ZenoGuardModel:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    return ZenoGuardModel.from_dict(payload)
