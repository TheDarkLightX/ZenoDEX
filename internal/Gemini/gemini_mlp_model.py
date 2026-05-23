"""
Gemini MLP: A 2-layer Neural Network for energy ranking.
Trained with NumPy, executed in pure Python.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

@dataclass(frozen=True)
class MlpEnergyModel:
    """A 2-layer MLP (Linear -> ReLU -> Linear) in pure Python."""

    feature_names: tuple[str, ...]
    w1: list[list[float]]  # [in_dim][hidden_dim]
    b1: list[float]        # [hidden_dim]
    w2: list[float]        # [hidden_dim]
    b2: float

    def energy(self, features: Sequence[float]) -> float:
        energy, _ = self.forward(features)
        return energy

    def forward(self, features: Sequence[float]) -> tuple[float, list[float]]:
        """Forward pass returning (energy, hidden_activations)."""
        if len(features) != len(self.feature_names):
            raise ValueError(f"expected {len(self.feature_names)} features, got {len(features)}")

        hidden_dim = len(self.b1)
        hidden = [0.0] * hidden_dim
        for j in range(hidden_dim):
            val = self.b1[j]
            for i, x in enumerate(features):
                val += x * self.w1[i][j]
            hidden[j] = max(0.0, val) # ReLU

        res = self.b2
        for j, h in enumerate(hidden):
            res += h * self.w2[j]
        return float(res), hidden

    def grad_input(self, features: Sequence[float]) -> list[float]:
        """Compute the gradient of the energy w.r.t the input features: dE/dx."""
        energy, hidden = self.forward(features)

        # dE/dh = w2
        # dh/dz = 1 if z > 0 else 0 (ReLU derivative)
        # dz/dx = w1

        hidden_dim = len(self.b1)
        in_dim = len(self.w1)

        # dE/dz = w2 * (z > 0)
        # We don't have z, but we have hidden = max(0, z)
        # So dE/dz[j] = w2[j] if hidden[j] > 0 else 0
        de_dz = [0.0] * hidden_dim
        for j in range(hidden_dim):
            if hidden[j] > 0:
                de_dz[j] = self.w2[j]

        # dE/dx[i] = sum_j (de/dz[j] * dz/dx[i,j])
        # dz/dx[i,j] = w1[i][j]
        grad = [0.0] * in_dim
        for i in range(in_dim):
            val = 0.0
            for j in range(hidden_dim):
                val += de_dz[j] * self.w1[i][j]
            grad[i] = val

        return grad

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "zenodex/energy/gemini_mlp/v1",
            "model_type": "mlp_energy",
            "feature_names": list(self.feature_names),
            "w1": self.w1,
            "b1": self.b1,
            "w2": self.w2,
            "b2": float(self.b2),
        }

    @classmethod
    def from_dict(cls, payload: dict[str, Any]) -> "MlpEnergyModel":
        if payload.get("schema") != "zenodex/energy/gemini_mlp/v1":
            raise ValueError("unsupported MLP energy model schema")
        return cls(
            feature_names=tuple(payload["feature_names"]),
            w1=payload["w1"],
            b1=payload["b1"],
            w2=payload["w2"],
            b2=payload["b2"],
        )

def save_mlp_model(model: MlpEnergyModel, path: str | Path) -> None:
    Path(path).write_text(json.dumps(model.to_dict(), indent=2) + "\n", encoding="utf-8")

def load_mlp_model(path: str | Path) -> MlpEnergyModel:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    return MlpEnergyModel.from_dict(payload)
