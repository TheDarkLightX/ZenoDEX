"""ZenoJEPA: advisory latent predictor for post-settlement market states.

The model scores predicted future tension. It is a search feature only; it does
not authorize settlement or replace deterministic verification.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Any, Sequence

@dataclass(frozen=True)
class ZenoJepaModel:
    """Predicts future latent state z' from current state x and action a (settlement)."""

    feature_names: tuple[str, ...]
    w_encoder: list[list[float]] # [dim][latent_dim]
    w_predictor: list[list[float]] # [latent_dim + action_dim][latent_dim]
    bias_jepa: float

    latent_dim: int = 8
    action_dim: int = 4 # e.g. [total_vol, net_imbalance, fee_yield, price_delta]

    def predict_latent_tension(self, state_features: Sequence[float], action_vector: Sequence[float]) -> float:
        """
        Predicts the 'tension' (norm of latent state) of the future market.
        Lower tension means a more stable post-settlement pool.
        """
        # 1. Encode current state
        if len(state_features) != len(self.feature_names):
            raise ValueError("state feature length does not match model")
        if len(action_vector) != self.action_dim:
            raise ValueError("action vector length does not match model")
        z = self._project(state_features, self.w_encoder)

        # 2. Concatenate with action (candidate settlement metrics)
        context = z + list(action_vector)

        # 3. Predict next latent state z'
        z_next = [0.0] * self.latent_dim
        for j in range(self.latent_dim):
            val = self.bias_jepa
            for i, x in enumerate(context):
                val += x * self.w_predictor[i][j]
            z_next[j] = val

        # 4. Energy = L2 norm of predicted latent state (Future Tension)
        return math.sqrt(sum(v*v for v in z_next))

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": "zenodex/energy/zeno_jepa/v1",
            "model_type": "latent_predictive_energy",
            "feature_names": list(self.feature_names),
            "w_encoder": self.w_encoder,
            "w_predictor": self.w_predictor,
            "bias_jepa": float(self.bias_jepa),
            "latent_dim": int(self.latent_dim),
            "action_dim": int(self.action_dim),
            "model_authorizes_settlement": False,
        }

    @classmethod
    def from_dict(cls, payload: dict[str, Any]) -> "ZenoJepaModel":
        if payload.get("schema") != "zenodex/energy/zeno_jepa/v1":
            raise ValueError("unsupported ZenoJEPA model schema")
        return cls(
            feature_names=tuple(str(name) for name in payload["feature_names"]),
            w_encoder=payload["w_encoder"],
            w_predictor=payload["w_predictor"],
            bias_jepa=float(payload["bias_jepa"]),
            latent_dim=int(payload.get("latent_dim", 8)),
            action_dim=int(payload.get("action_dim", 4)),
        )

    def _project(self, feat: Sequence[float], weights: Sequence[Sequence[float]]) -> list[float]:
        out_dim = len(weights[0])
        out = [0.0] * out_dim
        for j in range(out_dim):
            val = 0.0
            for i, x in enumerate(feat):
                val += x * weights[i][j]
            out[j] = val
        return out
