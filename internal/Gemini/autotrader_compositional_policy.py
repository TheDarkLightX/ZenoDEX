"""
Gemini AutoTrader Compositional Policy.
Allows modular strategy definition using energy kernels.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Mapping, Sequence

class PolicyKernel(ABC):
    """A modular component of the AutoTrader energy landscape."""
    @abstractmethod
    def energy(self, features: Mapping[str, float]) -> float:
        pass

class AlphaKernel(PolicyKernel):
    """Incentivizes trades with high expected edge and signal strength."""
    def energy(self, features: Mapping[str, float]) -> float:
        edge = features.get("expected_edge_norm", 0.0)
        signal = features.get("signal_strength_norm", 0.0)
        # Low energy = High quality trade
        return -(edge * 10.0 + signal * 5.0)

class RiskKernel(PolicyKernel):
    """Penalizes drawdown risk and position pressure."""
    def energy(self, features: Mapping[str, float]) -> float:
        drawdown = features.get("drawdown_risk_norm", 0.0)
        pressure = features.get("position_pressure_norm", 0.0)
        return drawdown * 15.0 + pressure * 5.0

class ExecutionCostKernel(PolicyKernel):
    """Penalizes adjustable execution costs while preserving alpha features."""
    def energy(self, features: Mapping[str, float]) -> float:
        slippage = features.get("slippage_bps_norm", 0.0)
        budget = features.get("budget_used_norm", 0.0)
        deviation = features.get("price_deviation_norm", 0.0)
        urgency = features.get("execution_urgency_norm", 0.0)
        return slippage * 8.0 + budget * 4.0 + deviation * 3.0 - urgency * 0.5

class ConstraintKernel(PolicyKernel):
    """Hard-penalizes budget, cooldown, and safety violations."""
    def energy(self, features: Mapping[str, float]) -> float:
        violations = [
            "insufficient_balance_flag",
            "budget_violation_flag",
            "cooldown_violation_flag",
            "slippage_violation_flag",
        ]
        total = 0.0
        for v in violations:
            if features.get(v, 0.0) > 0.5:
                total += 1000.0 # Heavy barrier
        return total

class SelfAttentiveCostKernel(PolicyKernel):
    """Captures quadratic alignment constraints between parameters using self-attention weights."""
    def __init__(self, attention_matrix: list[list[float]] | None = None, features_to_attend: tuple[str, ...] = ("slippage_bps_norm", "execution_urgency_norm", "budget_used_norm")):
        self.features = features_to_attend
        if attention_matrix is not None:
            self.A = attention_matrix
        else:
            # Default self-attention alignment constraints:
            # High urgency and high budget are negatively associated with slippage cost energy (meaning they align well)
            self.A = [
                [1.0, -0.4, 0.1],  # slippage vs urgency, budget
                [-0.4, 1.0, -0.3], # urgency vs slippage, budget
                [0.1, -0.3, 1.0],  # budget vs slippage, urgency
            ]

    def energy(self, features: Mapping[str, float]) -> float:
        x = [features.get(f, 0.0) for f in self.features]
        n = len(x)
        total = 0.0
        for i in range(n):
            for j in range(n):
                total += self.A[i][j] * x[i] * x[j]
        return total * 5.0

class AutoTraderCompositionalPolicy:
    """The global AutoTrader policy composed of multiple kernels."""
    def __init__(self, kernels: list[tuple[PolicyKernel, float]]):
        self.kernels = list(kernels)

    def total_energy(self, features: Mapping[str, float]) -> float:
        return sum(weight * k.energy(features) for k, weight in self.kernels)

class DynamicLagrangeMultiplierPolicy:
    """A policy wrapper that dynamically scales constraint kernels when violations are detected."""
    def __init__(self, base_policy: AutoTraderCompositionalPolicy, violation_keys: tuple[str, ...] = ("slippage_violation_flag", "budget_violation_flag")):
        self.base_policy = base_policy
        self.violation_keys = violation_keys

    def total_energy(self, features: Mapping[str, float]) -> float:
        energy = self.base_policy.total_energy(features)

        # Dynamically scale constraint weight if any violation flag is high
        for vk in self.violation_keys:
            if features.get(vk, 0.0) > 0.5:
                # Pareto alignment bump: multiply total energy penalty
                energy += 500.0
        return energy
