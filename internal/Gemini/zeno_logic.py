"""ZenoLogic: compositional advisory energy operators.

These operators compose ranking energies. They do not create a formal proof
system, a verifier, or an authorization rule.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Mapping

class LogicalEnergy(ABC):
    @abstractmethod
    def energy(self, features: Mapping[str, float]) -> float:
        pass

class EnergyAtom(LogicalEnergy):
    """A base energy kernel."""
    def __init__(self, kernel, weight: float = 1.0):
        self.kernel = kernel
        self.weight = weight
    def energy(self, features: Mapping[str, float]) -> float:
        return self.weight * self.kernel.energy(features)

class EnergyAnd(LogicalEnergy):
    """Conjunction: Energy is the sum (log-space product)."""
    def __init__(self, e1: LogicalEnergy, e2: LogicalEnergy):
        self.e1 = e1
        self.e2 = e2
    def energy(self, features: Mapping[str, float]) -> float:
        return self.e1.energy(features) + self.e2.energy(features)

class EnergyNot(LogicalEnergy):
    """Diagnostic complement: flips a soft landscape.

    This operator must not be applied to hard safety barriers in a production
    policy, because it can make violations attractive.
    """
    def __init__(self, e: LogicalEnergy):
        self.e = e
    def energy(self, features: Mapping[str, float]) -> float:
        # We use a large constant to keep energy positive if desired
        return -self.e.energy(features)

class EnergyOr(LogicalEnergy):
    """Disjunction: Log-Sum-Exp (Smooth minimum energy)."""
    def __init__(self, e1: LogicalEnergy, e2: LogicalEnergy):
        self.e1 = e1
        self.e2 = e2
    def energy(self, features: Mapping[str, float]) -> float:
        import math
        v1 = self.e1.energy(features)
        v2 = self.e2.energy(features)
        # Stable soft-min: -log(exp(-v1) + exp(-v2)).
        m = min(v1, v2)
        return m - math.log(math.exp(-(v1 - m)) + math.exp(-(v2 - m)))
