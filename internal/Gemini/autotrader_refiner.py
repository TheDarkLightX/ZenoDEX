"""AutoTrader intent refiner for bounded advisory proposal search.

The refiner proposes feature changes. A deterministic policy guard must check
the proposal before selection.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
import json
import math
import random
from typing import Any, Callable, Mapping

from internal.Gemini.autotrader_compositional_policy import AutoTraderCompositionalPolicy


AUTOTRADER_REFINABLE_FEATURES: tuple[str, ...] = (
    "slippage_bps_norm",
    "execution_urgency_norm",
    "budget_used_norm",
)


@dataclass(frozen=True)
class AutoTraderRefinementResult:
    """Policy-checked result for one AutoTrader refinement proposal."""

    initial_features: dict[str, float]
    refined_features: dict[str, float]
    selected_features: dict[str, float]
    initial_energy: float
    refined_energy: float
    selected_energy: float
    initial_valid: bool
    refined_valid: bool
    selected_valid: bool
    initial_objective: float
    refined_objective: float
    selected_objective: float
    accepted_refinement: bool
    fallback_to_seed: bool
    decision: str
    policy_guards_authoritative: bool = True
    model_authorizes_trade: bool = False

    def to_dict(self) -> dict[str, Any]:
        return {
            "initial_features": self.initial_features,
            "refined_features": self.refined_features,
            "selected_features": self.selected_features,
            "initial_energy": self.initial_energy,
            "refined_energy": self.refined_energy,
            "selected_energy": self.selected_energy,
            "initial_valid": self.initial_valid,
            "refined_valid": self.refined_valid,
            "selected_valid": self.selected_valid,
            "initial_objective": self.initial_objective,
            "refined_objective": self.refined_objective,
            "selected_objective": self.selected_objective,
            "accepted_refinement": self.accepted_refinement,
            "fallback_to_seed": self.fallback_to_seed,
            "decision": self.decision,
            "policy_guards_authoritative": self.policy_guards_authoritative,
            "model_authorizes_trade": self.model_authorizes_trade,
        }


class AutoTraderIntentRefiner:
    """Refines trade parameters to propose lower-energy candidate features."""

    def __init__(
        self,
        policy: AutoTraderCompositionalPolicy,
        lr: float = 0.01,
        steps: int = 20,
        *,
        random_seed: int = 0,
        noise_scale: float = 0.001,
        refinable_features: tuple[str, ...] = AUTOTRADER_REFINABLE_FEATURES,
        momentum_decay: float = 0.0,
        precondition_decay: float = 0.0,
        barrier_mu: float = 0.0,
    ):
        self.policy = policy
        self.lr = float(lr)
        self.steps = int(steps)
        self.random_seed = int(random_seed)
        self.noise_scale = float(noise_scale)
        self.refinable_features = tuple(refinable_features)
        self.momentum_decay = float(momentum_decay)
        self.precondition_decay = float(precondition_decay)
        self.barrier_mu = float(barrier_mu)
        if self.lr <= 0.0:
            raise ValueError("lr must be positive")
        if self.steps < 0:
            raise ValueError("steps must be nonnegative")
        if self.noise_scale < 0.0:
            raise ValueError("noise_scale must be nonnegative")
        if not (0.0 <= self.momentum_decay < 1.0):
            raise ValueError("momentum_decay must be in [0, 1)")
        if not (0.0 <= self.precondition_decay < 1.0):
            raise ValueError("precondition_decay must be in [0, 1)")
        if self.barrier_mu < 0.0:
            raise ValueError("barrier_mu must be nonnegative")

    def refine_trade(self, initial_features: Mapping[str, float]) -> dict[str, float]:
        """Return an untrusted feature proposal after bounded Langevin steps."""

        rng = random.Random(self._seed_for_features(initial_features))
        current_features = dict(initial_features)

        # Initialize momentum velocities and running second moments
        velocities = {key: 0.0 for key in self.refinable_features}
        sq_gradients = {key: 0.0 for key in self.refinable_features}

        for _ in range(self.steps):
            grads = {}
            base_e = self.policy.total_energy(current_features)

            for key in self.refinable_features:
                if key not in current_features:
                    continue
                prev_val = current_features[key]
                current_features[key] = prev_val + 0.01
                new_e = self.policy.total_energy(current_features)
                estimated_grad = (new_e - base_e) / 0.01
                current_features[key] = prev_val

                # Apply soft barrier logarithmic constraints if active
                if self.barrier_mu > 0.0:
                    val = current_features[key]
                    eps_barrier = 1e-6
                    barrier_grad = self.barrier_mu * (1.0 / max(eps_barrier, 1.0 - val) - 1.0 / max(eps_barrier, val))
                    estimated_grad += barrier_grad

                grads[key] = estimated_grad

            for key, grad in grads.items():
                # Preconditioned factor (RMSprop-style second moment tracking)
                precond_factor = 1.0
                if self.precondition_decay > 0.0:
                    gamma = self.precondition_decay
                    sq_gradients[key] = gamma * sq_gradients[key] + (1.0 - gamma) * (grad ** 2)
                    precond_factor = 1.0 / (math.sqrt(sq_gradients[key]) + 1e-6)

                # Momentum-accelerated updates
                if self.momentum_decay > 0.0:
                    beta = self.momentum_decay
                    velocities[key] = beta * velocities[key] + (1.0 - beta) * precond_factor * grad
                    step_dir = velocities[key]
                else:
                    step_dir = precond_factor * grad

                # Preconditioned SGLD noise calculation
                noise_scale_adjusted = self.noise_scale * math.sqrt(2.0 * self.lr * precond_factor)
                noise = noise_scale_adjusted * rng.normalvariate(0.0, 1.0)

                new_val = current_features[key] - self.lr * step_dir + noise

                # Constraint projection: open-interval projection if barrier is active to prevent divide-by-zero
                if self.barrier_mu > 0.0:
                    current_features[key] = max(1e-5, min(1.0 - 1e-5, new_val))
                else:
                    current_features[key] = max(0.0, min(1.0, new_val))

        return current_features

    def refine_trade_checked(
        self,
        initial_features: Mapping[str, float],
        *,
        label_fn: Callable[[Mapping[str, float]], Mapping[str, Any]],
    ) -> AutoTraderRefinementResult:
        """Return a policy-checked selection for a refinement proposal.

        The refined proposal is selected only when it remains policy-valid,
        lowers energy, and does not reduce the deterministic objective.
        """

        initial = dict(initial_features)
        refined = self.refine_trade(initial)
        initial_label = label_fn(initial)
        refined_label = label_fn(refined)
        initial_valid = bool(initial_label.get("valid", False))
        refined_valid = bool(refined_label.get("valid", False))
        initial_objective = float(initial_label.get("objective", 0.0))
        refined_objective = float(refined_label.get("objective", 0.0))
        initial_energy = float(self.policy.total_energy(initial))
        refined_energy = float(self.policy.total_energy(refined))

        accepted = (
            refined_valid
            and refined_energy < initial_energy
            and refined_objective >= initial_objective
        )
        if accepted:
            selected = refined
            selected_energy = refined_energy
            selected_valid = refined_valid
            selected_objective = refined_objective
            decision = "accepted_policy_checked_refinement"
        else:
            selected = initial
            selected_energy = initial_energy
            selected_valid = initial_valid
            selected_objective = initial_objective
            decision = "fallback_to_policy_checked_seed"

        return AutoTraderRefinementResult(
            initial_features={key: float(value) for key, value in initial.items()},
            refined_features={key: float(value) for key, value in refined.items()},
            selected_features={key: float(value) for key, value in selected.items()},
            initial_energy=initial_energy,
            refined_energy=refined_energy,
            selected_energy=selected_energy,
            initial_valid=initial_valid,
            refined_valid=refined_valid,
            selected_valid=selected_valid,
            initial_objective=initial_objective,
            refined_objective=refined_objective,
            selected_objective=selected_objective,
            accepted_refinement=accepted,
            fallback_to_seed=not accepted,
            decision=decision,
        )

    def _seed_for_features(self, features: Mapping[str, float]) -> int:
        payload = json.dumps(
            {
                "random_seed": self.random_seed,
                "features": {
                    str(key): round(float(value), 8)
                    for key, value in sorted(features.items())
                },
            },
            sort_keys=True,
            separators=(",", ":"),
        )
        return int(sha256(payload.encode("utf-8")).hexdigest()[:16], 16)
