"""
Gemini Langevin Discovery: Gradient-based candidate refinement.
Uses Finite Differences to propagate MLP energy gradients back to discrete settlement fills.
"""

from __future__ import annotations

import random
from dataclasses import dataclass
from typing import Sequence

from internal.Gemini.crossed_features import extract_gemini_features
from internal.Gemini.gemini_mlp_model import MlpEnergyModel
from internal.Gemini.zeno_guard_model import ZenoGuardModel
from src.core.uniform_batch_clearing import (
    UniformBatchCertificateV1,
    UniformBatchFillV1,
    verify_uniform_batch_certificate_v1,
)
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.state.balances import BalanceTable
from src.state.intents import Intent
from src.state.pools import PoolState


@dataclass(frozen=True)
class LangevinDiscoveryResult:
    """Verifier-checked result for one Langevin proposal."""

    seed: UniformBatchCertificateV1
    refined: UniformBatchCertificateV1
    selected: UniformBatchCertificateV1 | None
    seed_energy: float
    refined_energy: float
    seed_verifier_ok: bool
    refined_verifier_ok: bool
    seed_verifier_error: str | None
    refined_verifier_error: str | None
    accepted_refinement: bool
    fallback_to_seed: bool
    model_authorizes_settlement: bool = False


class LangevinDiscovery:
    """Propose UPBA candidates using a learned energy landscape.

    The returned proposal is untrusted. Deterministic verification decides
    whether the refinement can be selected.
    """

    def __init__(
        self,
        mlp: MlpEnergyModel,
        guard: ZenoGuardModel,
        guard_weight: float = 50.0,
        lr: float = 1.0,
        steps: int = 10,
        eps: float = 1e-4,
        noise_scale: float = 0.1,
        random_seed: int = 20260519,
    ) -> None:
        self.mlp = mlp
        self.guard = guard
        self.guard_weight = guard_weight
        self.lr = lr
        self.steps = steps
        self.eps = eps
        self.noise_scale = noise_scale
        self.random_seed = random_seed

    def discover(
        self,
        *,
        pool: PoolState,
        intents: Sequence[Intent],
        balances: BalanceTable,
        seed: UniformBatchCertificateV1,
    ) -> UniformBatchCertificateV1:
        """Return an untrusted lower-energy proposal when search succeeds."""

        rng = random.Random(self.random_seed)
        current_fills = {f.intent_id: int(f.executed_in) for f in seed.fills}
        intents_by_id = {i.intent_id: i for i in intents}

        for _step in range(self.steps):
            grads = {}
            # Base Energy
            base_energy = self._total_energy(pool, intents, balances, seed, current_fills)

            # Numeric Gradient for each fill
            for intent_id, val in current_fills.items():
                intent = intents_by_id.get(intent_id)
                if not intent:
                    continue

                # Small perturbation
                perturbed_fills = current_fills.copy()
                perturbed_fills[intent_id] = val + 1 # Delta of 1 unit

                perturbed_energy = self._total_energy(pool, intents, balances, seed, perturbed_fills)

                # Gradient dE/dfill
                grads[intent_id] = (perturbed_energy - base_energy)

            # Langevin Step: fill = fill - lr * grad + noise
            for intent_id, grad in grads.items():
                noise = rng.normalvariate(0, self.noise_scale)
                move = -self.lr * grad + noise

                # Update and Clamp
                new_val = int(current_fills[intent_id] + move)

                # Physical Constraints
                intent = intents_by_id[intent_id]
                max_val = min(intent.get_field("amount_in"), balances.get(intent.sender_pubkey, intent.get_field("asset_in")))

                current_fills[intent_id] = max(0, min(max_val, new_val))

        # Re-canonicalize the final candidate
        return self._rebuild_candidate(seed, current_fills)

    def discover_verified(
        self,
        *,
        pool: PoolState,
        intents: Sequence[Intent],
        balances: BalanceTable,
        seed: UniformBatchCertificateV1,
    ) -> LangevinDiscoveryResult:
        """Return a verifier-checked selection for one untrusted refinement."""

        seed_fills = {f.intent_id: int(f.executed_in) for f in seed.fills}
        seed_energy = self._total_energy(pool, intents, balances, seed, seed_fills)
        refined = self.discover(pool=pool, intents=intents, balances=balances, seed=seed)
        refined_fills = {f.intent_id: int(f.executed_in) for f in refined.fills}
        refined_energy = self._total_energy(
            pool,
            intents,
            balances,
            refined,
            refined_fills,
        )
        seed_verdict = verify_uniform_batch_certificate_v1(
            intents=intents,
            pool=pool,
            balances=balances,
            certificate=seed,
        )
        refined_verdict = verify_uniform_batch_certificate_v1(
            intents=intents,
            pool=pool,
            balances=balances,
            certificate=refined,
        )
        accepted_refinement = bool(refined_verdict.ok and refined_energy < seed_energy)
        fallback_to_seed = bool(not accepted_refinement and seed_verdict.ok)
        selected = refined if accepted_refinement else seed if fallback_to_seed else None
        return LangevinDiscoveryResult(
            seed=seed,
            refined=refined,
            selected=selected,
            seed_energy=seed_energy,
            refined_energy=refined_energy,
            seed_verifier_ok=bool(seed_verdict.ok),
            refined_verifier_ok=bool(refined_verdict.ok),
            seed_verifier_error=seed_verdict.error,
            refined_verifier_error=refined_verdict.error,
            accepted_refinement=accepted_refinement,
            fallback_to_seed=fallback_to_seed,
        )

    def _total_energy(self, pool, intents, balances, seed, fills_map) -> float:
        candidate = self._rebuild_candidate(seed, fills_map)
        record = extract_upba_v2_feature_record(
            pool=pool,
            intents=intents,
            balances=balances,
            candidate=candidate,
            include_verifier_label=False,
        )
        x = extract_gemini_features(record.values)

        quality_e = self.mlp.energy(x)
        valid_p = self.guard.predict_proba(x)

        return quality_e + (1.0 - valid_p) * self.guard_weight

    def _rebuild_candidate(self, seed: UniformBatchCertificateV1, fills_map: dict[str, int]) -> UniformBatchCertificateV1:
        # Note: In a real implementation, we'd also need to re-estimate
        # the optimal uniform price based on these new fills.
        # For this prototype, we keep the seed's price.
        new_fills = []
        for f in seed.fills:
            executed_in = fills_map.get(f.intent_id, 0)
            # Roughly estimate output using seed price
            executed_out = (executed_in * seed.price_num) // seed.price_den if seed.price_den > 0 else 0
            new_fills.append(UniformBatchFillV1(
                intent_id=f.intent_id,
                executed_in=executed_in,
                executed_out=executed_out
            ))

        return UniformBatchCertificateV1(
            pool_id=seed.pool_id,
            base_asset=seed.base_asset,
            quote_asset=seed.quote_asset,
            pool_state_hash=seed.pool_state_hash,
            intent_set_hash=seed.intent_set_hash,
            price_num=seed.price_num,
            price_den=seed.price_den,
            fills=tuple(new_fills),
            policy_id=seed.policy_id,
            price_objective_id=seed.price_objective_id,
            schema=seed.schema
        )
