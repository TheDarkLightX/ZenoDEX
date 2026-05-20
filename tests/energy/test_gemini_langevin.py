from __future__ import annotations

from random import Random

from internal.Gemini.gemini_mlp_model import load_mlp_model
from internal.Gemini.langevin_discovery import LangevinDiscovery
from internal.Gemini.zeno_guard_model import load_guard_model
from src.core.uniform_batch_clearing import verify_uniform_batch_certificate_v1
from src.energy.upba_v2_ranker import verify_candidates_in_order
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def test_langevin_discovery_is_verifier_checked_before_selection() -> None:
    batch = generate_synthetic_batch(
        rng=Random(20260580),
        batch_index=0,
        target_candidate_count=32,
    )
    verified = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=[item.candidate for item in batch.candidates],
    )
    seed = next(result.candidate for result in verified if result.ok and result.candidate.fills)
    explorer = LangevinDiscovery(
        load_mlp_model("internal/Gemini/gemini_mlp_v6_final.json"),
        load_guard_model("internal/Gemini/zeno_guard_v1.json"),
        lr=10.0,
        steps=5,
        random_seed=20260519,
    )

    result = explorer.discover_verified(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        seed=seed,
    )

    assert result.model_authorizes_settlement is False
    assert result.seed_verifier_ok is True
    assert result.selected is not None
    selected_verdict = verify_uniform_batch_certificate_v1(
        intents=batch.intents,
        pool=batch.pool,
        balances=batch.balances,
        certificate=result.selected,
    )
    assert selected_verdict.ok is True
    if not result.refined_verifier_ok:
        assert result.accepted_refinement is False
        assert result.fallback_to_seed is True
        assert result.selected == seed
