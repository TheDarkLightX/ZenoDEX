from __future__ import annotations

from random import Random

from src.energy.upba_v2_energy_model import LinearEnergyModel
from src.energy.upba_v2_neighborhood import augment_candidates_with_neighborhood
from src.energy.upba_v2_ranker import advisory_candidate_hash
from src.energy.upba_v2_repair_selector import (
    REPAIR_SELECTOR_FEATURE_DIM,
    REPAIR_SELECTOR_FEATURE_NAMES,
    extract_upba_v2_repair_selector_features,
    rank_repair_proposals,
)
from tools.benchmark_upba_repair_selector import train_and_evaluate_repair_selector
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def test_repair_selector_features_are_deterministic_and_label_free() -> None:
    batch = generate_synthetic_batch(
        rng=Random(811),
        batch_index=0,
        target_candidate_count=16,
    )
    source = batch.candidates[-1].candidate
    augmentation = augment_candidates_with_neighborhood(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=(source,),
        repair_seed_count=1,
        max_proposals_per_seed=4,
    )

    first = extract_upba_v2_repair_selector_features(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        source_candidate=source,
        proposal=augmentation.proposals[0],
        source_rank=0,
        source_count=1,
        proposal_index=0,
        proposal_count=len(augmentation.proposals),
    )
    second = extract_upba_v2_repair_selector_features(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        source_candidate=source,
        proposal=augmentation.proposals[0],
        source_rank=0,
        source_count=1,
        proposal_index=0,
        proposal_count=len(augmentation.proposals),
    )

    assert first == second
    assert first.feature_names == REPAIR_SELECTOR_FEATURE_NAMES
    assert len(first.values) == REPAIR_SELECTOR_FEATURE_DIM
    assert first.raw["feature_schema"] == "zenodex/energy/upba_v2_repair_selector_features/v1"
    assert "verifier_ok" not in first.raw
    assert "verifier_error" not in first.raw


def test_rank_repair_proposals_is_deterministic_with_hash_tiebreak() -> None:
    batch = generate_synthetic_batch(
        rng=Random(812),
        batch_index=1,
        target_candidate_count=16,
    )
    candidates = tuple(item.candidate for item in batch.candidates[:3])
    augmentation = augment_candidates_with_neighborhood(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=candidates,
        repair_seed_count=3,
        max_proposals_per_seed=3,
    )
    source_candidates_by_hash = {advisory_candidate_hash(candidate): candidate for candidate in candidates}
    source_ranks_by_hash = {
        advisory_candidate_hash(candidate): index for index, candidate in enumerate(candidates)
    }
    model = LinearEnergyModel(
        feature_names=REPAIR_SELECTOR_FEATURE_NAMES,
        weights=(0.0,) * REPAIR_SELECTOR_FEATURE_DIM,
    )

    first = rank_repair_proposals(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        proposals=augmentation.proposals,
        source_candidates_by_hash=source_candidates_by_hash,
        source_ranks_by_hash=source_ranks_by_hash,
        model=model,
    )
    second = rank_repair_proposals(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        proposals=augmentation.proposals,
        source_candidates_by_hash=source_candidates_by_hash,
        source_ranks_by_hash=source_ranks_by_hash,
        model=model,
    )

    assert [proposal.candidate_hash for proposal in first] == [
        proposal.candidate_hash for proposal in second
    ]
    assert [proposal.candidate_hash for proposal in first] == sorted(
        proposal.candidate_hash for proposal in augmentation.proposals
    )


def test_repair_selector_benchmark_smoke_keeps_verifier_authoritative() -> None:
    report, model = train_and_evaluate_repair_selector(
        train_batches=2,
        holdout_batches=2,
        candidates_per_batch=12,
        candidate_budget=4,
        proposal_budget=2,
        repair_seed_count=2,
        max_proposals_per_seed=3,
        step_denominator=4,
        epochs=1,
        learning_rate=0.05,
        margin=1.0,
        train_seed=813,
        holdout_seed=814,
    )

    assert model.feature_names == REPAIR_SELECTOR_FEATURE_NAMES
    assert report["feature_dim"] == REPAIR_SELECTOR_FEATURE_DIM
    assert set(report["modes"]) == {
        "limited",
        "full_neighborhood",
        "hand_selected",
        "learned_selected",
    }
    assert report["safety"]["invalid_accept_count"] == 0
    assert report["safety"]["verifier_authoritative"] is True
