from __future__ import annotations

from random import Random

from src.core.uniform_batch_clearing import verify_uniform_batch_certificate_v1
from src.energy.upba_v2_neighborhood import (
    augment_candidates_with_neighborhood,
    propose_upba_v2_neighborhood,
)
from src.energy.upba_v2_ranker import advisory_candidate_hash
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def test_neighborhood_proposals_are_deterministic_and_unique() -> None:
    batch = generate_synthetic_batch(
        rng=Random(801),
        batch_index=0,
        target_candidate_count=16,
    )
    seed = batch.candidates[-1].candidate

    first = propose_upba_v2_neighborhood(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        seed_candidate=seed,
        max_proposals=10,
    )
    second = propose_upba_v2_neighborhood(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        seed_candidate=seed,
        max_proposals=10,
    )

    assert [proposal.candidate_hash for proposal in first] == [
        proposal.candidate_hash for proposal in second
    ]
    assert len({proposal.candidate_hash for proposal in first}) == len(first)
    assert all(proposal.source_hash == advisory_candidate_hash(seed) for proposal in first)


def test_neighborhood_can_repair_invalid_candidates_but_verifier_decides() -> None:
    batch = generate_synthetic_batch(
        rng=Random(802),
        batch_index=1,
        target_candidate_count=18,
    )
    invalid_seed = next(
        item.candidate
        for item in batch.candidates
        if not verify_uniform_batch_certificate_v1(
            intents=batch.intents,
            pool=batch.pool,
            balances=batch.balances,
            certificate=item.candidate,
        ).ok
    )

    proposals = propose_upba_v2_neighborhood(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        seed_candidate=invalid_seed,
        max_proposals=12,
    )
    verified = [
        verify_uniform_batch_certificate_v1(
            intents=batch.intents,
            pool=batch.pool,
            balances=batch.balances,
            certificate=proposal.candidate,
        )
        for proposal in proposals
    ]

    assert proposals
    assert any(result.ok for result in verified)
    assert all(result.ok or result.error for result in verified)


def test_neighborhood_augmentation_preserves_original_candidates_as_subset() -> None:
    batch = generate_synthetic_batch(
        rng=Random(803),
        batch_index=2,
        target_candidate_count=20,
    )
    original = tuple(item.candidate for item in batch.candidates[:5])

    augmented = augment_candidates_with_neighborhood(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=original,
        repair_seed_count=5,
        max_proposals_per_seed=4,
    )

    assert augmented.original_subset_ok
    assert augmented.candidates[: len(original)] == original
    assert set(augmented.original_hashes).issubset(set(augmented.augmented_hashes))
    assert len(set(augmented.augmented_hashes)) == len(augmented.augmented_hashes)
