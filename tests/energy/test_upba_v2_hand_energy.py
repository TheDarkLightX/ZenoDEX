from __future__ import annotations

from random import Random

from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import (
    hard_barrier_energy_from_record,
    hand_energy_breakdown_from_record,
    hand_energy_from_record,
    primary_energy_failure_from_record,
    score_upba_v2_hand_energy,
)
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def test_hand_energy_penalizes_invalid_candidate_above_valid_candidate() -> None:
    batch = generate_synthetic_batch(rng=Random(201), batch_index=0, target_candidate_count=12)
    valid = next(item.candidate for item in batch.candidates if item.candidate_type.startswith("valid"))
    invalid = next(
        item.candidate
        for item in batch.candidates
        if item.candidate_type in {"invalid_negative_reserve", "invalid_all_zero"}
    )

    valid_energy = score_upba_v2_hand_energy(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=valid,
    )
    invalid_energy = score_upba_v2_hand_energy(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=invalid,
    )

    assert invalid_energy > valid_energy
    assert invalid_energy >= 100_000


def test_hand_energy_is_deterministic_for_same_feature_record() -> None:
    batch = generate_synthetic_batch(rng=Random(202), batch_index=0, target_candidate_count=12)
    candidate = batch.candidates[0].candidate
    record = extract_upba_v2_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=candidate,
        include_verifier_label=False,
    )

    assert hand_energy_from_record(record) == hand_energy_from_record(record)


def test_hand_energy_breakdown_localizes_hard_invalid_candidate() -> None:
    batch = generate_synthetic_batch(rng=Random(203), batch_index=0, target_candidate_count=32)
    candidate = next(
        item.candidate
        for item in batch.candidates
        if item.candidate_type == "hard_attractive_output_mismatch"
    )
    record = extract_upba_v2_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=candidate,
        include_verifier_label=True,
    )
    breakdown = hand_energy_breakdown_from_record(record)

    assert record.raw["verifier_ok"] is False
    assert breakdown["output_mismatch"] > 0
    assert hand_energy_from_record(record) == sum(breakdown.values())
    assert primary_energy_failure_from_record(record) in {
        "cpmm_invariant_violation",
        "noncanonical_fill_vector",
        "output_mismatch",
    }


def test_hard_barrier_energy_excludes_soft_objective_terms() -> None:
    batch = generate_synthetic_batch(rng=Random(204), batch_index=0, target_candidate_count=12)
    candidate = next(item.candidate for item in batch.candidates if item.candidate_type.startswith("valid"))
    record = extract_upba_v2_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=candidate,
        include_verifier_label=False,
    )
    breakdown = hand_energy_breakdown_from_record(record)
    soft_terms = {"dust", "imbalance", "executed_volume_reward", "surplus_reward"}
    expected_barrier = sum(value for name, value in breakdown.items() if name not in soft_terms)

    assert hard_barrier_energy_from_record(record) == expected_barrier
