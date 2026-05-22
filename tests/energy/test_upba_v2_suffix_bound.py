from __future__ import annotations

from random import Random

from src.energy.upba_v2_ranker import (
    deterministic_best_verified_candidate,
    verify_candidates_in_order,
)
from src.energy.upba_v2_suffix_bound import (
    SUFFIX_BOUND_SCHEMA,
    build_upba_v2_suffix_bound_certificate,
    candidate_objective_upper_bound,
    suffix_bound_cannot_beat,
    verify_upba_v2_suffix_bound_certificate,
)
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def test_objective_upper_bound_matches_verified_valid_candidate() -> None:
    batch, results = _batch_with_valid_candidates()
    valid = next(result for result in results if result.ok)

    bound = candidate_objective_upper_bound(
        valid.candidate,
        intents=batch.intents,
        pool=batch.pool,
        balances=batch.balances,
    )

    assert bound.volume_upper == valid.volume
    assert bound.surplus_upper == valid.surplus
    assert bound.disqualified is False
    assert suffix_bound_cannot_beat(valid, bound) is True


def test_objective_upper_bound_disqualifies_verifier_rejected_candidate() -> None:
    batch, results = _batch_with_valid_candidates()
    invalid = next(result for result in results if not result.ok)

    bound = candidate_objective_upper_bound(
        invalid.candidate,
        intents=batch.intents,
        pool=batch.pool,
        balances=batch.balances,
    )

    assert bound.disqualified is True
    assert bound.volume_upper == 0
    assert bound.surplus_upper == 0


def test_suffix_bound_certificate_passes_for_checked_winner_and_weak_suffix() -> None:
    batch, results = _batch_with_valid_candidates(min_valid=2)
    accepted = sorted(
        (result for result in results if result.ok),
        key=lambda result: (result.volume, result.surplus, result.certificate_hash),
    )
    weak = accepted[0]
    winner = accepted[-1]

    report = build_upba_v2_suffix_bound_certificate(
        checked_results=(winner,),
        unchecked_candidates=(weak.candidate,),
        full_candidates=(winner.candidate, weak.candidate),
        intents=batch.intents,
        pool=batch.pool,
        balances=batch.balances,
        full_list_complete_for_claim=True,
        scope="unit-test-suffix-bound",
    )

    assert report["schema"] == SUFFIX_BOUND_SCHEMA
    assert report["ok"] is True
    assert report["global_claim_ok"] is True
    assert report["checked_count"] == 1
    assert report["unchecked_count"] == 1
    assert verify_upba_v2_suffix_bound_certificate(report) is True


def test_suffix_bound_certificate_rejects_attractive_unchecked_candidate() -> None:
    batch, results = _batch_with_valid_candidates()
    winner = deterministic_best_verified_candidate(results)
    assert winner is not None
    attractive = max(
        (item.candidate for item in batch.candidates if not _is_candidate_ok(item.candidate, results)),
        key=lambda candidate: candidate_objective_upper_bound(
            candidate,
            intents=batch.intents,
        ).volume_upper,
    )

    report = build_upba_v2_suffix_bound_certificate(
        checked_results=(winner,),
        unchecked_candidates=(attractive,),
        full_candidates=(winner.candidate, attractive),
        intents=batch.intents,
        full_list_complete_for_claim=True,
        scope="unit-test-suffix-bound",
    )

    assert report["ok"] is False
    assert report["suffix_bound_ok"] is False
    assert verify_upba_v2_suffix_bound_certificate(report) is False


def test_suffix_bound_certificate_rejects_nonpartitioned_list() -> None:
    batch, results = _batch_with_valid_candidates(min_valid=2)
    accepted = [result for result in results if result.ok]
    winner = max(accepted, key=lambda result: (result.volume, result.surplus, result.certificate_hash))
    weak = min(accepted, key=lambda result: (result.volume, result.surplus, result.certificate_hash))

    report = build_upba_v2_suffix_bound_certificate(
        checked_results=(winner,),
        unchecked_candidates=(weak.candidate,),
        full_candidates=(winner.candidate,),
        intents=batch.intents,
        full_list_complete_for_claim=True,
        scope="unit-test-suffix-bound",
    )

    assert report["ok"] is False
    assert report["partition_ok"] is False
    assert verify_upba_v2_suffix_bound_certificate(report) is False


def _batch_with_valid_candidates(*, min_valid: int = 1):
    for seed in range(900, 930):
        batch = generate_synthetic_batch(
            rng=Random(seed),
            batch_index=0,
            target_candidate_count=20,
        )
        results = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=tuple(item.candidate for item in batch.candidates),
        )
        if sum(1 for result in results if result.ok) >= min_valid:
            return batch, results
    raise AssertionError("expected synthetic batch with enough valid candidates")


def _is_candidate_ok(candidate, results) -> bool:
    return any(result.ok and result.candidate == candidate for result in results)
