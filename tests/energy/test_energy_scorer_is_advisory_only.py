from __future__ import annotations

from pathlib import Path
from random import Random

from src.energy.upba_v2_ranker import (
    advisory_candidate_hash,
    candidate_orders_are_hash_permutation,
    rank_upba_v2_candidates,
    search_best_with_deterministic_fallback,
    verified_checked_stop_certificate_holds,
    verify_candidates_in_order,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from src.state.state_root import compute_state_root
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def test_model_cannot_accept_invalid_settlement_even_when_ranked_first() -> None:
    batch = generate_synthetic_batch(rng=Random(301), batch_index=0, target_candidate_count=12)
    candidates = [item.candidate for item in batch.candidates]
    invalid = next(item.candidate for item in batch.candidates if item.candidate_type == "invalid_negative_reserve")
    invalid_hash = advisory_candidate_hash(invalid)

    def adversarial_scorer(candidate) -> float:
        return -1_000_000.0 if advisory_candidate_hash(candidate) == invalid_hash else 0.0

    ranked = rank_upba_v2_candidates(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=candidates,
        scorer=adversarial_scorer,
    )
    first_result = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=[ranked[0].candidate],
    )[0]

    assert advisory_candidate_hash(ranked[0].candidate) == invalid_hash
    assert first_result.ok is False


def test_ranker_preserves_candidate_hash_multiset() -> None:
    batch = generate_synthetic_batch(rng=Random(304), batch_index=0, target_candidate_count=12)
    candidates = [item.candidate for item in batch.candidates]
    ranked = rank_upba_v2_candidates(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=candidates,
        scorer=lambda candidate: float(int(advisory_candidate_hash(candidate)[2:10], 16)),
    )
    ordered = [item.candidate for item in ranked]

    assert candidate_orders_are_hash_permutation(candidates, ordered)
    assert not candidate_orders_are_hash_permutation(candidates, ordered[1:])
    assert not candidate_orders_are_hash_permutation(candidates, ordered + [ordered[0]])


def test_search_best_uses_verifier_objective_after_reordering() -> None:
    batch = generate_synthetic_batch(rng=Random(302), batch_index=0, target_candidate_count=12)
    candidates = [item.candidate for item in batch.candidates]
    exhaustive_best = search_best_with_deterministic_fallback(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=candidates,
        scorer=None,
    ).best

    reversed_order_best = search_best_with_deterministic_fallback(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=candidates,
        scorer=lambda candidate: -float(int(advisory_candidate_hash(candidate)[2:10], 16)),
    ).best

    assert exhaustive_best is not None
    assert reversed_order_best is not None
    assert reversed_order_best.certificate_hash == exhaustive_best.certificate_hash


def test_search_report_records_permutation_ok() -> None:
    batch = generate_synthetic_batch(rng=Random(305), batch_index=0, target_candidate_count=12)
    report = search_best_with_deterministic_fallback(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=[item.candidate for item in batch.candidates],
        scorer=lambda candidate: -float(int(advisory_candidate_hash(candidate)[2:10], 16)),
        top_k=5,
    )

    assert report.permutation_ok is True


def test_verified_checked_stop_certificate_holds_for_exhaustive_winner() -> None:
    batch = generate_synthetic_batch(rng=Random(306), batch_index=0, target_candidate_count=12)
    results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=[item.candidate for item in batch.candidates],
    )
    winner = max(
        (result for result in results if result.ok),
        key=lambda result: (result.volume, result.surplus, result.certificate_hash),
    )
    winner_index = next(index for index, result in enumerate(results) if result.certificate_hash == winner.certificate_hash)

    assert verified_checked_stop_certificate_holds(
        winner=winner,
        checked=results[: winner_index + 1],
        suffix=results[winner_index + 1 :],
    )


def test_verified_checked_stop_certificate_rejects_nonwinner_when_better_suffix_exists() -> None:
    batch = generate_synthetic_batch(rng=Random(307), batch_index=0, target_candidate_count=24)
    results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=[item.candidate for item in batch.candidates],
    )
    accepted = sorted(
        (result for result in results if result.ok),
        key=lambda result: (result.volume, result.surplus, result.certificate_hash),
    )
    assert len(accepted) >= 2
    weaker = accepted[0]
    stronger = accepted[-1]

    assert not verified_checked_stop_certificate_holds(
        winner=weaker,
        checked=[weaker],
        suffix=[stronger],
    )


def test_model_output_not_in_state_root() -> None:
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id = compute_pool_id(asset0, asset1, 30)
    pubkey = "0x" + "04" * 48
    balances = BalanceTable()
    balances.set(pubkey, asset0, 1_000)
    pool = PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=1_000,
        reserve1=1_000,
        fee_bps=30,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
    )

    root_before = compute_state_root(balances=balances, pools={pool_id: pool}, lp_balances=LPTable())
    batch = generate_synthetic_batch(rng=Random(303), batch_index=0, target_candidate_count=12)
    rank_upba_v2_candidates(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=[item.candidate for item in batch.candidates],
    )
    root_after = compute_state_root(balances=balances, pools={pool_id: pool}, lp_balances=LPTable())

    assert root_after == root_before


def test_core_verifier_modules_do_not_import_energy_package() -> None:
    root = Path(__file__).resolve().parents[2]
    core_files = list((root / "src" / "core").glob("*.py"))

    offenders = [
        path.name
        for path in core_files
        if "src.energy" in path.read_text(encoding="utf-8") or "from src import energy" in path.read_text(encoding="utf-8")
    ]

    assert offenders == []
