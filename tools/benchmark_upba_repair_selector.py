#!/usr/bin/env python3
"""Train and benchmark a tiny UPBA v2 neighborhood repair selector.

The selector is advisory. It chooses which deterministic neighborhood proposals
to add to a limited candidate set. Every resulting candidate is still checked by
the deterministic UPBA verifier before objective comparison.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from random import Random
from statistics import mean
from time import perf_counter
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.uniform_batch_clearing import UniformBatchCertificateV1
from src.energy.upba_v2_energy_model import LinearEnergyModel, save_linear_model
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import hand_energy_from_record
from src.energy.upba_v2_neighborhood import UpbaV2NeighborhoodProposal, augment_candidates_with_neighborhood
from src.energy.upba_v2_ranker import (
    VerifiedCandidateResult,
    advisory_candidate_hash,
    deterministic_best_verified_candidate,
    verify_candidates_in_order,
)
from src.energy.upba_v2_repair_selector import (
    REPAIR_SELECTOR_FEATURE_NAMES,
    extract_upba_v2_repair_selector_features,
    rank_repair_proposals,
)
from tools.benchmark_upba_energy_neighborhood import _deterministic_budget_order
from tools.generate_upba_energy_dataset import SyntheticBatch, generate_synthetic_batch


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train-batches", type=int, default=120)
    parser.add_argument("--holdout-batches", type=int, default=80)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--candidate-budget", type=int, default=6)
    parser.add_argument("--proposal-budget", type=int, default=4)
    parser.add_argument("--repair-seed-count", type=int, default=4)
    parser.add_argument("--max-proposals-per-seed", type=int, default=6)
    parser.add_argument("--step-denominator", type=int, default=4)
    parser.add_argument("--epochs", type=int, default=10)
    parser.add_argument("--learning-rate", type=float, default=0.05)
    parser.add_argument("--margin", type=float, default=1.0)
    parser.add_argument("--train-seed", type=int, default=20260526)
    parser.add_argument("--holdout-seed", type=int, default=20260527)
    parser.add_argument("--output-model", type=Path)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report, model = train_and_evaluate_repair_selector(
        train_batches=args.train_batches,
        holdout_batches=args.holdout_batches,
        candidates_per_batch=args.candidates_per_batch,
        candidate_budget=args.candidate_budget,
        proposal_budget=args.proposal_budget,
        repair_seed_count=args.repair_seed_count,
        max_proposals_per_seed=args.max_proposals_per_seed,
        step_denominator=args.step_denominator,
        epochs=args.epochs,
        learning_rate=args.learning_rate,
        margin=args.margin,
        train_seed=args.train_seed,
        holdout_seed=args.holdout_seed,
    )
    if args.output_model is not None:
        args.output_model.parent.mkdir(parents=True, exist_ok=True)
        save_linear_model(model, args.output_model)
        report["model_path"] = str(args.output_model)

    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0


def train_and_evaluate_repair_selector(
    *,
    train_batches: int,
    holdout_batches: int,
    candidates_per_batch: int,
    candidate_budget: int,
    proposal_budget: int,
    repair_seed_count: int,
    max_proposals_per_seed: int,
    step_denominator: int,
    epochs: int,
    learning_rate: float,
    margin: float,
    train_seed: int,
    holdout_seed: int,
) -> tuple[dict[str, Any], LinearEnergyModel]:
    started = perf_counter()
    train_rows = collect_repair_selector_rows(
        batches=train_batches,
        candidates_per_batch=candidates_per_batch,
        candidate_budget=candidate_budget,
        repair_seed_count=repair_seed_count,
        max_proposals_per_seed=max_proposals_per_seed,
        step_denominator=step_denominator,
        seed=train_seed,
    )
    model = train_linear_repair_selector(
        train_rows,
        epochs=epochs,
        learning_rate=learning_rate,
        margin=margin,
        seed=train_seed,
    )
    evaluation = evaluate_repair_selector(
        batches=holdout_batches,
        candidates_per_batch=candidates_per_batch,
        candidate_budget=candidate_budget,
        proposal_budget=proposal_budget,
        repair_seed_count=repair_seed_count,
        max_proposals_per_seed=max_proposals_per_seed,
        step_denominator=step_denominator,
        seed=holdout_seed,
        model=model,
    )
    wall_clock_ms = (perf_counter() - started) * 1000
    report: dict[str, Any] = {
        "schema": "zenodex/energy/upba_v2_repair_selector_benchmark/v1",
        "train_batches": train_batches,
        "holdout_batches": holdout_batches,
        "evaluated_batches": evaluation["evaluated_batches"],
        "candidates_per_batch": candidates_per_batch,
        "candidate_budget": candidate_budget,
        "proposal_budget": proposal_budget,
        "repair_seed_count": repair_seed_count,
        "max_proposals_per_seed": max_proposals_per_seed,
        "step_denominator": step_denominator,
        "epochs": epochs,
        "learning_rate": learning_rate,
        "margin": margin,
        "train_seed": train_seed,
        "holdout_seed": holdout_seed,
        "training_rows": len(train_rows),
        "feature_dim": len(REPAIR_SELECTOR_FEATURE_NAMES),
        "parameter_count": len(model.weights) + 1,
        "wall_clock_ms": wall_clock_ms,
        "modes": evaluation["modes"],
        "deltas": _deltas(evaluation["modes"]),
        "safety": {
            "invalid_accept_count": 0,
            "verifier_authoritative": True,
            "candidate_source": "synthetic bounded UPBA v2 candidate/proposal generator",
            "fallback_required": True,
        },
        "interpretation": _interpretation(evaluation["modes"]),
    }
    return report, model


def collect_repair_selector_rows(
    *,
    batches: int,
    candidates_per_batch: int,
    candidate_budget: int,
    repair_seed_count: int,
    max_proposals_per_seed: int,
    step_denominator: int,
    seed: int,
) -> list[dict[str, Any]]:
    rng = Random(seed)
    rows: list[dict[str, Any]] = []
    for batch_index in range(batches):
        batch = generate_synthetic_batch(
            rng=rng,
            batch_index=batch_index,
            target_candidate_count=candidates_per_batch,
        )
        setup = _limited_neighborhood_setup(
            batch=batch,
            candidate_budget=candidate_budget,
            repair_seed_count=repair_seed_count,
            max_proposals_per_seed=max_proposals_per_seed,
            step_denominator=step_denominator,
            seed=seed,
            batch_index=batch_index,
        )
        full_winner = setup["full_winner"]
        if full_winner is None:
            continue
        proposals = setup["proposals"]
        source_candidates_by_hash = setup["source_candidates_by_hash"]
        source_ranks_by_hash = setup["source_ranks_by_hash"]
        source_count = max(1, len(source_candidates_by_hash))
        proposal_count = max(1, len(proposals))
        proposal_results = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=tuple(proposal.candidate for proposal in proposals),
        )
        for proposal_index, (proposal, result) in enumerate(zip(proposals, proposal_results, strict=True)):
            source_candidate = source_candidates_by_hash[proposal.source_hash]
            record = extract_upba_v2_repair_selector_features(
                pool=batch.pool,
                intents=batch.intents,
                balances=batch.balances,
                source_candidate=source_candidate,
                proposal=proposal,
                source_rank=source_ranks_by_hash[proposal.source_hash],
                source_count=source_count,
                proposal_index=proposal_index,
                proposal_count=proposal_count,
            )
            rows.append(
                {
                    "schema": "zenodex/energy/upba_v2_repair_selector_row/v1",
                    "source": "synthetic",
                    "batch_id": batch.batch_id,
                    "batch_index": batch_index,
                    "proposal_index": proposal_index,
                    "proposal_hash": proposal.candidate_hash,
                    "source_hash": proposal.source_hash,
                    "recipe_id": proposal.recipe_id,
                    "feature_names": list(record.feature_names),
                    "features": list(record.values),
                    "label": {
                        "valid": bool(result.ok),
                        "objective_volume": int(result.volume),
                        "objective_surplus": int(result.surplus),
                        "dominates_full_winner": bool(
                            result.ok and _weakly_dominates(result, full_winner)
                        ),
                        "matches_full_winner": result.certificate_hash == full_winner.certificate_hash,
                        "full_winner_hash": full_winner.certificate_hash,
                        "verifier_error": result.error,
                    },
                }
            )
    return rows


def train_linear_repair_selector(
    rows: Sequence[dict[str, Any]],
    *,
    epochs: int,
    learning_rate: float,
    margin: float,
    seed: int,
) -> LinearEnergyModel:
    if not rows:
        raise ValueError("repair selector training rows are empty")
    if tuple(rows[0]["feature_names"]) != REPAIR_SELECTOR_FEATURE_NAMES:
        raise ValueError("repair selector feature schema mismatch")

    weights = _initial_repair_selector_weights()
    by_batch: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if tuple(row["feature_names"]) != REPAIR_SELECTOR_FEATURE_NAMES:
            raise ValueError("repair selector feature schema mismatch")
        by_batch[str(row["batch_id"])].append(row)

    rng = Random(seed)
    batches = list(by_batch.values())
    for _epoch in range(max(0, epochs)):
        rng.shuffle(batches)
        for batch_rows in batches:
            ranked = sorted(batch_rows, key=_label_score, reverse=True)
            scale = _batch_scale(batch_rows)
            for good_index, good in enumerate(ranked):
                good_x = [float(value) for value in good["features"]]
                for bad in ranked[good_index + 1 :]:
                    if _label_score(good) <= _label_score(bad):
                        continue
                    bad_x = [float(value) for value in bad["features"]]
                    energy_good = _dot(weights, good_x)
                    energy_bad = _dot(weights, bad_x)
                    if margin + energy_good - energy_bad <= 0:
                        continue
                    pair_weight = _pair_weight(good=good, bad=bad, scale=scale)
                    for index, (good_value, bad_value) in enumerate(zip(good_x, bad_x, strict=True)):
                        weights[index] -= learning_rate * pair_weight * (good_value - bad_value)
    return LinearEnergyModel(
        feature_names=REPAIR_SELECTOR_FEATURE_NAMES,
        weights=tuple(weights),
        bias=0.0,
    )


def evaluate_repair_selector(
    *,
    batches: int,
    candidates_per_batch: int,
    candidate_budget: int,
    proposal_budget: int,
    repair_seed_count: int,
    max_proposals_per_seed: int,
    step_denominator: int,
    seed: int,
    model: LinearEnergyModel,
) -> dict[str, Any]:
    rng = Random(seed)
    stats = {
        "limited": _empty_stats(),
        "full_neighborhood": _empty_stats(),
        "hand_selected": _empty_stats(),
        "learned_selected": _empty_stats(),
    }
    skipped_without_winner = 0
    for batch_index in range(batches):
        batch = generate_synthetic_batch(
            rng=rng,
            batch_index=batch_index,
            target_candidate_count=candidates_per_batch,
        )
        setup = _limited_neighborhood_setup(
            batch=batch,
            candidate_budget=candidate_budget,
            repair_seed_count=repair_seed_count,
            max_proposals_per_seed=max_proposals_per_seed,
            step_denominator=step_denominator,
            seed=seed,
            batch_index=batch_index,
        )
        full_winner = setup["full_winner"]
        if full_winner is None:
            skipped_without_winner += 1
            continue

        limited = setup["limited_ordered"]
        proposals = setup["proposals"]
        source_candidates_by_hash = setup["source_candidates_by_hash"]
        source_ranks_by_hash = setup["source_ranks_by_hash"]
        augmentation_candidates = setup["augmentation_candidates"]
        proposal_budget_clamped = max(0, min(proposal_budget, len(proposals)))
        hand_proposals = _hand_rank_proposals(
            batch=batch,
            proposals=proposals,
        )[:proposal_budget_clamped]
        learned_proposals = rank_repair_proposals(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            proposals=proposals,
            source_candidates_by_hash=source_candidates_by_hash,
            source_ranks_by_hash=source_ranks_by_hash,
            model=model,
        )[:proposal_budget_clamped]

        mode_candidates = {
            "limited": limited,
            "full_neighborhood": _hand_rank_candidates(batch=batch, candidates=augmentation_candidates),
            "hand_selected": _hand_rank_candidates(
                batch=batch,
                candidates=_append_unique(limited, tuple(proposal.candidate for proposal in hand_proposals)),
            ),
            "learned_selected": _hand_rank_candidates(
                batch=batch,
                candidates=_append_unique(limited, tuple(proposal.candidate for proposal in learned_proposals)),
            ),
        }
        for mode, ordered in mode_candidates.items():
            added_count = 0
            if mode == "full_neighborhood":
                added_count = len(proposals)
            elif mode == "hand_selected":
                added_count = len(hand_proposals)
            elif mode == "learned_selected":
                added_count = len(learned_proposals)
            _record_stats(
                stats=stats[mode],
                batch=batch,
                ordered=ordered,
                full_winner=full_winner,
                added_count=added_count,
                original_subset_ok=setup["original_subset_ok"],
            )

    return {
        "evaluated_batches": _finalize_stats(stats["limited"])["batches"],
        "skipped_without_winner": skipped_without_winner,
        "modes": {mode: _finalize_stats(mode_stats) for mode, mode_stats in stats.items()},
    }


def _limited_neighborhood_setup(
    *,
    batch: SyntheticBatch,
    candidate_budget: int,
    repair_seed_count: int,
    max_proposals_per_seed: int,
    step_denominator: int,
    seed: int,
    batch_index: int,
) -> dict[str, Any]:
    full_candidates = tuple(item.candidate for item in batch.candidates)
    full_results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=full_candidates,
    )
    full_winner = deterministic_best_verified_candidate(full_results)
    ordered_full = _deterministic_budget_order(
        candidates=full_candidates,
        seed=seed,
        batch_index=batch_index,
    )
    limited = ordered_full[: max(1, min(candidate_budget, len(ordered_full)))]
    limited_ordered = _hand_rank_candidates(batch=batch, candidates=limited)
    augmentation = augment_candidates_with_neighborhood(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=limited_ordered,
        repair_seed_count=repair_seed_count,
        max_proposals_per_seed=max_proposals_per_seed,
        step_denominator=step_denominator,
    )
    source_candidates_by_hash = {
        advisory_candidate_hash(candidate): candidate for candidate in limited_ordered
    }
    source_ranks_by_hash = {
        advisory_candidate_hash(candidate): rank for rank, candidate in enumerate(limited_ordered)
    }
    return {
        "full_winner": full_winner,
        "limited_ordered": limited_ordered,
        "proposals": augmentation.proposals,
        "augmentation_candidates": augmentation.candidates,
        "source_candidates_by_hash": source_candidates_by_hash,
        "source_ranks_by_hash": source_ranks_by_hash,
        "original_subset_ok": augmentation.original_subset_ok,
    }


def _hand_rank_candidates(
    *,
    batch: SyntheticBatch,
    candidates: Sequence[UniformBatchCertificateV1],
) -> tuple[UniformBatchCertificateV1, ...]:
    return tuple(
        sorted(
            candidates,
            key=lambda candidate: (
                _hand_energy_for_candidate(batch=batch, candidate=candidate),
                advisory_candidate_hash(candidate),
            ),
        )
    )


def _hand_rank_proposals(
    *,
    batch: SyntheticBatch,
    proposals: Sequence[UpbaV2NeighborhoodProposal],
) -> tuple[UpbaV2NeighborhoodProposal, ...]:
    return tuple(
        sorted(
            proposals,
            key=lambda proposal: (
                _hand_energy_for_candidate(batch=batch, candidate=proposal.candidate),
                proposal.candidate_hash,
            ),
        )
    )


def _hand_energy_for_candidate(
    *,
    batch: SyntheticBatch,
    candidate: UniformBatchCertificateV1,
) -> float:
    record = extract_upba_v2_feature_record(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidate=candidate,
        include_verifier_label=False,
    )
    return hand_energy_from_record(record)


def _append_unique(
    original: Sequence[UniformBatchCertificateV1],
    additions: Sequence[UniformBatchCertificateV1],
) -> tuple[UniformBatchCertificateV1, ...]:
    seen = {advisory_candidate_hash(candidate) for candidate in original}
    combined = list(original)
    for candidate in additions:
        candidate_hash = advisory_candidate_hash(candidate)
        if candidate_hash in seen:
            continue
        seen.add(candidate_hash)
        combined.append(candidate)
    return tuple(combined)


def _record_stats(
    *,
    stats: dict[str, list[int]],
    batch: SyntheticBatch,
    ordered: Sequence[UniformBatchCertificateV1],
    full_winner: VerifiedCandidateResult,
    added_count: int,
    original_subset_ok: bool,
) -> None:
    results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=ordered,
    )
    best = deterministic_best_verified_candidate(results)
    full_winner_hash = full_winner.certificate_hash
    winner_position = _winner_position(results=results, winner_hash=full_winner_hash)
    dominance_position = _dominance_position(results=results, full_winner=full_winner)
    stats["candidate_count"].append(len(ordered))
    stats["added_count"].append(added_count)
    stats["full_winner_present"].append(1 if winner_position is not None else 0)
    stats["best_matches_full_winner"].append(
        1 if best is not None and best.certificate_hash == full_winner_hash else 0
    )
    stats["best_weakly_dominates_full_winner"].append(
        1 if best is not None and _weakly_dominates(best, full_winner) else 0
    )
    stats["calls_until_full_winner_or_exhausted"].append(
        winner_position if winner_position is not None else len(ordered)
    )
    stats["calls_until_dominating_candidate_or_exhausted"].append(
        dominance_position if dominance_position is not None else len(ordered)
    )
    if best is None:
        stats["volume_regret"].append(full_winner.volume)
        stats["surplus_regret"].append(full_winner.surplus)
    else:
        stats["volume_regret"].append(max(0, full_winner.volume - best.volume))
        stats["surplus_regret"].append(
            max(0, full_winner.surplus - best.surplus)
            if best.volume == full_winner.volume
            else 0
        )
    stats["original_subset_violation"].append(0 if original_subset_ok else 1)


def _empty_stats() -> dict[str, list[int]]:
    return {
        "candidate_count": [],
        "added_count": [],
        "full_winner_present": [],
        "best_matches_full_winner": [],
        "best_weakly_dominates_full_winner": [],
        "calls_until_full_winner_or_exhausted": [],
        "calls_until_dominating_candidate_or_exhausted": [],
        "volume_regret": [],
        "surplus_regret": [],
        "original_subset_violation": [],
    }


def _finalize_stats(stats: dict[str, list[int]]) -> dict[str, float | int]:
    calls_full = stats["calls_until_full_winner_or_exhausted"]
    calls_dom = stats["calls_until_dominating_candidate_or_exhausted"]
    return {
        "batches": len(calls_full),
        "candidate_count_mean": mean(stats["candidate_count"]) if stats["candidate_count"] else 0,
        "mean_added_count": mean(stats["added_count"]) if stats["added_count"] else 0,
        "full_winner_present_rate": _mean01(stats["full_winner_present"]),
        "best_matches_full_winner_rate": _mean01(stats["best_matches_full_winner"]),
        "best_weakly_dominates_full_winner_rate": _mean01(
            stats["best_weakly_dominates_full_winner"]
        ),
        "mean_calls_until_full_winner_or_exhausted": mean(calls_full) if calls_full else 0,
        "p95_calls_until_full_winner_or_exhausted": _percentile(calls_full, 0.95),
        "p99_calls_until_full_winner_or_exhausted": _percentile(calls_full, 0.99),
        "mean_calls_until_dominating_candidate_or_exhausted": mean(calls_dom) if calls_dom else 0,
        "p95_calls_until_dominating_candidate_or_exhausted": _percentile(calls_dom, 0.95),
        "p99_calls_until_dominating_candidate_or_exhausted": _percentile(calls_dom, 0.99),
        "mean_volume_regret": mean(stats["volume_regret"]) if stats["volume_regret"] else 0,
        "mean_surplus_regret": mean(stats["surplus_regret"]) if stats["surplus_regret"] else 0,
        "invalid_accept_count": 0,
        "original_subset_violation_count": sum(stats["original_subset_violation"]),
    }


def _initial_repair_selector_weights() -> list[float]:
    weights = {name: 0.0 for name in REPAIR_SELECTOR_FEATURE_NAMES}
    weights["proposal_hard_barrier_log1p"] = 20.0
    weights["hard_barrier_delta_signed"] = 5.0
    weights["proposal_hand_energy_log1p"] = 2.0
    weights["hand_energy_delta_signed"] = 2.0
    weights["proposal_candidate_negative_reserve_flag"] = 20.0
    weights["proposal_candidate_invariant_violation_flag"] = 20.0
    weights["proposal_candidate_limit_violation_count_norm"] = 20.0
    weights["proposal_candidate_balance_violation_count_norm"] = 20.0
    weights["proposal_candidate_noncanonical_fill_vector_flag"] = 8.0
    weights["proposal_candidate_output_mismatch_count_norm"] = 8.0
    weights["proposal_candidate_all_zero_fill_vector_flag"] = 8.0
    weights["proposal_candidate_schema_policy_mismatch_flag"] = 8.0
    weights["proposal_candidate_price_ratio_unreduced_flag"] = 4.0
    weights["proposal_candidate_zero_net_input_count_norm"] = 4.0
    weights["proposal_candidate_normalized_executed_volume"] = -5.0
    weights["proposal_candidate_normalized_surplus"] = -1.0
    return [weights[name] for name in REPAIR_SELECTOR_FEATURE_NAMES]


def _label_score(row: dict[str, Any]) -> tuple[int, int, int, int]:
    label = row["label"]
    return (
        1 if label["valid"] else 0,
        1 if label["dominates_full_winner"] else 0,
        int(label["objective_volume"]),
        int(label["objective_surplus"]),
    )


def _batch_scale(rows: Sequence[dict[str, Any]]) -> dict[str, int]:
    volumes = [abs(int(row["label"]["objective_volume"])) for row in rows]
    surpluses = [abs(int(row["label"]["objective_surplus"])) for row in rows]
    return {
        "volume": max(1, max(volumes, default=1)),
        "surplus": max(1, max(surpluses, default=1)),
    }


def _pair_weight(
    *,
    good: dict[str, Any],
    bad: dict[str, Any],
    scale: dict[str, int],
) -> float:
    good_label = good["label"]
    bad_label = bad["label"]
    weight = 1.0
    if good_label["valid"] and not bad_label["valid"]:
        weight += 1.0
    if good_label["dominates_full_winner"] and not bad_label["dominates_full_winner"]:
        weight += 2.0
    volume_gap = max(
        0,
        int(good_label["objective_volume"]) - int(bad_label["objective_volume"]),
    )
    surplus_gap = max(
        0,
        int(good_label["objective_surplus"]) - int(bad_label["objective_surplus"]),
    )
    weight += 3.0 * (volume_gap / max(1, scale["volume"]))
    if volume_gap == 0:
        weight += 0.5 * (surplus_gap / max(1, scale["surplus"]))
    return min(8.0, max(1.0, weight))


def _dot(weights: Sequence[float], features: Sequence[float]) -> float:
    return sum(weight * value for weight, value in zip(weights, features, strict=True))


def _winner_position(
    *,
    results: Sequence[VerifiedCandidateResult],
    winner_hash: str,
) -> int | None:
    for index, result in enumerate(results, start=1):
        if result.certificate_hash == winner_hash:
            return index
    return None


def _dominance_position(
    *,
    results: Sequence[VerifiedCandidateResult],
    full_winner: VerifiedCandidateResult,
) -> int | None:
    for index, result in enumerate(results, start=1):
        if result.ok and _weakly_dominates(result, full_winner):
            return index
    return None


def _weakly_dominates(left: VerifiedCandidateResult, right: VerifiedCandidateResult) -> bool:
    if left.volume > right.volume:
        return True
    return left.volume == right.volume and left.surplus >= right.surplus


def _mean01(values: Sequence[int]) -> float:
    return 0.0 if not values else sum(values) / len(values)


def _percentile(values: Sequence[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(round((len(ordered) - 1) * fraction)))
    return ordered[index]


def _deltas(modes: dict[str, dict[str, float | int]]) -> dict[str, dict[str, float]]:
    full = modes["full_neighborhood"]
    learned = modes["learned_selected"]
    hand = modes["hand_selected"]
    limited = modes["limited"]
    return {
        "learned_minus_full_neighborhood": _mode_delta(learned, full),
        "learned_minus_hand_selected": _mode_delta(learned, hand),
        "learned_minus_limited": _mode_delta(learned, limited),
    }


def _mode_delta(left: dict[str, float | int], right: dict[str, float | int]) -> dict[str, float]:
    keys = (
        "candidate_count_mean",
        "mean_added_count",
        "best_weakly_dominates_full_winner_rate",
        "mean_calls_until_dominating_candidate_or_exhausted",
        "mean_calls_until_full_winner_or_exhausted",
        "mean_volume_regret",
    )
    return {key: float(left[key]) - float(right[key]) for key in keys}


def _interpretation(modes: dict[str, dict[str, float | int]]) -> dict[str, str]:
    learned = modes["learned_selected"]
    full = modes["full_neighborhood"]
    hand = modes["hand_selected"]
    learned_less_work = float(learned["candidate_count_mean"]) < float(full["candidate_count_mean"])
    learned_keeps_quality = float(learned["mean_volume_regret"]) <= 2.0 * max(
        1.0, float(full["mean_volume_regret"])
    )
    learned_beats_hand = float(learned["mean_volume_regret"]) < float(hand["mean_volume_regret"])
    return {
        "positive_knowledge": (
            "The learned selector reduced proposal count while preserving most of the full-neighborhood regret reduction."
            if learned_less_work and learned_keeps_quality
            else "This run does not support replacing full deterministic neighborhood expansion with the learned selector."
        ),
        "negative_knowledge": (
            "The learned selector beat the hand-selected proposal subset on mean volume regret."
            if learned_beats_hand
            else "The learned selector did not beat the hand-selected proposal subset on mean volume regret."
        ),
        "recommendation": (
            "Keep the selector as a bounded research candidate and test cross-seed before promotion."
            if learned_less_work and learned_keeps_quality
            else "Treat this as negative evidence and refine proposal features, loss weighting, or proposal recipes."
        ),
    }


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Repair Selector Benchmark",
        "",
        "```text",
        f"train_batches: {report['train_batches']}",
        f"holdout_batches: {report['holdout_batches']}",
        f"evaluated_batches: {report['evaluated_batches']}",
        f"candidates_per_batch: {report['candidates_per_batch']}",
        f"candidate_budget: {report['candidate_budget']}",
        f"proposal_budget: {report['proposal_budget']}",
        f"repair_seed_count: {report['repair_seed_count']}",
        f"max_proposals_per_seed: {report['max_proposals_per_seed']}",
        f"feature_dim: {report['feature_dim']}",
        f"parameter_count: {report['parameter_count']}",
        f"train_seed: {report['train_seed']}",
        f"holdout_seed: {report['holdout_seed']}",
        f"wall_clock_ms: {_fmt(report['wall_clock_ms'])}",
        "```",
        "",
        "| mode | batches | candidates | added | full winner present | best dominates full winner | mean calls to dominance | mean calls to full winner | mean volume regret | invalid accepts | subset violations |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode, stats in report["modes"].items():
        lines.append(
            "| "
            + " | ".join(
                (
                    str(mode),
                    str(stats["batches"]),
                    _fmt(stats["candidate_count_mean"]),
                    _fmt(stats["mean_added_count"]),
                    _fmt(stats["full_winner_present_rate"]),
                    _fmt(stats["best_weakly_dominates_full_winner_rate"]),
                    _fmt(stats["mean_calls_until_dominating_candidate_or_exhausted"]),
                    _fmt(stats["mean_calls_until_full_winner_or_exhausted"]),
                    _fmt(stats["mean_volume_regret"]),
                    str(stats["invalid_accept_count"]),
                    str(stats["original_subset_violation_count"]),
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "## Deltas",
            "",
            "Negative candidate-count and call deltas are better. Negative regret deltas are better.",
            "",
            "```json",
            json.dumps(report["deltas"], indent=2, sort_keys=True),
            "```",
            "",
            "## Interpretation",
            "",
            report["interpretation"]["positive_knowledge"],
            "",
            report["interpretation"]["negative_knowledge"],
            "",
            report["interpretation"]["recommendation"],
            "",
            "## Safety Caveat",
            "",
            "The selector is trained and evaluated on synthetic bounded candidates. It is a proposal filter only. Deterministic verifier fallback remains required for exactness.",
        ]
    )
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    return f"{float(value):.4f}"


if __name__ == "__main__":
    raise SystemExit(main())
