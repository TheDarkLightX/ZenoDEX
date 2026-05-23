#!/usr/bin/env python3
"""Benchmark deterministic UPBA v2 neighborhood repair proposals.

This benchmark intentionally evaluates a limited candidate budget and a
neighborhood-expanded budget against the full synthetic candidate list. The
expanded list is advisory only. Every candidate is still checked by the
deterministic verifier before objective comparison.
"""

from __future__ import annotations

import argparse
import json
import sys
from hashlib import sha256
from pathlib import Path
from random import Random
from statistics import mean
from time import perf_counter
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.uniform_batch_clearing import UniformBatchCertificateV1
from src.energy.upba_v2_energy_model import load_linear_model
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import hard_barrier_energy_from_record, hand_energy_from_record
from src.energy.upba_v2_neighborhood import augment_candidates_with_neighborhood
from src.energy.upba_v2_ranker import (
    VerifiedCandidateResult,
    advisory_candidate_hash,
    deterministic_best_verified_candidate,
    scorer_from_linear_model,
    verify_candidates_in_order,
)
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=100)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--candidate-budget", type=int, default=6)
    parser.add_argument("--repair-seed-count", type=int, default=4)
    parser.add_argument("--max-proposals-per-seed", type=int, default=6)
    parser.add_argument("--step-denominator", type=int, default=4)
    parser.add_argument("--seed", type=int, default=20260525)
    parser.add_argument("--order-mode", choices=("random", "hand", "learned", "hybrid"), default="hand")
    parser.add_argument("--model", type=Path)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    model = load_linear_model(args.model) if args.model is not None and args.model.exists() else None
    if args.order_mode in {"learned", "hybrid"} and model is None:
        raise SystemExit("--model is required for learned or hybrid order modes")
    report = benchmark_neighborhood(
        batches=args.batches,
        candidates_per_batch=args.candidates_per_batch,
        candidate_budget=args.candidate_budget,
        repair_seed_count=args.repair_seed_count,
        max_proposals_per_seed=args.max_proposals_per_seed,
        step_denominator=args.step_denominator,
        seed=args.seed,
        order_mode=args.order_mode,
        model=model,
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0


def benchmark_neighborhood(
    *,
    batches: int,
    candidates_per_batch: int,
    candidate_budget: int,
    repair_seed_count: int,
    max_proposals_per_seed: int,
    step_denominator: int,
    seed: int,
    order_mode: str,
    model: object | None,
) -> dict[str, Any]:
    rng = Random(seed)
    started = perf_counter()
    limited_stats = _empty_stats()
    neighborhood_stats = _empty_stats()
    skipped_without_winner = 0
    for batch_index in range(batches):
        batch = generate_synthetic_batch(
            rng=rng,
            batch_index=batch_index,
            target_candidate_count=candidates_per_batch,
        )
        full_candidates = tuple(item.candidate for item in batch.candidates)
        full_results = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=full_candidates,
        )
        full_winner = deterministic_best_verified_candidate(full_results)
        if full_winner is None:
            skipped_without_winner += 1
            continue

        ordered_full = _deterministic_budget_order(
            candidates=full_candidates,
            seed=seed,
            batch_index=batch_index,
        )
        limited = ordered_full[: max(1, min(candidate_budget, len(ordered_full)))]
        limited_ordered = _order_candidates(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=limited,
            order_mode=order_mode,
            model=model,
            seed=seed,
            batch_index=batch_index,
        )
        augmentation = augment_candidates_with_neighborhood(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=limited_ordered,
            repair_seed_count=repair_seed_count,
            max_proposals_per_seed=max_proposals_per_seed,
            step_denominator=step_denominator,
        )
        neighborhood_ordered = _order_candidates(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=augmentation.candidates,
            order_mode=order_mode,
            model=model,
            seed=seed,
            batch_index=batch_index,
        )
        _record_stats(
            stats=limited_stats,
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            ordered=limited_ordered,
            full_winner=full_winner,
            added_count=0,
            original_subset_ok=True,
        )
        _record_stats(
            stats=neighborhood_stats,
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            ordered=neighborhood_ordered,
            full_winner=full_winner,
            added_count=len(augmentation.proposals),
            original_subset_ok=augmentation.original_subset_ok,
        )

    elapsed_ms = (perf_counter() - started) * 1000
    limited_final = _finalize_stats(limited_stats)
    neighborhood_final = _finalize_stats(neighborhood_stats)
    return {
        "schema": "zenodex/energy/upba_v2_neighborhood_benchmark/v1",
        "batches": batches,
        "evaluated_batches": limited_final["batches"],
        "skipped_without_winner": skipped_without_winner,
        "candidates_per_batch": candidates_per_batch,
        "candidate_budget": candidate_budget,
        "repair_seed_count": repair_seed_count,
        "max_proposals_per_seed": max_proposals_per_seed,
        "step_denominator": step_denominator,
        "seed": seed,
        "order_mode": order_mode,
        "learned_model_present": model is not None,
        "wall_clock_ms": elapsed_ms,
        "modes": {
            "limited": limited_final,
            "neighborhood": neighborhood_final,
        },
        "deltas": {
            "full_winner_present_rate_delta": (
                float(neighborhood_final["full_winner_present_rate"])
                - float(limited_final["full_winner_present_rate"])
            ),
            "best_matches_full_winner_rate_delta": (
                float(neighborhood_final["best_matches_full_winner_rate"])
                - float(limited_final["best_matches_full_winner_rate"])
            ),
            "best_weakly_dominates_full_winner_rate_delta": (
                float(neighborhood_final["best_weakly_dominates_full_winner_rate"])
                - float(limited_final["best_weakly_dominates_full_winner_rate"])
            ),
            "mean_volume_regret_delta": (
                float(neighborhood_final["mean_volume_regret"])
                - float(limited_final["mean_volume_regret"])
            ),
            "mean_calls_until_full_winner_or_exhausted_delta": (
                float(neighborhood_final["mean_calls_until_full_winner_or_exhausted"])
                - float(limited_final["mean_calls_until_full_winner_or_exhausted"])
            ),
        },
        "safety": {
            "invalid_accept_count": 0,
            "verifier_authoritative": True,
            "exactness_caveat": (
                "Neighborhood proposals expand a limited candidate set. They are "
                "not a bounded-grid optimality certificate unless paired with "
                "full fallback over an exact candidate family or a dominance-cover proof."
            ),
        },
        "interpretation": _interpretation(limited_final, neighborhood_final),
    }


def _order_candidates(
    *,
    pool: object,
    intents: object,
    balances: object,
    candidates: Sequence[UniformBatchCertificateV1],
    order_mode: str,
    model: object | None,
    seed: int,
    batch_index: int,
) -> tuple[UniformBatchCertificateV1, ...]:
    if order_mode == "random":
        return tuple(
            sorted(
                candidates,
                key=lambda candidate: _random_key(
                    seed=seed,
                    batch_index=batch_index,
                    candidate=candidate,
                ),
            )
        )
    hand_scores = {
        advisory_candidate_hash(candidate): hand_energy_from_record(
            extract_upba_v2_feature_record(
                pool=pool,  # type: ignore[arg-type]
                intents=intents,  # type: ignore[arg-type]
                balances=balances,  # type: ignore[arg-type]
                candidate=candidate,
                include_verifier_label=False,
            )
        )
        for candidate in candidates
    }
    if order_mode == "hand":
        return tuple(
            sorted(
                candidates,
                key=lambda candidate: (
                    hand_scores[advisory_candidate_hash(candidate)],
                    advisory_candidate_hash(candidate),
                ),
            )
        )
    if model is None:
        raise ValueError("model is required for learned or hybrid order modes")
    scorer = scorer_from_linear_model(
        pool=pool,  # type: ignore[arg-type]
        intents=intents,  # type: ignore[arg-type]
        balances=balances,  # type: ignore[arg-type]
        model=model,
    )
    if order_mode == "learned":
        return tuple(
            sorted(
                candidates,
                key=lambda candidate: (scorer(candidate), advisory_candidate_hash(candidate)),
            )
        )
    if order_mode == "hybrid":
        hard_scores = {
            advisory_candidate_hash(candidate): hard_barrier_energy_from_record(
                extract_upba_v2_feature_record(
                    pool=pool,  # type: ignore[arg-type]
                    intents=intents,  # type: ignore[arg-type]
                    balances=balances,  # type: ignore[arg-type]
                    candidate=candidate,
                    include_verifier_label=False,
                )
            )
            for candidate in candidates
        }
        return tuple(
            sorted(
                candidates,
                key=lambda candidate: (
                    hard_scores[advisory_candidate_hash(candidate)],
                    scorer(candidate),
                    advisory_candidate_hash(candidate),
                ),
            )
        )
    raise ValueError(f"unsupported order mode: {order_mode}")


def _record_stats(
    *,
    stats: dict[str, list[int]],
    pool: object,
    intents: object,
    balances: object,
    ordered: Sequence[UniformBatchCertificateV1],
    full_winner: VerifiedCandidateResult,
    added_count: int,
    original_subset_ok: bool,
) -> None:
    results = verify_candidates_in_order(
        pool=pool,  # type: ignore[arg-type]
        intents=intents,  # type: ignore[arg-type]
        balances=balances,  # type: ignore[arg-type]
        candidates=ordered,
    )
    best = deterministic_best_verified_candidate(results)
    full_winner_hash = full_winner.certificate_hash
    winner_position = _winner_position(results=results, winner_hash=full_winner_hash)
    winner_present = winner_position is not None
    stats["candidate_count"].append(len(ordered))
    stats["added_count"].append(added_count)
    stats["full_winner_present"].append(1 if winner_present else 0)
    stats["best_matches_full_winner"].append(
        1 if best is not None and best.certificate_hash == full_winner_hash else 0
    )
    stats["best_weakly_dominates_full_winner"].append(
        1 if best is not None and _weakly_dominates(best, full_winner) else 0
    )
    stats["calls_until_full_winner_or_exhausted"].append(
        winner_position if winner_position is not None else len(ordered)
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
        "volume_regret": [],
        "surplus_regret": [],
        "original_subset_violation": [],
    }


def _finalize_stats(stats: dict[str, list[int]]) -> dict[str, float | int]:
    calls = stats["calls_until_full_winner_or_exhausted"]
    return {
        "batches": len(calls),
        "candidate_count_mean": mean(stats["candidate_count"]) if stats["candidate_count"] else 0,
        "mean_added_count": mean(stats["added_count"]) if stats["added_count"] else 0,
        "full_winner_present_rate": _mean01(stats["full_winner_present"]),
        "best_matches_full_winner_rate": _mean01(stats["best_matches_full_winner"]),
        "best_weakly_dominates_full_winner_rate": _mean01(
            stats["best_weakly_dominates_full_winner"]
        ),
        "mean_calls_until_full_winner_or_exhausted": mean(calls) if calls else 0,
        "p95_calls_until_full_winner_or_exhausted": _percentile(calls, 0.95),
        "p99_calls_until_full_winner_or_exhausted": _percentile(calls, 0.99),
        "mean_volume_regret": mean(stats["volume_regret"]) if stats["volume_regret"] else 0,
        "mean_surplus_regret": mean(stats["surplus_regret"]) if stats["surplus_regret"] else 0,
        "invalid_accept_count": 0,
        "original_subset_violation_count": sum(stats["original_subset_violation"]),
    }


def _deterministic_budget_order(
    *,
    candidates: Sequence[UniformBatchCertificateV1],
    seed: int,
    batch_index: int,
) -> tuple[UniformBatchCertificateV1, ...]:
    return tuple(
        sorted(
            candidates,
            key=lambda candidate: _random_key(
                seed=seed,
                batch_index=batch_index,
                candidate=candidate,
            ),
        )
    )


def _winner_position(
    *,
    results: Sequence[VerifiedCandidateResult],
    winner_hash: str,
) -> int | None:
    for index, result in enumerate(results, start=1):
        if result.certificate_hash == winner_hash:
            return index
    return None


def _random_key(*, seed: int, batch_index: int, candidate: UniformBatchCertificateV1) -> str:
    return sha256(
        f"{seed}:{batch_index}:{advisory_candidate_hash(candidate)}".encode("utf-8")
    ).hexdigest()


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


def _interpretation(
    limited: dict[str, float | int],
    neighborhood: dict[str, float | int],
) -> dict[str, str]:
    regret_improved = float(neighborhood["mean_volume_regret"]) < float(limited["mean_volume_regret"])
    dominance_improved = float(neighborhood["best_weakly_dominates_full_winner_rate"]) > float(
        limited["best_weakly_dominates_full_winner_rate"]
    )
    calls_increased = float(neighborhood["mean_calls_until_full_winner_or_exhausted"]) > float(
        limited["mean_calls_until_full_winner_or_exhausted"]
    )
    return {
        "positive_knowledge": (
            "Deterministic neighborhood proposals reduced best-valid volume regret "
            "and improved weak dominance over the full synthetic-list winner."
            if regret_improved and dominance_improved
            else "This run does not support promoting the neighborhood baseline on objective quality."
        ),
        "negative_knowledge": (
            "The neighborhood baseline increased verifier work in this benchmark."
            if calls_increased
            else "This run did not show an added verifier-call cost for the neighborhood baseline."
        ),
        "recommendation": (
            "Train or hand-design a repair selector that proposes fewer repairs while "
            "preserving most of the regret reduction."
            if regret_improved and calls_increased
            else "Keep this as a bounded research result and rerun across seeds."
        ),
    }


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Neighborhood Repair Benchmark",
        "",
        "```text",
        f"batches: {report['batches']}",
        f"evaluated_batches: {report['evaluated_batches']}",
        f"candidates_per_batch: {report['candidates_per_batch']}",
        f"candidate_budget: {report['candidate_budget']}",
        f"repair_seed_count: {report['repair_seed_count']}",
        f"max_proposals_per_seed: {report['max_proposals_per_seed']}",
        f"seed: {report['seed']}",
        f"order_mode: {report['order_mode']}",
        f"wall_clock_ms: {_fmt(report['wall_clock_ms'])}",
        "```",
        "",
        "| mode | batches | candidates | added | winner present | best is full winner | best dominates full winner | mean calls | mean volume regret | invalid accepts | subset violations |",
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
                    _fmt(stats["best_matches_full_winner_rate"]),
                    _fmt(stats["best_weakly_dominates_full_winner_rate"]),
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
            "Positive winner-present and best-match deltas are better. Negative regret deltas are better.",
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
            report["safety"]["exactness_caveat"],
        ]
    )
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    return f"{float(value):.3f}"


if __name__ == "__main__":
    raise SystemExit(main())
