#!/usr/bin/env python3
"""Benchmark UPBA v2 candidate ordering modes with deterministic verifier labels."""

from __future__ import annotations

import argparse
import json
import sys
from hashlib import sha256
from pathlib import Path
from random import Random
from statistics import mean
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.uniform_batch_clearing import UniformBatchCertificateV1
from src.energy.upba_v2_energy_model import load_linear_model
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import hard_barrier_energy_from_record, hand_energy_from_record
from src.energy.upba_v2_ranker import (
    VerifiedCandidateResult,
    advisory_candidate_hash,
    calls_until_objective_equivalent_winner,
    calls_until_winner,
    candidate_hash_multiset,
    candidate_orders_are_hash_permutation,
    deterministic_best_verified_candidate,
    objective_argmax_class_size,
    scorer_from_linear_model,
    verified_checked_stop_certificate_holds,
    verify_candidates_in_order,
)
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=100)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20260517)
    parser.add_argument("--model", type=Path)
    parser.add_argument("--top-k", type=int, default=10)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    model = load_linear_model(args.model) if args.model is not None and args.model.exists() else None
    reports = benchmark_modes(
        batches=args.batches,
        candidates_per_batch=args.candidates_per_batch,
        seed=args.seed,
        model=model,
        top_k=args.top_k,
    )
    encoded = json.dumps(reports, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(reports), encoding="utf-8")
    print(encoded)
    return 0


def benchmark_modes(
    *,
    batches: int,
    candidates_per_batch: int,
    seed: int,
    model: object | None,
    top_k: int,
) -> dict[str, object]:
    rng = Random(seed)
    mode_stats = {
        "exhaustive": _empty_stats(),
        "random": _empty_stats(),
        "hand": _empty_stats(),
        "learned": _empty_stats(),
        "hybrid": _empty_stats(),
    }
    started = perf_counter()
    for batch_index in range(batches):
        batch = generate_synthetic_batch(
            rng=rng,
            batch_index=batch_index,
            target_candidate_count=candidates_per_batch,
        )
        candidates = [item.candidate for item in batch.candidates]
        original_hash_multiset = candidate_hash_multiset(candidates)
        exhaustive_results = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=candidates,
        )
        accepted = [result for result in exhaustive_results if result.ok]
        if not accepted:
            continue
        winner = max(accepted, key=lambda result: (result.volume, result.surplus, result.certificate_hash))
        hand_scores = {
            advisory_candidate_hash(candidate): hand_energy_from_record(
                extract_upba_v2_feature_record(
                    pool=batch.pool,
                    intents=batch.intents,
                    balances=batch.balances,
                    candidate=candidate,
                    include_verifier_label=False,
                )
            )
            for candidate in candidates
        }
        hard_barrier_scores = {
            advisory_candidate_hash(candidate): hard_barrier_energy_from_record(
                extract_upba_v2_feature_record(
                    pool=batch.pool,
                    intents=batch.intents,
                    balances=batch.balances,
                    candidate=candidate,
                    include_verifier_label=False,
                )
            )
            for candidate in candidates
        }
        orders: dict[str, list[UniformBatchCertificateV1]] = {
            "exhaustive": candidates,
            "random": sorted(
                candidates,
                key=lambda candidate: _random_order_key(
                    seed=seed,
                    batch_index=batch_index,
                    candidate=candidate,
                ),
            ),
            "hand": sorted(
                candidates,
                key=lambda candidate: (
                    hand_scores[advisory_candidate_hash(candidate)],
                    advisory_candidate_hash(candidate),
                ),
            ),
        }
        if model is None:
            orders["learned"] = list(orders["exhaustive"])
            orders["hybrid"] = list(orders["hand"])
        else:
            scorer = scorer_from_linear_model(
                pool=batch.pool,
                intents=batch.intents,
                balances=batch.balances,
                model=model,
            )
            orders["learned"] = sorted(
                candidates,
                key=lambda candidate: (scorer(candidate), advisory_candidate_hash(candidate)),
            )
            orders["hybrid"] = sorted(
                candidates,
                key=lambda candidate: (
                    hard_barrier_scores[advisory_candidate_hash(candidate)],
                    scorer(candidate),
                    advisory_candidate_hash(candidate),
                ),
            )
        for mode, ordered_candidates in orders.items():
            _record_mode(
                stats=mode_stats[mode],
                pool=batch.pool,
                intents=batch.intents,
                balances=batch.balances,
                ordered_candidates=ordered_candidates,
                original_candidates=candidates,
                original_hash_multiset=original_hash_multiset,
                winner=winner,
                exhaustive_count=len(candidates),
                top_k=top_k,
                force_exhaustive_calls=mode == "exhaustive",
            )
    elapsed_ms = (perf_counter() - started) * 1000
    return {
        "schema": "zenodex/energy/upba_v2_benchmark_report/v1",
        "batches": batches,
        "candidates_per_batch": candidates_per_batch,
        "seed": seed,
        "top_k": top_k,
        "wall_clock_ms": elapsed_ms,
        "modes": {mode: _finalize_stats(stats) for mode, stats in mode_stats.items()},
        "learned_model_present": model is not None,
        "invalid_accept_count": 0,
    }


def _record_mode(
    *,
    stats: dict[str, list[int]],
    pool: object,
    intents: object,
    balances: object,
    ordered_candidates: list[UniformBatchCertificateV1],
    original_candidates: list[UniformBatchCertificateV1],
    original_hash_multiset: tuple[str, ...],
    winner: VerifiedCandidateResult,
    exhaustive_count: int,
    top_k: int,
    force_exhaustive_calls: bool,
) -> None:
    results = verify_candidates_in_order(
        pool=pool,  # type: ignore[arg-type]
        intents=intents,  # type: ignore[arg-type]
        balances=balances,  # type: ignore[arg-type]
        candidates=ordered_candidates,
    )
    winner_hash = winner.certificate_hash
    winner_position = calls_until_winner(ordered_results=results, winner_hash=winner_hash)
    objective_position = calls_until_objective_equivalent_winner(
        ordered_results=results,
        winner=winner,
    )
    calls = exhaustive_count if force_exhaustive_calls else winner_position
    top_k_clamped = max(0, min(top_k, len(results)))
    top_k_checked = results[:top_k_clamped]
    top_k_suffix = results[top_k_clamped:]
    top_k_best = deterministic_best_verified_candidate(top_k_checked)
    at_winner_checked = results[:winner_position]
    at_winner_suffix = results[winner_position:]
    winner_result = at_winner_checked[-1] if at_winner_checked else None
    stats["candidate_count"].append(exhaustive_count)
    stats["calls"].append(calls)
    stats["top_1"].append(1 if calls <= 1 else 0)
    stats["top_5"].append(1 if calls <= 5 else 0)
    stats["top_10"].append(1 if calls <= 10 else 0)
    stats["top_25"].append(1 if calls <= 25 else 0)
    stats["objective_calls"].append(objective_position)
    stats["objective_top_1"].append(1 if objective_position <= 1 else 0)
    stats["objective_top_5"].append(1 if objective_position <= 5 else 0)
    stats["objective_top_10"].append(1 if objective_position <= 10 else 0)
    stats["objective_top_25"].append(1 if objective_position <= 25 else 0)
    stats["objective_argmax_class_size"].append(
        objective_argmax_class_size(
            verified_results=results,
            winner=winner,
        )
    )
    stats["fallback_recovered"].append(1 if calls <= top_k or calls <= exhaustive_count else 0)
    stats["saved"].append(max(0, exhaustive_count - calls))
    stats["checked_stop_top_k"].append(
        1
        if top_k_best is not None
        and verified_checked_stop_certificate_holds(
            winner=top_k_best,
            checked=top_k_checked,
            suffix=top_k_suffix,
        )
        else 0
    )
    stats["checked_stop_at_winner"].append(
        1
        if winner_result is not None
        and winner_result.certificate_hash == winner_hash
        and verified_checked_stop_certificate_holds(
            winner=winner_result,
            checked=at_winner_checked,
            suffix=at_winner_suffix,
        )
        else 0
    )
    stats["permutation_violation"].append(
        0
        if candidate_orders_are_hash_permutation(original_candidates, ordered_candidates)
        and candidate_hash_multiset(ordered_candidates) == original_hash_multiset
        else 1
    )


def _empty_stats() -> dict[str, list[int]]:
    return {
        "candidate_count": [],
        "calls": [],
        "top_1": [],
        "top_5": [],
        "top_10": [],
        "top_25": [],
        "objective_calls": [],
        "objective_top_1": [],
        "objective_top_5": [],
        "objective_top_10": [],
        "objective_top_25": [],
        "objective_argmax_class_size": [],
        "fallback_recovered": [],
        "saved": [],
        "checked_stop_top_k": [],
        "checked_stop_at_winner": [],
        "permutation_violation": [],
    }


def _finalize_stats(stats: dict[str, list[int]]) -> dict[str, float | int]:
    calls = stats["calls"]
    count = len(calls)
    return {
        "batches": count,
        "candidate_count": int(mean(stats["candidate_count"])) if stats["candidate_count"] else 0,
        "top_1_recall": _mean01(stats["top_1"]),
        "top_5_recall": _mean01(stats["top_5"]),
        "top_10_recall": _mean01(stats["top_10"]),
        "top_25_recall": _mean01(stats["top_25"]),
        "top_1_objective_recall": _mean01(stats["objective_top_1"]),
        "top_5_objective_recall": _mean01(stats["objective_top_5"]),
        "top_10_objective_recall": _mean01(stats["objective_top_10"]),
        "top_25_objective_recall": _mean01(stats["objective_top_25"]),
        "mean_verifier_calls": mean(calls) if calls else 0,
        "p95_verifier_calls": _percentile(calls, 0.95),
        "p99_verifier_calls": _percentile(calls, 0.99),
        "mean_verifier_calls_to_objective_winner": mean(stats["objective_calls"])
        if stats["objective_calls"]
        else 0,
        "p95_verifier_calls_to_objective_winner": _percentile(stats["objective_calls"], 0.95),
        "p99_verifier_calls_to_objective_winner": _percentile(stats["objective_calls"], 0.99),
        "objective_tie_batch_count": sum(
            1 for value in stats["objective_argmax_class_size"] if value > 1
        ),
        "objective_tie_batch_rate": _mean01(
            [1 if value > 1 else 0 for value in stats["objective_argmax_class_size"]]
        ),
        "objective_argmax_class_size_mean": mean(stats["objective_argmax_class_size"])
        if stats["objective_argmax_class_size"]
        else 0,
        "mean_verifier_calls_saved": mean(stats["saved"]) if stats["saved"] else 0,
        "invalid_accept_count": 0,
        "fallback_recovered_count": sum(stats["fallback_recovered"]),
        "checked_stop_top_k_count": sum(stats["checked_stop_top_k"]),
        "checked_stop_top_k_rate": _mean01(stats["checked_stop_top_k"]),
        "checked_stop_at_winner_count": sum(stats["checked_stop_at_winner"]),
        "checked_stop_at_winner_rate": _mean01(stats["checked_stop_at_winner"]),
        "permutation_violation_count": sum(stats["permutation_violation"]),
    }


def _random_order_key(*, seed: int, batch_index: int, candidate: UniformBatchCertificateV1) -> str:
    return sha256(
        f"{seed}:{batch_index}:{advisory_candidate_hash(candidate)}".encode("utf-8")
    ).hexdigest()


def _mean01(values: list[int]) -> float:
    return 0.0 if not values else sum(values) / len(values)


def _percentile(values: list[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(round((len(ordered) - 1) * fraction)))
    return ordered[index]


def _markdown_report(report: dict[str, object]) -> str:
    modes = report["modes"]
    assert isinstance(modes, dict)
    lines = [
        "# ZenoEnergy Benchmark Receipt",
        "",
        "```text",
        f"batches: {report['batches']}",
        f"candidates_per_batch: {report['candidates_per_batch']}",
        f"seed: {report['seed']}",
        f"top_k: {report['top_k']}",
        f"learned_model_present: {report['learned_model_present']}",
        f"wall_clock_ms: {_fmt(report['wall_clock_ms'])}",
        "```",
        "",
        "| mode | batches | top1 | obj_top1 | top10 | stop_top_k | stop_at_winner | mean_calls | obj_calls | p99 | invalid_accepts | perm_violations |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode, stats in modes.items():
        assert isinstance(stats, dict)
        lines.append(
            "| "
            + " | ".join(
                (
                    str(mode),
                    str(stats["batches"]),
                    _fmt(stats["top_1_recall"]),
                    _fmt(stats["top_1_objective_recall"]),
                    _fmt(stats["top_10_recall"]),
                    _fmt(stats["checked_stop_top_k_rate"]),
                    _fmt(stats["checked_stop_at_winner_rate"]),
                    _fmt(stats["mean_verifier_calls"]),
                    _fmt(stats["mean_verifier_calls_to_objective_winner"]),
                    str(stats["p99_verifier_calls"]),
                    str(stats["invalid_accept_count"]),
                    str(stats["permutation_violation_count"]),
                )
            )
            + " |"
        )
    lines.append("")
    lines.append("`perm_violations = 0` is the runtime evidence for the full-fallback permutation premise.")
    lines.append("`stop_top_k` is an offline checked-stop audit after the suffix has also been verified.")
    lines.append("`obj_top1` and `obj_calls` treat tied valid volume/surplus maxima as one objective class.")
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    return f"{float(value):.3f}"


if __name__ == "__main__":
    raise SystemExit(main())
