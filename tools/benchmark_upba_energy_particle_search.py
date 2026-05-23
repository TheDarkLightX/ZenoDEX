#!/usr/bin/env python3
"""Benchmark PEM-style advisory UPBA v2 particle candidate search."""

from __future__ import annotations

import argparse
import json
import sys
from hashlib import sha256
from pathlib import Path
from random import Random
from statistics import mean
from time import perf_counter
from typing import Any, Callable, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.uniform_batch_clearing import UniformBatchCertificateV1
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import hand_energy_from_record
from src.energy.upba_v2_neighborhood import propose_upba_v2_neighborhood
from src.energy.upba_v2_ranker import (
    VerifiedCandidateResult,
    advisory_candidate_hash,
    deterministic_best_verified_candidate,
    verify_candidates_in_order,
)
from src.energy.upba_v2_set_features import extract_upba_v2_set_feature_record
from tools.compare_upba_energy_compositional import _obligation_formula_scorer
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=100)
    parser.add_argument("--candidates-per-batch", type=int, default=40)
    parser.add_argument("--candidate-budget", type=int, default=4)
    parser.add_argument("--particle-count", type=int, default=4)
    parser.add_argument("--iterations", type=int, default=3)
    parser.add_argument("--max-proposals-per-particle", type=int, default=6)
    parser.add_argument("--step-denominator", type=int, default=4)
    parser.add_argument("--seed", type=int, default=20260566)
    parser.add_argument("--score-mode", choices=("hand", "obligation"), default="obligation")
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()
    _validate_args(args)
    report = benchmark_particle_search(
        batches=args.batches,
        candidates_per_batch=args.candidates_per_batch,
        candidate_budget=args.candidate_budget,
        particle_count=args.particle_count,
        iterations=args.iterations,
        max_proposals_per_particle=args.max_proposals_per_particle,
        step_denominator=args.step_denominator,
        seed=args.seed,
        score_mode=args.score_mode,
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


def benchmark_particle_search(
    *,
    batches: int,
    candidates_per_batch: int,
    candidate_budget: int,
    particle_count: int,
    iterations: int,
    max_proposals_per_particle: int,
    step_denominator: int,
    seed: int,
    score_mode: str,
) -> dict[str, Any]:
    rng = Random(seed)
    started = perf_counter()
    mode_stats = {
        "limited": _empty_stats(),
        "one_shot_neighborhood": _empty_stats(),
        "particle_resample": _empty_stats(),
    }
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
        scorer = _candidate_scorer(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            score_mode=score_mode,
        )
        limited = _random_budget(
            candidates=full_candidates,
            seed=seed,
            batch_index=batch_index,
            candidate_budget=candidate_budget,
        )
        one_shot = _one_shot_neighborhood(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            seeds=_order_by_score(limited, scorer)[:particle_count],
            max_proposals_per_particle=max_proposals_per_particle,
            step_denominator=step_denominator,
        )
        particle = _particle_resample_search(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            seeds=limited,
            scorer=scorer,
            particle_count=particle_count,
            iterations=iterations,
            max_proposals_per_particle=max_proposals_per_particle,
            step_denominator=step_denominator,
        )
        _record_stats(
            stats=mode_stats["limited"],
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=_order_by_score(limited, scorer),
            full_winner=full_winner,
        )
        _record_stats(
            stats=mode_stats["one_shot_neighborhood"],
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=_order_by_score(one_shot, scorer),
            full_winner=full_winner,
        )
        _record_stats(
            stats=mode_stats["particle_resample"],
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=_order_by_score(particle, scorer),
            full_winner=full_winner,
        )
    modes = {mode: _finalize_stats(stats) for mode, stats in mode_stats.items()}
    elapsed_ms = (perf_counter() - started) * 1000
    return {
        "schema": "zenodex/energy/upba_v2_particle_search_benchmark/v1",
        "batches": batches,
        "evaluated_batches": modes["limited"]["batches"],
        "skipped_without_winner": skipped_without_winner,
        "candidates_per_batch": candidates_per_batch,
        "candidate_budget": candidate_budget,
        "particle_count": particle_count,
        "iterations": iterations,
        "max_proposals_per_particle": max_proposals_per_particle,
        "step_denominator": step_denominator,
        "seed": seed,
        "score_mode": score_mode,
        "modes": modes,
        "deltas": _deltas(modes),
        "safety": {
            "invalid_accept_count": sum(int(mode["invalid_accept_count"]) for mode in modes.values()),
            "verifier_authoritative": True,
            "model_authorizes_settlement": False,
        },
        "interpretation": _interpretation(modes),
        "wall_clock_ms": elapsed_ms,
    }


def _one_shot_neighborhood(
    *,
    pool: object,
    intents: object,
    balances: object,
    seeds: Sequence[UniformBatchCertificateV1],
    max_proposals_per_particle: int,
    step_denominator: int,
) -> tuple[UniformBatchCertificateV1, ...]:
    seen: dict[str, UniformBatchCertificateV1] = {
        advisory_candidate_hash(candidate): candidate for candidate in seeds
    }
    for seed in seeds:
        for proposal in propose_upba_v2_neighborhood(
            pool=pool,  # type: ignore[arg-type]
            intents=intents,  # type: ignore[arg-type]
            balances=balances,  # type: ignore[arg-type]
            seed_candidate=seed,
            max_proposals=max_proposals_per_particle,
            step_denominator=step_denominator,
        ):
            seen.setdefault(proposal.candidate_hash, proposal.candidate)
    return tuple(seen.values())


def _particle_resample_search(
    *,
    pool: object,
    intents: object,
    balances: object,
    seeds: Sequence[UniformBatchCertificateV1],
    scorer: Callable[[UniformBatchCertificateV1], float],
    particle_count: int,
    iterations: int,
    max_proposals_per_particle: int,
    step_denominator: int,
) -> tuple[UniformBatchCertificateV1, ...]:
    archive: dict[str, UniformBatchCertificateV1] = {
        advisory_candidate_hash(candidate): candidate for candidate in seeds
    }
    particles = _order_by_score(seeds, scorer)[:particle_count]
    for _iteration in range(iterations):
        candidates: dict[str, UniformBatchCertificateV1] = {
            advisory_candidate_hash(candidate): candidate for candidate in particles
        }
        for particle in particles:
            for proposal in propose_upba_v2_neighborhood(
                pool=pool,  # type: ignore[arg-type]
                intents=intents,  # type: ignore[arg-type]
                balances=balances,  # type: ignore[arg-type]
                seed_candidate=particle,
                max_proposals=max_proposals_per_particle,
                step_denominator=step_denominator,
            ):
                candidates.setdefault(proposal.candidate_hash, proposal.candidate)
                archive.setdefault(proposal.candidate_hash, proposal.candidate)
        particles = _order_by_score(tuple(candidates.values()), scorer)[:particle_count]
    return tuple(archive.values())


def _candidate_scorer(
    *,
    pool: object,
    intents: object,
    balances: object,
    score_mode: str,
) -> Callable[[UniformBatchCertificateV1], float]:
    def score(candidate: UniformBatchCertificateV1) -> float:
        record = extract_upba_v2_feature_record(
            pool=pool,  # type: ignore[arg-type]
            intents=intents,  # type: ignore[arg-type]
            balances=balances,  # type: ignore[arg-type]
            candidate=candidate,
            include_verifier_label=False,
        )
        if score_mode == "hand":
            return hand_energy_from_record(record)
        set_record = extract_upba_v2_set_feature_record(
            pool=pool,  # type: ignore[arg-type]
            intents=intents,  # type: ignore[arg-type]
            balances=balances,  # type: ignore[arg-type]
            candidate=candidate,
        )
        row = {
            "features": list(record.values),
            "set_aware_features": list(record.values) + list(set_record.values),
        }
        return float(_obligation_formula_scorer(row))

    return score


def _record_stats(
    *,
    stats: dict[str, list[int]],
    pool: object,
    intents: object,
    balances: object,
    candidates: Sequence[UniformBatchCertificateV1],
    full_winner: VerifiedCandidateResult,
) -> None:
    results = verify_candidates_in_order(
        pool=pool,  # type: ignore[arg-type]
        intents=intents,  # type: ignore[arg-type]
        balances=balances,  # type: ignore[arg-type]
        candidates=candidates,
    )
    best = deterministic_best_verified_candidate(results)
    full_winner_hash = full_winner.certificate_hash
    winner_position = _winner_position(results, full_winner_hash)
    stats["candidate_count"].append(len(candidates))
    stats["full_winner_present"].append(1 if winner_position is not None else 0)
    stats["best_matches_full_winner"].append(
        1 if best is not None and best.certificate_hash == full_winner_hash else 0
    )
    stats["best_weakly_dominates_full_winner"].append(
        1 if best is not None and _weakly_dominates(best, full_winner) else 0
    )
    stats["calls_until_full_winner_or_exhausted"].append(
        winner_position if winner_position is not None else len(candidates)
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


def _empty_stats() -> dict[str, list[int]]:
    return {
        "candidate_count": [],
        "full_winner_present": [],
        "best_matches_full_winner": [],
        "best_weakly_dominates_full_winner": [],
        "calls_until_full_winner_or_exhausted": [],
        "volume_regret": [],
        "surplus_regret": [],
    }


def _finalize_stats(stats: dict[str, list[int]]) -> dict[str, float | int]:
    calls = stats["calls_until_full_winner_or_exhausted"]
    return {
        "batches": len(calls),
        "candidate_count_mean": mean(stats["candidate_count"]) if stats["candidate_count"] else 0,
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
    }


def _deltas(modes: dict[str, dict[str, float | int]]) -> dict[str, dict[str, float]]:
    limited = modes["limited"]
    return {
        mode: {
            "full_winner_present_rate_delta": float(stats["full_winner_present_rate"])
            - float(limited["full_winner_present_rate"]),
            "best_matches_full_winner_rate_delta": float(stats["best_matches_full_winner_rate"])
            - float(limited["best_matches_full_winner_rate"]),
            "best_weakly_dominates_full_winner_rate_delta": float(
                stats["best_weakly_dominates_full_winner_rate"]
            )
            - float(limited["best_weakly_dominates_full_winner_rate"]),
            "mean_volume_regret_delta": float(stats["mean_volume_regret"])
            - float(limited["mean_volume_regret"]),
            "mean_calls_delta": float(stats["mean_calls_until_full_winner_or_exhausted"])
            - float(limited["mean_calls_until_full_winner_or_exhausted"]),
        }
        for mode, stats in modes.items()
        if mode != "limited"
    }


def _interpretation(modes: dict[str, dict[str, float | int]]) -> dict[str, Any]:
    limited = modes["limited"]
    particle = modes["particle_resample"]
    helped_quality = float(particle["mean_volume_regret"]) < float(limited["mean_volume_regret"])
    helped_match = float(particle["best_matches_full_winner_rate"]) > float(
        limited["best_matches_full_winner_rate"]
    )
    calls_increased = float(particle["mean_calls_until_full_winner_or_exhausted"]) > float(
        limited["mean_calls_until_full_winner_or_exhausted"]
    )
    return {
        "particle_helped_quality": helped_quality,
        "particle_helped_full_winner_match": helped_match,
        "particle_increased_verifier_work": calls_increased,
        "recommendation": (
            "Keep PEM-style particle search as a constructive candidate-generation branch."
            if helped_quality or helped_match
            else "Do not promote this PEM-style particle configuration; tune proposals or objective decomposition."
        ),
    }


def _random_budget(
    *,
    candidates: Sequence[UniformBatchCertificateV1],
    seed: int,
    batch_index: int,
    candidate_budget: int,
) -> tuple[UniformBatchCertificateV1, ...]:
    ordered = sorted(
        candidates,
        key=lambda candidate: sha256(
            f"{seed}:{batch_index}:{advisory_candidate_hash(candidate)}".encode("utf-8")
        ).hexdigest(),
    )
    return tuple(ordered[: max(1, min(candidate_budget, len(ordered)))])


def _order_by_score(
    candidates: Sequence[UniformBatchCertificateV1],
    scorer: Callable[[UniformBatchCertificateV1], float],
) -> tuple[UniformBatchCertificateV1, ...]:
    return tuple(
        sorted(
            candidates,
            key=lambda candidate: (scorer(candidate), advisory_candidate_hash(candidate)),
        )
    )


def _winner_position(results: Sequence[VerifiedCandidateResult], winner_hash: str) -> int | None:
    for index, result in enumerate(results, start=1):
        if result.certificate_hash == winner_hash:
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


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Particle Search Probe",
        "",
        "```text",
        f"batches: {report['batches']}",
        f"evaluated_batches: {report['evaluated_batches']}",
        f"candidates_per_batch: {report['candidates_per_batch']}",
        f"candidate_budget: {report['candidate_budget']}",
        f"particle_count: {report['particle_count']}",
        f"iterations: {report['iterations']}",
        f"max_proposals_per_particle: {report['max_proposals_per_particle']}",
        f"score_mode: {report['score_mode']}",
        "```",
        "",
        "| mode | batches | candidates | winner present | best is full winner | best dominates full winner | mean calls | volume regret | invalid accepts |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode, stats in report["modes"].items():
        lines.append(
            "| "
            + " | ".join(
                (
                    mode,
                    str(stats["batches"]),
                    _fmt(stats["candidate_count_mean"]),
                    _fmt(stats["full_winner_present_rate"]),
                    _fmt(stats["best_matches_full_winner_rate"]),
                    _fmt(stats["best_weakly_dominates_full_winner_rate"]),
                    _fmt(stats["mean_calls_until_full_winner_or_exhausted"]),
                    _fmt(stats["mean_volume_regret"]),
                    str(stats["invalid_accept_count"]),
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            f"particle_helped_quality: {report['interpretation']['particle_helped_quality']}",
            f"particle_helped_full_winner_match: {report['interpretation']['particle_helped_full_winner_match']}",
            f"particle_increased_verifier_work: {report['interpretation']['particle_increased_verifier_work']}",
            "",
            report["interpretation"]["recommendation"],
            "",
            "Every generated candidate remains advisory and is checked by the deterministic verifier.",
        ]
    )
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    return f"{float(value):.4f}"


def _validate_args(args: argparse.Namespace) -> None:
    if args.batches <= 0:
        raise SystemExit("--batches must be positive")
    if args.candidates_per_batch <= 1:
        raise SystemExit("--candidates-per-batch must be greater than one")
    if args.candidate_budget <= 0:
        raise SystemExit("--candidate-budget must be positive")
    if args.particle_count <= 0:
        raise SystemExit("--particle-count must be positive")
    if args.iterations <= 0:
        raise SystemExit("--iterations must be positive")
    if args.max_proposals_per_particle <= 0:
        raise SystemExit("--max-proposals-per-particle must be positive")
    if args.step_denominator <= 0:
        raise SystemExit("--step-denominator must be positive")


if __name__ == "__main__":
    raise SystemExit(main())
