#!/usr/bin/env python3
"""Cross-seed stress harness for the UPBA v2 repair selector."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from statistics import mean
from time import perf_counter
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.benchmark_upba_repair_selector import train_and_evaluate_repair_selector


DEFAULT_SEED_PAIRS: tuple[tuple[int, int], ...] = (
    (20260526, 20260527),
    (20260528, 20260529),
    (20260530, 20260531),
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train-batches", type=int, default=80)
    parser.add_argument("--holdout-batches", type=int, default=60)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--candidate-budget", type=int, default=6)
    parser.add_argument("--proposal-budget", type=int, default=2)
    parser.add_argument("--repair-seed-count", type=int, default=4)
    parser.add_argument("--max-proposals-per-seed", type=int, default=6)
    parser.add_argument("--step-denominator", type=int, default=4)
    parser.add_argument("--epochs", type=int, default=8)
    parser.add_argument("--learning-rate", type=float, default=0.05)
    parser.add_argument("--margin", type=float, default=1.0)
    parser.add_argument(
        "--seed-pairs",
        default=",".join(f"{train}:{holdout}" for train, holdout in DEFAULT_SEED_PAIRS),
        help="Comma-separated train:holdout seed pairs.",
    )
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = stress_repair_selector(
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
        seed_pairs=_parse_seed_pairs(args.seed_pairs),
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


def stress_repair_selector(
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
    seed_pairs: Sequence[tuple[int, int]],
) -> dict[str, Any]:
    if not seed_pairs:
        raise ValueError("at least one seed pair is required")
    started = perf_counter()
    runs: list[dict[str, Any]] = []
    for train_seed, holdout_seed in seed_pairs:
        run_report, _model = train_and_evaluate_repair_selector(
            train_batches=train_batches,
            holdout_batches=holdout_batches,
            candidates_per_batch=candidates_per_batch,
            candidate_budget=candidate_budget,
            proposal_budget=proposal_budget,
            repair_seed_count=repair_seed_count,
            max_proposals_per_seed=max_proposals_per_seed,
            step_denominator=step_denominator,
            epochs=epochs,
            learning_rate=learning_rate,
            margin=margin,
            train_seed=train_seed,
            holdout_seed=holdout_seed,
        )
        runs.append(run_report)
    elapsed_ms = (perf_counter() - started) * 1000
    return {
        "schema": "zenodex/energy/upba_v2_repair_selector_cross_seed/v1",
        "train_batches": train_batches,
        "holdout_batches": holdout_batches,
        "candidates_per_batch": candidates_per_batch,
        "candidate_budget": candidate_budget,
        "proposal_budget": proposal_budget,
        "repair_seed_count": repair_seed_count,
        "max_proposals_per_seed": max_proposals_per_seed,
        "step_denominator": step_denominator,
        "epochs": epochs,
        "learning_rate": learning_rate,
        "margin": margin,
        "seed_pairs": [
            {"train_seed": train_seed, "holdout_seed": holdout_seed}
            for train_seed, holdout_seed in seed_pairs
        ],
        "run_count": len(runs),
        "runs": [_compact_run(run) for run in runs],
        "aggregate": _aggregate_runs(runs),
        "wall_clock_ms": elapsed_ms,
        "safety": {
            "invalid_accept_count": sum(_invalid_accepts(run) for run in runs),
            "original_subset_violation_count": sum(_subset_violations(run) for run in runs),
            "verifier_authoritative": all(run["safety"]["verifier_authoritative"] for run in runs),
        },
        "interpretation": _interpretation(runs),
    }


def _compact_run(run: dict[str, Any]) -> dict[str, Any]:
    return {
        "train_seed": run["train_seed"],
        "holdout_seed": run["holdout_seed"],
        "evaluated_batches": run["evaluated_batches"],
        "training_rows": run["training_rows"],
        "modes": run["modes"],
        "deltas": run["deltas"],
        "safety": run["safety"],
        "interpretation": run["interpretation"],
    }


def _aggregate_runs(runs: Sequence[dict[str, Any]]) -> dict[str, Any]:
    modes = runs[0]["modes"].keys()
    aggregate_modes = {
        mode: {
            "candidate_count_mean": _stats(
                [float(run["modes"][mode]["candidate_count_mean"]) for run in runs]
            ),
            "mean_added_count": _stats(
                [float(run["modes"][mode]["mean_added_count"]) for run in runs]
            ),
            "best_weakly_dominates_full_winner_rate": _stats(
                [float(run["modes"][mode]["best_weakly_dominates_full_winner_rate"]) for run in runs]
            ),
            "mean_calls_until_dominating_candidate_or_exhausted": _stats(
                [
                    float(run["modes"][mode]["mean_calls_until_dominating_candidate_or_exhausted"])
                    for run in runs
                ]
            ),
            "mean_calls_until_full_winner_or_exhausted": _stats(
                [
                    float(run["modes"][mode]["mean_calls_until_full_winner_or_exhausted"])
                    for run in runs
                ]
            ),
            "mean_volume_regret": _stats(
                [float(run["modes"][mode]["mean_volume_regret"]) for run in runs]
            ),
        }
        for mode in modes
    }
    compression_passes = [
        _compresses_full_neighborhood(run)
        for run in runs
    ]
    hand_win_passes = [
        _strictly_beats_hand_selected(run)
        for run in runs
    ]
    return {
        "modes": aggregate_modes,
        "compression_pass_count": sum(1 for item in compression_passes if item),
        "compression_fail_count": sum(1 for item in compression_passes if not item),
        "strict_hand_win_count": sum(1 for item in hand_win_passes if item),
        "strict_hand_win_fail_count": sum(1 for item in hand_win_passes if not item),
        "all_safety_passed": all(_invalid_accepts(run) == 0 and _subset_violations(run) == 0 for run in runs),
    }


def _stats(values: Sequence[float]) -> dict[str, float]:
    if not values:
        return {"mean": 0.0, "min": 0.0, "max": 0.0}
    return {
        "mean": mean(values),
        "min": min(values),
        "max": max(values),
    }


def _compresses_full_neighborhood(run: dict[str, Any]) -> bool:
    learned = run["modes"]["learned_selected"]
    full = run["modes"]["full_neighborhood"]
    return (
        float(learned["candidate_count_mean"]) < float(full["candidate_count_mean"])
        and float(learned["mean_added_count"]) < float(full["mean_added_count"])
        and float(learned["mean_volume_regret"]) <= float(full["mean_volume_regret"])
        and float(learned["best_weakly_dominates_full_winner_rate"])
        >= float(full["best_weakly_dominates_full_winner_rate"])
    )


def _strictly_beats_hand_selected(run: dict[str, Any]) -> bool:
    learned = run["modes"]["learned_selected"]
    hand = run["modes"]["hand_selected"]
    return float(learned["mean_volume_regret"]) < float(hand["mean_volume_regret"])


def _invalid_accepts(run: dict[str, Any]) -> int:
    return sum(int(mode["invalid_accept_count"]) for mode in run["modes"].values())


def _subset_violations(run: dict[str, Any]) -> int:
    return sum(int(mode["original_subset_violation_count"]) for mode in run["modes"].values())


def _interpretation(runs: Sequence[dict[str, Any]]) -> dict[str, str]:
    compression_count = sum(1 for run in runs if _compresses_full_neighborhood(run))
    hand_win_count = sum(1 for run in runs if _strictly_beats_hand_selected(run))
    safety_ok = all(_invalid_accepts(run) == 0 and _subset_violations(run) == 0 for run in runs)
    return {
        "positive_knowledge": (
            "The learned selector compressed full neighborhood expansion on every seed pair while preserving regret and weak-dominance metrics."
            if compression_count == len(runs)
            else "The learned selector did not preserve the full-neighborhood compression result on every seed pair."
        ),
        "negative_knowledge": (
            "The learned selector strictly beat the hand-selected subset on every seed pair."
            if hand_win_count == len(runs)
            else "The learned selector did not strictly beat the hand-selected subset on every seed pair."
        ),
        "safety": (
            "All runs reported zero invalid accepts and zero original-subset violations."
            if safety_ok
            else "At least one run reported an invalid accept or original-subset violation."
        ),
    }


def _parse_seed_pairs(raw: str) -> tuple[tuple[int, int], ...]:
    pairs: list[tuple[int, int]] = []
    for item in raw.split(","):
        stripped = item.strip()
        if not stripped:
            continue
        left, separator, right = stripped.partition(":")
        if separator != ":":
            raise ValueError("seed pairs must use train:holdout format")
        pairs.append((int(left), int(right)))
    return tuple(pairs)


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Repair Selector Cross-Seed Stress",
        "",
        "```text",
        f"run_count: {report['run_count']}",
        f"train_batches: {report['train_batches']}",
        f"holdout_batches: {report['holdout_batches']}",
        f"candidates_per_batch: {report['candidates_per_batch']}",
        f"candidate_budget: {report['candidate_budget']}",
        f"proposal_budget: {report['proposal_budget']}",
        f"repair_seed_count: {report['repair_seed_count']}",
        f"max_proposals_per_seed: {report['max_proposals_per_seed']}",
        f"epochs: {report['epochs']}",
        f"wall_clock_ms: {_fmt(report['wall_clock_ms'])}",
        "```",
        "",
        "| seeds | mode | candidates | added | best dominates full winner | calls to dominance | calls to full winner | volume regret | invalid accepts | subset violations |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for run in report["runs"]:
        seed_label = f"{run['train_seed']}->{run['holdout_seed']}"
        for mode, stats in run["modes"].items():
            lines.append(
                "| "
                + " | ".join(
                    (
                        seed_label,
                        str(mode),
                        _fmt(stats["candidate_count_mean"]),
                        _fmt(stats["mean_added_count"]),
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
            "## Aggregate",
            "",
            "```json",
            json.dumps(report["aggregate"], indent=2, sort_keys=True),
            "```",
            "",
            "## Interpretation",
            "",
            report["interpretation"]["positive_knowledge"],
            "",
            report["interpretation"]["negative_knowledge"],
            "",
            report["interpretation"]["safety"],
        ]
    )
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    return f"{float(value):.4f}"


if __name__ == "__main__":
    raise SystemExit(main())
