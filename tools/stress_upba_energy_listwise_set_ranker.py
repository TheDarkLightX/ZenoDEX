#!/usr/bin/env python3
"""Cross-seed stress harness for the UPBA v2 listwise set ranker."""

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

from tools.compare_upba_energy_listwise_set_ranker import compare_listwise_set_ranker


DEFAULT_SEED_PAIRS: tuple[tuple[int, int], ...] = (
    (20260532, 20260533),
    (20260534, 20260535),
    (20260536, 20260537),
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train-batches", type=int, default=80)
    parser.add_argument("--holdout-batches", type=int, default=60)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--pairwise-epochs", type=int, default=6)
    parser.add_argument("--listwise-epochs", type=int, default=10)
    parser.add_argument("--pairwise-learning-rate", type=float, default=0.03)
    parser.add_argument("--listwise-learning-rate", type=float, default=0.08)
    parser.add_argument("--l2", type=float, default=0.0001)
    parser.add_argument(
        "--seed-pairs",
        default=",".join(f"{train}:{holdout}" for train, holdout in DEFAULT_SEED_PAIRS),
        help="Comma-separated train:holdout seed pairs.",
    )
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = stress_listwise_set_ranker(
        train_batches=args.train_batches,
        holdout_batches=args.holdout_batches,
        candidates_per_batch=args.candidates_per_batch,
        pairwise_epochs=args.pairwise_epochs,
        listwise_epochs=args.listwise_epochs,
        pairwise_learning_rate=args.pairwise_learning_rate,
        listwise_learning_rate=args.listwise_learning_rate,
        l2=args.l2,
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


def stress_listwise_set_ranker(
    *,
    train_batches: int,
    holdout_batches: int,
    candidates_per_batch: int,
    pairwise_epochs: int,
    listwise_epochs: int,
    pairwise_learning_rate: float,
    listwise_learning_rate: float,
    l2: float,
    seed_pairs: Sequence[tuple[int, int]],
) -> dict[str, Any]:
    if not seed_pairs:
        raise ValueError("at least one seed pair is required")
    started = perf_counter()
    runs: list[dict[str, Any]] = []
    for train_seed, holdout_seed in seed_pairs:
        runs.append(
            compare_listwise_set_ranker(
                train_batches=train_batches,
                holdout_batches=holdout_batches,
                candidates_per_batch=candidates_per_batch,
                train_seed=train_seed,
                holdout_seed=holdout_seed,
                pairwise_epochs=pairwise_epochs,
                listwise_epochs=listwise_epochs,
                pairwise_learning_rate=pairwise_learning_rate,
                listwise_learning_rate=listwise_learning_rate,
                l2=l2,
                output_model_dir=None,
            )
        )
    elapsed_ms = (perf_counter() - started) * 1000
    return {
        "schema": "zenodex/energy/upba_v2_listwise_set_ranker_cross_seed/v1",
        "train_batches": train_batches,
        "holdout_batches": holdout_batches,
        "candidates_per_batch": candidates_per_batch,
        "pairwise_epochs": pairwise_epochs,
        "listwise_epochs": listwise_epochs,
        "pairwise_learning_rate": pairwise_learning_rate,
        "listwise_learning_rate": listwise_learning_rate,
        "l2": l2,
        "seed_pairs": [
            {"train_seed": train_seed, "holdout_seed": holdout_seed}
            for train_seed, holdout_seed in seed_pairs
        ],
        "run_count": len(runs),
        "runs": [_compact_run(run) for run in runs],
        "aggregate": _aggregate_runs(runs),
        "safety": _safety(runs),
        "interpretation": _interpretation(runs),
        "wall_clock_ms": elapsed_ms,
    }


def _compact_run(run: dict[str, Any]) -> dict[str, Any]:
    return {
        "train_seed": run["train"]["seed"],
        "holdout_seed": run["holdout"]["seed"],
        "train_rows": run["train"]["rows"],
        "holdout_rows": run["holdout"]["rows"],
        "modes": run["modes"],
        "deltas": run["deltas"],
        "interpretation": run["interpretation"],
    }


def _aggregate_runs(runs: Sequence[dict[str, Any]]) -> dict[str, Any]:
    modes = runs[0]["modes"].keys()
    strict_improvements = [_listwise_improved(run) for run in runs]
    top10_passes = [_listwise_top10_passed(run) for run in runs]
    checked_stop_passes = [_checked_stop_passed(run) for run in runs]
    return {
        "modes": {
            mode: {
                "top_1_recall": _stats([float(run["modes"][mode]["top_1_recall"]) for run in runs]),
                "top_5_recall": _stats([float(run["modes"][mode]["top_5_recall"]) for run in runs]),
                "top_10_recall": _stats([float(run["modes"][mode]["top_10_recall"]) for run in runs]),
                "mean_verifier_calls": _stats(
                    [float(run["modes"][mode]["mean_verifier_calls"]) for run in runs]
                ),
                "p99_verifier_calls": _stats(
                    [float(run["modes"][mode]["p99_verifier_calls"]) for run in runs]
                ),
            }
            for mode in modes
        },
        "listwise_top10_pass_count": sum(1 for item in top10_passes if item),
        "listwise_top10_fail_count": sum(1 for item in top10_passes if not item),
        "checked_stop_at_winner_pass_count": sum(1 for item in checked_stop_passes if item),
        "checked_stop_at_winner_fail_count": sum(1 for item in checked_stop_passes if not item),
        "strict_improvement_count": sum(1 for item in strict_improvements if item),
        "strict_improvement_fail_count": sum(1 for item in strict_improvements if not item),
        "all_safety_passed": _safety(runs)["invalid_accept_count"] == 0
        and _safety(runs)["permutation_violation_count"] == 0,
    }


def _safety(runs: Sequence[dict[str, Any]]) -> dict[str, Any]:
    invalid_accept_count = 0
    permutation_violation_count = 0
    for run in runs:
        invalid_accept_count += sum(
            int(stats["invalid_accept_count"]) for stats in run["modes"].values()
        )
        permutation_violation_count += int(
            run["modes"]["listwise_set"]["permutation_violation_count"]
        )
    return {
        "invalid_accept_count": invalid_accept_count,
        "permutation_violation_count": permutation_violation_count,
        "verifier_authoritative": True,
    }


def _listwise_improved(run: dict[str, Any]) -> bool:
    return bool(run["interpretation"]["listwise_improved_over_best_pairwise"])


def _listwise_top10_passed(run: dict[str, Any]) -> bool:
    listwise = run["modes"]["listwise_set"]
    return (
        float(listwise["top_10_recall"]) == 1.0
        and float(listwise["false_exclusion_rate_top_10"]) == 0.0
    )


def _checked_stop_passed(run: dict[str, Any]) -> bool:
    return float(run["modes"]["listwise_set"]["checked_stop_at_winner_rate"]) == 1.0


def _interpretation(runs: Sequence[dict[str, Any]]) -> dict[str, str]:
    safety = _safety(runs)
    strict_improvement_count = sum(1 for run in runs if _listwise_improved(run))
    top10_count = sum(1 for run in runs if _listwise_top10_passed(run))
    checked_stop_count = sum(1 for run in runs if _checked_stop_passed(run))
    return {
        "positive_knowledge": (
            "The listwise set ranker preserved top-10 recall and checked-stop-at-winner audits on every seed pair."
            if top10_count == len(runs) and checked_stop_count == len(runs)
            else "The listwise set ranker did not preserve top-10 recall or checked-stop-at-winner audits on every seed pair."
        ),
        "negative_knowledge": (
            "The listwise set ranker strictly improved over the best pairwise baseline on every seed pair."
            if strict_improvement_count == len(runs)
            else "The listwise set ranker did not strictly improve over the best pairwise baseline on every seed pair."
        ),
        "safety": (
            "All runs reported zero invalid accepts and zero permutation violations."
            if safety["invalid_accept_count"] == 0 and safety["permutation_violation_count"] == 0
            else "At least one run reported an invalid accept or permutation violation."
        ),
    }


def _stats(values: Sequence[float]) -> dict[str, float]:
    if not values:
        return {"mean": 0.0, "min": 0.0, "max": 0.0}
    return {
        "mean": mean(values),
        "min": min(values),
        "max": max(values),
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
        "# ZenoEnergy Listwise Set Ranker Cross-Seed Stress",
        "",
        "```text",
        f"run_count: {report['run_count']}",
        f"train_batches: {report['train_batches']}",
        f"holdout_batches: {report['holdout_batches']}",
        f"candidates_per_batch: {report['candidates_per_batch']}",
        f"pairwise_epochs: {report['pairwise_epochs']}",
        f"listwise_epochs: {report['listwise_epochs']}",
        f"wall_clock_ms: {_fmt(report['wall_clock_ms'])}",
        "```",
        "",
        "| seeds | mode | top1 | top5 | top10 | mean calls | p99 | invalid accepts |",
        "| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |",
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
                        _fmt(stats["top_1_recall"]),
                        _fmt(stats["top_5_recall"]),
                        _fmt(stats["top_10_recall"]),
                        _fmt(stats["mean_verifier_calls"]),
                        _fmt(stats["p99_verifier_calls"]),
                        str(stats["invalid_accept_count"]),
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
