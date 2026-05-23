#!/usr/bin/env python3
"""Measure whether more synthetic UPBA v2 examples improve ZenoEnergy."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
from random import Random
from statistics import mean
from time import perf_counter
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.upba_v2_energy_model import load_linear_model, save_linear_model
from tools.evaluate_upba_energy import evaluate_rows
from tools.train_upba_energy import load_rows, train_linear_ranker


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--train-dataset",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_synthetic_seed20260517.jsonl"),
    )
    parser.add_argument(
        "--holdout-dataset",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_holdout_seed20260518.jsonl"),
    )
    parser.add_argument(
        "--baseline-model",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json"),
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_data_scaling_seed20260517.json"),
    )
    parser.add_argument(
        "--output-markdown",
        type=Path,
        default=Path("docs/ZENO_ENERGY_DATA_SCALING.md"),
    )
    parser.add_argument(
        "--output-model-dir",
        type=Path,
        default=Path("data/upba_energy/data_scaling_models"),
    )
    parser.add_argument(
        "--batch-counts",
        default="50,100,250,500,1000,2500",
        help="Comma-separated training batch counts to sample deterministically.",
    )
    parser.add_argument("--epochs", type=int, default=4)
    parser.add_argument("--learning-rate", type=float, default=0.05)
    parser.add_argument("--margin", type=float, default=1.0)
    parser.add_argument("--seed", type=int, default=20260553)
    parser.add_argument("--winner-pair-weight", type=float, default=2.0)
    parser.add_argument("--objective-gap-weight", type=float, default=4.0)
    parser.add_argument("--same-volume-surplus-gap-weight", type=float, default=1.0)
    parser.add_argument("--max-pair-weight", type=float, default=8.0)
    args = parser.parse_args()

    batch_counts = _parse_counts(args.batch_counts)
    train_rows_all = load_rows(args.train_dataset)
    holdout_rows = load_rows(args.holdout_dataset)
    train_batches = _group_by_batch(train_rows_all)
    available_batch_count = len(train_batches)
    if any(count > available_batch_count for count in batch_counts):
        raise SystemExit(
            f"requested batch count exceeds available batches: {available_batch_count}"
        )

    hand_report = evaluate_rows(
        holdout_rows,
        scorer=lambda row: float(row["label"]["hand_energy"]),
        mode="hand",
        seed=args.seed,
    )
    baseline_model = load_linear_model(args.baseline_model)
    baseline_report = evaluate_rows(
        holdout_rows,
        scorer=lambda row: baseline_model.energy([float(value) for value in row["features"]]),
        mode="learned",
        seed=args.seed,
    )

    rows_by_budget: list[dict[str, Any]] = []
    for budget in batch_counts:
        sample_rows = _sample_batches(train_batches, budget, seed=args.seed)
        started = perf_counter()
        model = train_linear_ranker(
            sample_rows,
            epochs=args.epochs,
            learning_rate=args.learning_rate,
            margin=args.margin,
            seed=args.seed,
            init="hand",
            winner_pair_weight=args.winner_pair_weight,
            objective_gap_weight=args.objective_gap_weight,
            same_volume_surplus_gap_weight=args.same_volume_surplus_gap_weight,
            max_pair_weight=args.max_pair_weight,
        )
        train_seconds = perf_counter() - started
        model_path = args.output_model_dir / f"upba_v2_energy_data_scaling_{budget}_batches.json"
        model_path.parent.mkdir(parents=True, exist_ok=True)
        save_linear_model(model, model_path)
        report = evaluate_rows(
            holdout_rows,
            scorer=lambda row, model=model: model.energy(
                [float(value) for value in row["features"]]
            ),
            mode="learned",
            seed=args.seed,
        )
        rows_by_budget.append(
            {
                "train_batches": budget,
                "train_rows": len(sample_rows),
                "train_seconds": train_seconds,
                "model_path": str(model_path),
                "model_sha256": _file_sha256(model_path),
                "metrics": _compact_metrics(report),
            }
        )

    best = min(
        rows_by_budget,
        key=lambda row: (
            float(row["metrics"]["mean_verifier_calls"]),
            -float(row["metrics"]["top_1_recall"]),
            int(row["train_batches"]),
        ),
    )
    report = {
        "schema": "zenodex/energy/upba_v2_data_scaling_report/v1",
        "train_dataset": str(args.train_dataset),
        "holdout_dataset": str(args.holdout_dataset),
        "available_train_batches": available_batch_count,
        "available_train_rows": len(train_rows_all),
        "holdout_rows": len(holdout_rows),
        "holdout_batches_with_winner": int(baseline_report["batches"]),
        "seed": args.seed,
        "training": {
            "epochs": args.epochs,
            "learning_rate": args.learning_rate,
            "margin": args.margin,
            "init": "hand",
            "winner_pair_weight": args.winner_pair_weight,
            "objective_gap_weight": args.objective_gap_weight,
            "same_volume_surplus_gap_weight": args.same_volume_surplus_gap_weight,
            "max_pair_weight": args.max_pair_weight,
        },
        "baselines": {
            "hand": _compact_metrics(hand_report),
            "current_gap_weighted": {
                **_compact_metrics(baseline_report),
                "model_path": str(args.baseline_model),
            },
        },
        "runs": rows_by_budget,
        "best_budget": {
            "train_batches": best["train_batches"],
            "train_rows": best["train_rows"],
            "mean_verifier_calls": best["metrics"]["mean_verifier_calls"],
            "top_1_recall": best["metrics"]["top_1_recall"],
            "top_10_recall": best["metrics"]["top_10_recall"],
        },
        "interpretation": _interpret(rows_by_budget, baseline_report),
        "safety": {
            "invalid_accept_count_total": sum(
                int(row["metrics"]["invalid_accept_count"]) for row in rows_by_budget
            )
            + int(hand_report["invalid_accept_count"])
            + int(baseline_report["invalid_accept_count"]),
            "verifier_authoritative": True,
        },
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
    args.output_markdown.write_text(_markdown(report), encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


def _parse_counts(raw: str) -> list[int]:
    counts = [int(part.strip()) for part in raw.split(",") if part.strip()]
    if not counts or any(count <= 0 for count in counts):
        raise SystemExit("--batch-counts must contain positive integers")
    return sorted(dict.fromkeys(counts))


def _group_by_batch(rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        out[str(row["batch_id"])].append(row)
    return dict(out)


def _sample_batches(
    batches: dict[str, list[dict[str, Any]]],
    count: int,
    *,
    seed: int,
) -> list[dict[str, Any]]:
    ids = sorted(batches)
    rng = Random(seed + count)
    selected = sorted(rng.sample(ids, count))
    rows: list[dict[str, Any]] = []
    for batch_id in selected:
        rows.extend(batches[batch_id])
    return rows


def _compact_metrics(report: dict[str, Any]) -> dict[str, Any]:
    return {
        "batches": report["batches"],
        "top_1_recall": report["top_1_recall"],
        "top_5_recall": report["top_5_recall"],
        "top_10_recall": report["top_10_recall"],
        "top_25_recall": report["top_25_recall"],
        "top_1_objective_recall": report["top_1_objective_recall"],
        "mean_verifier_calls": report["mean_verifier_calls"],
        "p95_verifier_calls": report["p95_verifier_calls"],
        "p99_verifier_calls": report["p99_verifier_calls"],
        "mean_verifier_calls_to_objective_winner": report[
            "mean_verifier_calls_to_objective_winner"
        ],
        "invalid_accept_count": report["invalid_accept_count"],
        "false_exclusion_rate_top_10": report["false_exclusion_rate_top_10"],
    }


def _interpret(rows: list[dict[str, Any]], baseline_report: dict[str, Any]) -> dict[str, Any]:
    first = rows[0]["metrics"]
    last = rows[-1]["metrics"]
    best = min(rows, key=lambda row: float(row["metrics"]["mean_verifier_calls"]))
    baseline_calls = float(baseline_report["mean_verifier_calls"])
    return {
        "more_examples_helped_from_small_budget": float(last["mean_verifier_calls"])
        < float(first["mean_verifier_calls"]),
        "best_budget_beats_current_gap_weighted": float(best["metrics"]["mean_verifier_calls"])
        < baseline_calls,
        "best_budget_matches_current_gap_weighted_top10": float(best["metrics"]["top_10_recall"])
        >= float(baseline_report["top_10_recall"]),
        "negative_knowledge": (
            "Extra i.i.d. synthetic examples help only if the added batches expose "
            "new ranking errors or rare verifier-shaped families; raw volume alone "
            "is not a correctness or production-readiness certificate."
        ),
    }


def _file_sha256(path: Path) -> str:
    return "sha256:" + sha256(path.read_bytes()).hexdigest()


def _markdown(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Synthetic Data Scaling",
        "",
        f"schema: `{report['schema']}`",
        f"train_rows_available: {report['available_train_rows']}",
        f"holdout_rows: {report['holdout_rows']}",
        f"epochs: {report['training']['epochs']}",
        "",
        "| train batches | train rows | top-1 | top-10 | mean calls | p95 | p99 | invalid accepts |",
        "| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in report["runs"]:
        metrics = row["metrics"]
        lines.append(
            "| "
            + " | ".join(
                [
                    str(row["train_batches"]),
                    str(row["train_rows"]),
                    f"{metrics['top_1_recall']:.4f}",
                    f"{metrics['top_10_recall']:.4f}",
                    f"{metrics['mean_verifier_calls']:.4f}",
                    str(metrics["p95_verifier_calls"]),
                    str(metrics["p99_verifier_calls"]),
                    str(metrics["invalid_accept_count"]),
                ]
            )
            + " |"
        )
    current = report["baselines"]["current_gap_weighted"]
    lines.extend(
        [
            "",
            "## Current Gap-Weighted Baseline",
            "",
            f"top_1_recall: {current['top_1_recall']:.4f}",
            f"top_10_recall: {current['top_10_recall']:.4f}",
            f"mean_verifier_calls: {current['mean_verifier_calls']:.4f}",
            f"p99_verifier_calls: {current['p99_verifier_calls']}",
            "",
            "## Interpretation",
            "",
            report["interpretation"]["negative_knowledge"],
            "",
            "More synthetic examples are useful when they add coverage over rare verifier",
            "failure families or live-like candidate distributions. Repeating the same",
            "bounded generator eventually saturates the tiny linear ranker.",
        ]
    )
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    raise SystemExit(main())
