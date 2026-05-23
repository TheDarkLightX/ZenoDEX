#!/usr/bin/env python3
"""Compare aggregate and set-aware UPBA v2 energy rankers on fresh synthetic data."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from statistics import mean
from time import perf_counter
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.upba_v2_energy_model import LinearEnergyModel, save_linear_model
from tools.evaluate_upba_energy import evaluate_rows
from tools.generate_upba_energy_dataset import generate_dataset_rows
from tools.train_upba_energy import train_linear_ranker


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train-batches", type=int, default=200)
    parser.add_argument("--holdout-batches", type=int, default=100)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--train-seed", type=int, default=20260519)
    parser.add_argument("--holdout-seed", type=int, default=20260520)
    parser.add_argument("--epochs", type=int, default=6)
    parser.add_argument("--learning-rate", type=float, default=0.03)
    parser.add_argument("--margin", type=float, default=1.0)
    parser.add_argument("--winner-pair-weight", type=float, default=2.0)
    parser.add_argument("--objective-gap-weight", type=float, default=4.0)
    parser.add_argument("--same-volume-surplus-gap-weight", type=float, default=1.0)
    parser.add_argument("--max-pair-weight", type=float, default=8.0)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    parser.add_argument("--output-model-dir", type=Path)
    args = parser.parse_args()

    _validate_args(args)
    report = compare_set_aware_rankers(
        train_batches=args.train_batches,
        holdout_batches=args.holdout_batches,
        candidates_per_batch=args.candidates_per_batch,
        train_seed=args.train_seed,
        holdout_seed=args.holdout_seed,
        epochs=args.epochs,
        learning_rate=args.learning_rate,
        margin=args.margin,
        winner_pair_weight=args.winner_pair_weight,
        objective_gap_weight=args.objective_gap_weight,
        same_volume_surplus_gap_weight=args.same_volume_surplus_gap_weight,
        max_pair_weight=args.max_pair_weight,
        output_model_dir=args.output_model_dir,
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


def compare_set_aware_rankers(
    *,
    train_batches: int,
    holdout_batches: int,
    candidates_per_batch: int,
    train_seed: int,
    holdout_seed: int,
    epochs: int,
    learning_rate: float,
    margin: float,
    winner_pair_weight: float,
    objective_gap_weight: float,
    same_volume_surplus_gap_weight: float,
    max_pair_weight: float,
    output_model_dir: Path | None = None,
) -> dict[str, Any]:
    started = perf_counter()
    train_rows = list(
        generate_dataset_rows(
            batches=train_batches,
            candidates_per_batch=candidates_per_batch,
            seed=train_seed,
        )
    )
    holdout_rows = list(
        generate_dataset_rows(
            batches=holdout_batches,
            candidates_per_batch=candidates_per_batch,
            seed=holdout_seed,
        )
    )
    train_args = {
        "epochs": epochs,
        "learning_rate": learning_rate,
        "margin": margin,
        "seed": train_seed,
        "init": "zero",
        "winner_pair_weight": winner_pair_weight,
        "objective_gap_weight": objective_gap_weight,
        "same_volume_surplus_gap_weight": same_volume_surplus_gap_weight,
        "max_pair_weight": max_pair_weight,
    }
    aggregate = train_linear_ranker(train_rows, feature_block="aggregate", **train_args)
    set_aware = train_linear_ranker(train_rows, feature_block="set-aware", **train_args)

    model_paths: dict[str, str] = {}
    if output_model_dir is not None:
        output_model_dir.mkdir(parents=True, exist_ok=True)
        aggregate_path = output_model_dir / "upba_v2_energy_aggregate_compare.json"
        set_aware_path = output_model_dir / "upba_v2_energy_set_aware_compare.json"
        save_linear_model(aggregate, aggregate_path)
        save_linear_model(set_aware, set_aware_path)
        model_paths = {
            "aggregate": str(aggregate_path),
            "set_aware": str(set_aware_path),
        }

    modes = {
        "random": evaluate_rows(holdout_rows, scorer=None, mode="random", seed=holdout_seed),
        "hand": evaluate_rows(
            holdout_rows,
            scorer=lambda row: float(row["label"]["hand_energy"]),
            mode="hand",
            seed=holdout_seed,
        ),
        "aggregate_learned": evaluate_rows(
            holdout_rows,
            scorer=_aggregate_scorer(aggregate),
            mode="learned",
            seed=holdout_seed,
        ),
        "aggregate_hybrid": evaluate_rows(
            holdout_rows,
            scorer=_aggregate_scorer(aggregate),
            mode="hybrid",
            seed=holdout_seed,
        ),
        "set_aware_learned": evaluate_rows(
            holdout_rows,
            scorer=_set_aware_scorer(set_aware),
            mode="learned",
            seed=holdout_seed,
        ),
        "set_aware_hybrid": evaluate_rows(
            holdout_rows,
            scorer=_set_aware_scorer(set_aware),
            mode="hybrid",
            seed=holdout_seed,
        ),
    }
    elapsed_ms = (perf_counter() - started) * 1000
    return {
        "schema": "zenodex/energy/upba_v2_set_aware_comparison/v1",
        "train": {
            "batches": train_batches,
            "rows": len(train_rows),
            "candidate_count_mean": _candidate_count_mean(train_rows),
            "seed": train_seed,
        },
        "holdout": {
            "batches": holdout_batches,
            "rows": len(holdout_rows),
            "candidate_count_mean": _candidate_count_mean(holdout_rows),
            "seed": holdout_seed,
        },
        "candidates_per_batch": candidates_per_batch,
        "training": {
            "epochs": epochs,
            "learning_rate": learning_rate,
            "margin": margin,
            "winner_pair_weight": winner_pair_weight,
            "objective_gap_weight": objective_gap_weight,
            "same_volume_surplus_gap_weight": same_volume_surplus_gap_weight,
            "max_pair_weight": max_pair_weight,
        },
        "models": {
            "aggregate": {
                "feature_dim": len(aggregate.feature_names),
                "parameter_count": len(aggregate.weights) + 1,
            },
            "set_aware": {
                "feature_dim": len(set_aware.feature_names),
                "parameter_count": len(set_aware.weights) + 1,
            },
        },
        "model_paths": model_paths,
        "modes": modes,
        "deltas": _mode_deltas(modes),
        "interpretation": _interpretation(modes),
        "wall_clock_ms": elapsed_ms,
    }


def _aggregate_scorer(model: LinearEnergyModel) -> Callable[[dict[str, Any]], float]:
    return lambda row: model.energy([float(value) for value in row["features"]])


def _set_aware_scorer(model: LinearEnergyModel) -> Callable[[dict[str, Any]], float]:
    return lambda row: model.energy([float(value) for value in row["set_aware_features"]])


def _mode_deltas(modes: dict[str, dict[str, Any]]) -> dict[str, Any]:
    aggregate = modes["aggregate_learned"]
    set_aware = modes["set_aware_learned"]
    aggregate_hybrid = modes["aggregate_hybrid"]
    set_aware_hybrid = modes["set_aware_hybrid"]
    return {
        "set_aware_vs_aggregate_learned": _delta(set_aware, aggregate),
        "set_aware_hybrid_vs_aggregate_hybrid": _delta(set_aware_hybrid, aggregate_hybrid),
    }


def _delta(left: dict[str, Any], right: dict[str, Any]) -> dict[str, float]:
    return {
        "top_1_recall_delta": float(left["top_1_recall"]) - float(right["top_1_recall"]),
        "top_5_recall_delta": float(left["top_5_recall"]) - float(right["top_5_recall"]),
        "top_10_recall_delta": float(left["top_10_recall"]) - float(right["top_10_recall"]),
        "mean_verifier_calls_delta": float(left["mean_verifier_calls"]) - float(right["mean_verifier_calls"]),
        "p99_verifier_calls_delta": float(left["p99_verifier_calls"]) - float(right["p99_verifier_calls"]),
    }


def _interpretation(modes: dict[str, dict[str, Any]]) -> dict[str, Any]:
    aggregate = modes["aggregate_learned"]
    set_aware = modes["set_aware_learned"]
    aggregate_calls = float(aggregate["mean_verifier_calls"])
    set_aware_calls = float(set_aware["mean_verifier_calls"])
    aggregate_top1 = float(aggregate["top_1_recall"])
    set_aware_top1 = float(set_aware["top_1_recall"])
    preferred = "set_aware_learned"
    if (aggregate_calls, -aggregate_top1) <= (set_aware_calls, -set_aware_top1):
        preferred = "aggregate_learned"
    invalid_accept_count_total = sum(
        int(stats["invalid_accept_count"]) for stats in modes.values()
    )
    return {
        "preferred_measured_checkpoint": preferred,
        "all_modes_invalid_accept_count": invalid_accept_count_total,
        "set_aware_mean_calls_improved": set_aware_calls < aggregate_calls,
        "set_aware_top1_improved": set_aware_top1 > aggregate_top1,
        "negative_knowledge": (
            "Extra set-aware moment features did not improve the linear ranker "
            "on this comparison run. Keep the aggregate gap-weighted checkpoint "
            "as the measured default until cross-seed evidence supports a change."
        ),
    }


def _candidate_count_mean(rows: list[dict[str, Any]]) -> float:
    counts: dict[str, int] = {}
    for row in rows:
        batch_id = str(row["batch_id"])
        counts[batch_id] = counts.get(batch_id, 0) + 1
    return mean(counts.values()) if counts else 0.0


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Set-Aware Comparison",
        "",
        "```text",
        f"train_batches: {report['train']['batches']}",
        f"train_rows: {report['train']['rows']}",
        f"train_seed: {report['train']['seed']}",
        f"holdout_batches: {report['holdout']['batches']}",
        f"holdout_rows: {report['holdout']['rows']}",
        f"holdout_seed: {report['holdout']['seed']}",
        f"candidates_per_batch: {report['candidates_per_batch']}",
        "```",
        "",
        "| mode | batches | top1 | top5 | top10 | mean calls | p95 | p99 | invalid accepts |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode, stats in report["modes"].items():
        lines.append(
            "| "
            + " | ".join(
                (
                    mode,
                    str(stats["batches"]),
                    _fmt(stats["top_1_recall"]),
                    _fmt(stats["top_5_recall"]),
                    _fmt(stats["top_10_recall"]),
                    _fmt(stats["mean_verifier_calls"]),
                    str(stats["p95_verifier_calls"]),
                    str(stats["p99_verifier_calls"]),
                    str(stats["invalid_accept_count"]),
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
        "## Deltas",
        "",
        "Negative mean-call deltas are better.",
        "",
            "```json",
            json.dumps(report["deltas"], indent=2, sort_keys=True),
            "```",
            "",
            "## Interpretation",
            "",
            f"Preferred measured checkpoint: `{report['interpretation']['preferred_measured_checkpoint']}`.",
            "",
            report["interpretation"]["negative_knowledge"],
            "",
            "This is bounded synthetic evidence. It is useful for scorer selection "
            "inside the verifier-backed research harness, and it does not certify "
            "production readiness or v2 bounded-grid optimality.",
        ]
    )
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    return f"{float(value):.3f}"


def _validate_args(args: argparse.Namespace) -> None:
    if args.train_batches <= 0:
        raise SystemExit("--train-batches must be positive")
    if args.holdout_batches <= 0:
        raise SystemExit("--holdout-batches must be positive")
    if args.candidates_per_batch <= 1:
        raise SystemExit("--candidates-per-batch must be greater than one")
    if args.epochs <= 0:
        raise SystemExit("--epochs must be positive")
    if args.learning_rate <= 0:
        raise SystemExit("--learning-rate must be positive")
    if args.margin <= 0:
        raise SystemExit("--margin must be positive")
    if args.winner_pair_weight <= 0:
        raise SystemExit("--winner-pair-weight must be positive")
    if args.objective_gap_weight < 0:
        raise SystemExit("--objective-gap-weight must be nonnegative")
    if args.same_volume_surplus_gap_weight < 0:
        raise SystemExit("--same-volume-surplus-gap-weight must be nonnegative")
    if args.max_pair_weight < 1:
        raise SystemExit("--max-pair-weight must be at least one")


if __name__ == "__main__":
    raise SystemExit(main())
