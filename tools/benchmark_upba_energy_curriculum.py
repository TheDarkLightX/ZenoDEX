#!/usr/bin/env python3
"""Train and benchmark a negative-curriculum UPBA v2 energy ranker."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from statistics import mean
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.upba_v2_energy_model import load_linear_model, save_linear_model
from tools.benchmark_upba_energy_search import benchmark_modes
from tools.evaluate_upba_energy import evaluate_rows
from tools.train_upba_energy import (
    load_negative_curriculum_weights,
    load_rows,
    train_linear_ranker,
)


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
        "--curriculum",
        type=Path,
        default=Path("data/upba_energy/zenoenergy_negative_curriculum_seed20260545.json"),
    )
    parser.add_argument(
        "--baseline-model",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json"),
    )
    parser.add_argument(
        "--output-model",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_linear_curriculum_seed20260517.json"),
    )
    parser.add_argument("--epochs", type=int, default=8)
    parser.add_argument(
        "--max-train-batches",
        type=int,
        help="Optional deterministic prefix of training batches for bounded curriculum experiments.",
    )
    parser.add_argument("--learning-rate", type=float, default=0.02)
    parser.add_argument("--seed", type=int, default=20260517)
    parser.add_argument("--winner-pair-weight", type=float, default=2.0)
    parser.add_argument("--objective-gap-weight", type=float, default=4.0)
    parser.add_argument("--same-volume-surplus-gap-weight", type=float, default=1.0)
    parser.add_argument("--max-pair-weight", type=float, default=8.0)
    parser.add_argument("--stress-batches", type=int, default=80)
    parser.add_argument("--stress-seeds", default="20260546,20260547,20260548")
    parser.add_argument("--candidate-counts", default="20,32,50")
    parser.add_argument("--top-k", type=int, default=10)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    weights = load_negative_curriculum_weights(args.curriculum)
    train_rows_all = load_rows(args.train_dataset)
    train_rows = _limit_train_batches(
        train_rows_all,
        max_train_batches=args.max_train_batches,
    )
    curriculum_model = train_linear_ranker(
        train_rows,
        epochs=args.epochs,
        learning_rate=args.learning_rate,
        margin=1.0,
        seed=args.seed,
        init="hand",
        winner_pair_weight=args.winner_pair_weight,
        objective_gap_weight=args.objective_gap_weight,
        same_volume_surplus_gap_weight=args.same_volume_surplus_gap_weight,
        max_pair_weight=args.max_pair_weight,
        positive_class="hash-winner",
        negative_curriculum_weights=weights,
    )
    args.output_model.parent.mkdir(parents=True, exist_ok=True)
    save_linear_model(curriculum_model, args.output_model)

    baseline_model = load_linear_model(args.baseline_model)
    holdout_rows = load_rows(args.holdout_dataset)
    holdout = {
        "hand": evaluate_rows(holdout_rows, scorer=lambda row: float(row["label"]["hand_energy"]), mode="hand"),
        "baseline": evaluate_rows(
            holdout_rows,
            scorer=lambda row: baseline_model.energy(_features(row)),
            mode="baseline",
        ),
        "curriculum": evaluate_rows(
            holdout_rows,
            scorer=lambda row: curriculum_model.energy(_features(row)),
            mode="curriculum",
        ),
    }

    stress_configs = []
    for candidate_count in _parse_int_csv(args.candidate_counts):
        for seed in _parse_int_csv(args.stress_seeds):
            stress_configs.append(
                {
                    "seed": seed,
                    "candidate_count": candidate_count,
                    "baseline": benchmark_modes(
                        batches=args.stress_batches,
                        candidates_per_batch=candidate_count,
                        seed=seed,
                        model=baseline_model,
                        top_k=args.top_k,
                    ),
                    "curriculum": benchmark_modes(
                        batches=args.stress_batches,
                        candidates_per_batch=candidate_count,
                        seed=seed,
                        model=curriculum_model,
                        top_k=args.top_k,
                    ),
                }
            )

    report = {
        "schema": "zenodex/energy/upba_v2_curriculum_ranker_report/v1",
        "train_dataset": str(args.train_dataset),
        "holdout_dataset": str(args.holdout_dataset),
        "curriculum": str(args.curriculum),
        "baseline_model": str(args.baseline_model),
        "curriculum_model": str(args.output_model),
        "train_rows": len(train_rows),
        "train_rows_available": len(train_rows_all),
        "max_train_batches": args.max_train_batches,
        "holdout_rows": len(holdout_rows),
        "train_args": {
            "epochs": args.epochs,
            "learning_rate": args.learning_rate,
            "seed": args.seed,
            "winner_pair_weight": args.winner_pair_weight,
            "objective_gap_weight": args.objective_gap_weight,
            "same_volume_surplus_gap_weight": args.same_volume_surplus_gap_weight,
            "max_pair_weight": args.max_pair_weight,
            "positive_class": "hash-winner",
        },
        "negative_curriculum_feature_weights": weights,
        "holdout": holdout,
        "stress": {
            "batches_per_config": args.stress_batches,
            "seeds": _parse_int_csv(args.stress_seeds),
            "candidate_counts": _parse_int_csv(args.candidate_counts),
            "top_k": args.top_k,
            "configs": stress_configs,
            "summary": _stress_summary(stress_configs),
        },
    }
    report["interpretation"] = _interpret(report)
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown(report), encoding="utf-8")
    print(encoded)
    return 0


def _features(row: dict[str, Any]) -> list[float]:
    return [float(value) for value in row["features"]]


def _limit_train_batches(
    rows: list[dict[str, Any]],
    *,
    max_train_batches: int | None,
) -> list[dict[str, Any]]:
    if max_train_batches is None:
        return rows
    if max_train_batches <= 0:
        raise SystemExit("--max-train-batches must be positive")
    selected: list[dict[str, Any]] = []
    seen: set[str] = set()
    for row in rows:
        batch_id = str(row["batch_id"])
        if batch_id not in seen:
            if len(seen) >= max_train_batches:
                break
            seen.add(batch_id)
        selected.append(row)
    return selected


def _parse_int_csv(value: str) -> list[int]:
    out = [int(item.strip()) for item in value.split(",") if item.strip()]
    if not out:
        raise SystemExit("CSV option must contain at least one integer")
    return out


def _stress_summary(configs: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "baseline_learned": _mode_summary(configs, family="baseline", mode="learned"),
        "curriculum_learned": _mode_summary(configs, family="curriculum", mode="learned"),
        "baseline_hybrid": _mode_summary(configs, family="baseline", mode="hybrid"),
        "curriculum_hybrid": _mode_summary(configs, family="curriculum", mode="hybrid"),
    }


def _mode_summary(configs: list[dict[str, Any]], *, family: str, mode: str) -> dict[str, Any]:
    rows = [config[family]["modes"][mode] for config in configs]
    return {
        "configs": len(rows),
        "top_1_recall_mean": _mean(rows, "top_1_recall"),
        "top_5_recall_min": min(float(row["top_5_recall"]) for row in rows),
        "top_10_recall_min": min(float(row["top_10_recall"]) for row in rows),
        "checked_stop_at_winner_rate_min": min(
            float(row["checked_stop_at_winner_rate"]) for row in rows
        ),
        "mean_verifier_calls_mean": _mean(rows, "mean_verifier_calls"),
        "p99_verifier_calls_max": max(int(row["p99_verifier_calls"]) for row in rows),
        "invalid_accept_count_total": sum(int(row["invalid_accept_count"]) for row in rows),
        "permutation_violation_count_total": sum(
            int(row["permutation_violation_count"]) for row in rows
        ),
    }


def _mean(rows: list[dict[str, Any]], key: str) -> float:
    return mean(float(row[key]) for row in rows) if rows else 0.0


def _interpret(report: dict[str, Any]) -> dict[str, Any]:
    baseline = report["stress"]["summary"]["baseline_learned"]
    curriculum = report["stress"]["summary"]["curriculum_learned"]
    improved = float(curriculum["mean_verifier_calls_mean"]) < float(
        baseline["mean_verifier_calls_mean"]
    )
    safety_clean = (
        int(curriculum["invalid_accept_count_total"]) == 0
        and int(curriculum["permutation_violation_count_total"]) == 0
    )
    return {
        "curriculum_improved_cross_seed_mean_calls": improved,
        "safety_clean": safety_clean,
        "promotion_decision": "keep_default" if not improved else "candidate_for_more_stress",
        "negative_knowledge": (
            "The rare-disqualifier curriculum did not beat the gap-weighted default "
            "on cross-seed learned mean verifier calls."
            if not improved
            else ""
        ),
    }


def _markdown(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Negative-Curriculum Ranker",
        "",
        "```text",
        f"train_rows: {report['train_rows']}",
        f"train_rows_available: {report['train_rows_available']}",
        f"max_train_batches: {report['max_train_batches']}",
        f"holdout_rows: {report['holdout_rows']}",
        f"baseline_model: {report['baseline_model']}",
        f"curriculum_model: {report['curriculum_model']}",
        f"promotion_decision: {report['interpretation']['promotion_decision']}",
        "```",
        "",
        "## Holdout",
        "",
        "| mode | top1 | top5 | top10 | mean_calls | p99 | invalid_accepts |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode in ("hand", "baseline", "curriculum"):
        stats = report["holdout"][mode]
        lines.append(
            f"| {mode} | {_fmt(stats['top_1_recall'])} | {_fmt(stats['top_5_recall'])} | "
            f"{_fmt(stats['top_10_recall'])} | {_fmt(stats['mean_verifier_calls'])} | "
            f"{stats['p99_verifier_calls']} | {stats['invalid_accept_count']} |"
        )
    lines.extend(
        [
            "",
            "## Cross-Seed Stress",
            "",
            "| mode | configs | top1_mean | top5_min | top10_min | mean_calls | p99_max | invalid_accepts | perm_violations |",
            "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
        ]
    )
    for mode, stats in report["stress"]["summary"].items():
        lines.append(
            f"| {mode} | {stats['configs']} | {_fmt(stats['top_1_recall_mean'])} | "
            f"{_fmt(stats['top_5_recall_min'])} | {_fmt(stats['top_10_recall_min'])} | "
            f"{_fmt(stats['mean_verifier_calls_mean'])} | {stats['p99_verifier_calls_max']} | "
            f"{stats['invalid_accept_count_total']} | {stats['permutation_violation_count_total']} |"
        )
    lines.append("")
    lines.append(str(report["interpretation"]["negative_knowledge"] or "No negative knowledge recorded."))
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    return f"{float(value):.3f}"


if __name__ == "__main__":
    raise SystemExit(main())
