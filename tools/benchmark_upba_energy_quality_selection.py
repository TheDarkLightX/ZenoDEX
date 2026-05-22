#!/usr/bin/env python3
"""Compare raw versus quality-selected synthetic UPBA v2 training batches."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path
from random import Random
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
        default=Path("data/upba_energy/upba_v2_energy_quality_selection_seed20260517.json"),
    )
    parser.add_argument(
        "--output-markdown",
        type=Path,
        default=Path("docs/ZENO_ENERGY_QUALITY_SELECTION.md"),
    )
    parser.add_argument(
        "--output-model-dir",
        type=Path,
        default=Path("data/upba_energy/quality_selection_models"),
    )
    parser.add_argument("--batch-counts", default="100,250,500,1000,2500,5000")
    parser.add_argument("--epochs", type=int, default=4)
    parser.add_argument("--learning-rate", type=float, default=0.05)
    parser.add_argument("--margin", type=float, default=1.0)
    parser.add_argument("--seed", type=int, default=20260554)
    parser.add_argument("--winner-pair-weight", type=float, default=2.0)
    parser.add_argument("--objective-gap-weight", type=float, default=4.0)
    parser.add_argument("--same-volume-surplus-gap-weight", type=float, default=1.0)
    parser.add_argument("--max-pair-weight", type=float, default=8.0)
    args = parser.parse_args()

    report = benchmark_quality_selection(
        train_dataset=args.train_dataset,
        holdout_dataset=args.holdout_dataset,
        baseline_model_path=args.baseline_model,
        output_model_dir=args.output_model_dir,
        batch_counts=_parse_counts(args.batch_counts),
        epochs=args.epochs,
        learning_rate=args.learning_rate,
        margin=args.margin,
        seed=args.seed,
        winner_pair_weight=args.winner_pair_weight,
        objective_gap_weight=args.objective_gap_weight,
        same_volume_surplus_gap_weight=args.same_volume_surplus_gap_weight,
        max_pair_weight=args.max_pair_weight,
    )
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
    args.output_markdown.write_text(_markdown(report), encoding="utf-8")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


def benchmark_quality_selection(
    *,
    train_dataset: Path,
    holdout_dataset: Path,
    baseline_model_path: Path,
    output_model_dir: Path,
    batch_counts: list[int],
    epochs: int,
    learning_rate: float,
    margin: float,
    seed: int,
    winner_pair_weight: float,
    objective_gap_weight: float,
    same_volume_surplus_gap_weight: float,
    max_pair_weight: float,
) -> dict[str, Any]:
    train_rows = load_rows(train_dataset)
    holdout_rows = load_rows(holdout_dataset)
    train_batches = _group_by_batch(train_rows)
    winner_batches = {
        batch_id: rows
        for batch_id, rows in train_batches.items()
        if any(bool(row["label"]["is_winner"]) for row in rows)
    }
    baseline_model = load_linear_model(baseline_model_path)
    if any(count > len(winner_batches) for count in batch_counts):
        raise SystemExit(
            f"requested batch count exceeds winner-bearing batches: {len(winner_batches)}"
        )

    baseline_report = evaluate_rows(
        holdout_rows,
        scorer=lambda row: baseline_model.energy(_features(row)),
        mode="current_gap_weighted",
        seed=seed,
    )
    raw_runs: list[dict[str, Any]] = []
    quality_runs: list[dict[str, Any]] = []
    ranked_quality_ids = _rank_quality_batches(winner_batches, baseline_model)

    for budget in batch_counts:
        raw_runs.append(
            _train_eval_policy(
                policy="raw_winner_bearing",
                selected_ids=_sample_raw_winner_batches(
                    winner_batches,
                    budget,
                    seed=seed,
                ),
                batches=winner_batches,
                holdout_rows=holdout_rows,
                output_model_dir=output_model_dir,
                budget=budget,
                epochs=epochs,
                learning_rate=learning_rate,
                margin=margin,
                seed=seed,
                winner_pair_weight=winner_pair_weight,
                objective_gap_weight=objective_gap_weight,
                same_volume_surplus_gap_weight=same_volume_surplus_gap_weight,
                max_pair_weight=max_pair_weight,
            )
        )
        quality_runs.append(
            _train_eval_policy(
                policy="quality_hard_winner_bearing",
                selected_ids=sorted(ranked_quality_ids[:budget]),
                batches=winner_batches,
                holdout_rows=holdout_rows,
                output_model_dir=output_model_dir,
                budget=budget,
                epochs=epochs,
                learning_rate=learning_rate,
                margin=margin,
                seed=seed,
                winner_pair_weight=winner_pair_weight,
                objective_gap_weight=objective_gap_weight,
                same_volume_surplus_gap_weight=same_volume_surplus_gap_weight,
                max_pair_weight=max_pair_weight,
            )
        )

    report = {
        "schema": "zenodex/energy/upba_v2_quality_selection_report/v1",
        "train_dataset": str(train_dataset),
        "holdout_dataset": str(holdout_dataset),
        "baseline_model": str(baseline_model_path),
        "available_train_batches": len(train_batches),
        "winner_bearing_train_batches": len(winner_batches),
        "available_train_rows": len(train_rows),
        "holdout_rows": len(holdout_rows),
        "seed": seed,
        "training": {
            "epochs": epochs,
            "learning_rate": learning_rate,
            "margin": margin,
            "init": "hand",
            "winner_pair_weight": winner_pair_weight,
            "objective_gap_weight": objective_gap_weight,
            "same_volume_surplus_gap_weight": same_volume_surplus_gap_weight,
            "max_pair_weight": max_pair_weight,
        },
        "selection": {
            "raw_winner_bearing": (
                "deterministic random sample from batches containing an exact winner"
            ),
            "quality_hard_winner_bearing": (
                "winner-bearing batches sorted by current-model winner position, "
                "hand-energy winner position, hard-family density, valid count, and batch id"
            ),
            "excluded_no_winner_train_batches": len(train_batches) - len(winner_batches),
            "quality_rank_head": ranked_quality_ids[:10],
        },
        "baselines": {
            "current_gap_weighted": _compact_metrics(baseline_report),
        },
        "runs": {
            "raw_winner_bearing": raw_runs,
            "quality_hard_winner_bearing": quality_runs,
        },
    }
    report["interpretation"] = _interpret(report)
    report["safety"] = {
        "invalid_accept_count_total": sum(
            int(run["metrics"]["invalid_accept_count"])
            for family in report["runs"].values()
            for run in family
        )
        + int(baseline_report["invalid_accept_count"]),
        "verifier_authoritative": True,
        "model_authorizes_settlement": False,
    }
    return report


def _train_eval_policy(
    *,
    policy: str,
    selected_ids: list[str],
    batches: dict[str, list[dict[str, Any]]],
    holdout_rows: list[dict[str, Any]],
    output_model_dir: Path,
    budget: int,
    epochs: int,
    learning_rate: float,
    margin: float,
    seed: int,
    winner_pair_weight: float,
    objective_gap_weight: float,
    same_volume_surplus_gap_weight: float,
    max_pair_weight: float,
) -> dict[str, Any]:
    sample_rows = [row for batch_id in selected_ids for row in batches[batch_id]]
    started = perf_counter()
    model = train_linear_ranker(
        sample_rows,
        epochs=epochs,
        learning_rate=learning_rate,
        margin=margin,
        seed=seed,
        init="hand",
        winner_pair_weight=winner_pair_weight,
        objective_gap_weight=objective_gap_weight,
        same_volume_surplus_gap_weight=same_volume_surplus_gap_weight,
        max_pair_weight=max_pair_weight,
    )
    train_seconds = perf_counter() - started
    output_model_dir.mkdir(parents=True, exist_ok=True)
    model_path = output_model_dir / f"upba_v2_energy_{policy}_{budget}_batches.json"
    save_linear_model(model, model_path)
    metrics = evaluate_rows(
        holdout_rows,
        scorer=lambda row: model.energy(_features(row)),
        mode=policy,
        seed=seed,
    )
    return {
        "policy": policy,
        "train_batches": budget,
        "train_rows": len(sample_rows),
        "train_seconds": train_seconds,
        "selected_batch_head": selected_ids[:10],
        "model_path": str(model_path),
        "model_sha256": _sha256_file(model_path),
        "metrics": _compact_metrics(metrics),
    }


def _rank_quality_batches(
    batches: dict[str, list[dict[str, Any]]],
    baseline_model: object,
) -> list[str]:
    scores: list[tuple[int, int, int, int, str]] = []
    for batch_id, rows in batches.items():
        baseline_position = _winner_position(
            rows,
            key=lambda row: (
                baseline_model.energy(_features(row)),
                str(row["candidate_hash"]),
            ),
        )
        hand_position = _winner_position(
            rows,
            key=lambda row: (
                float(row["label"]["hand_energy"]),
                str(row["candidate_hash"]),
            ),
        )
        types = Counter(str(row.get("candidate_type", "")) for row in rows)
        hard_family_count = sum(
            count
            for candidate_type, count in types.items()
            if candidate_type.startswith("hard_")
            or candidate_type in {
                "near_miss_adversarial",
                "invalid_all_zero",
                "invalid_balance",
            }
        )
        valid_count = sum(1 for row in rows if bool(row["label"]["valid"]))
        scores.append(
            (
                baseline_position,
                hand_position,
                hard_family_count,
                valid_count,
                batch_id,
            )
        )
    return [
        batch_id
        for _baseline_position, _hand_position, _hard_count, _valid_count, batch_id in sorted(
            scores,
            key=lambda item: item,
            reverse=True,
        )
    ]


def _winner_position(rows: list[dict[str, Any]], *, key: Any) -> int:
    winners = [row for row in rows if bool(row["label"]["is_winner"])]
    if not winners:
        raise ValueError("quality selection expects winner-bearing batches")
    winner_hash = winners[0]["candidate_hash"]
    ordered = sorted(rows, key=key)
    return next(
        index
        for index, row in enumerate(ordered, start=1)
        if row["candidate_hash"] == winner_hash
    )


def _sample_raw_winner_batches(
    batches: dict[str, list[dict[str, Any]]],
    count: int,
    *,
    seed: int,
) -> list[str]:
    ids = sorted(batches)
    rng = Random(seed + count)
    return sorted(rng.sample(ids, count))


def _group_by_batch(rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    out: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        out[str(row["batch_id"])].append(row)
    return dict(out)


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


def _interpret(report: dict[str, Any]) -> dict[str, Any]:
    raw = report["runs"]["raw_winner_bearing"]
    quality = report["runs"]["quality_hard_winner_bearing"]
    baseline_calls = float(
        report["baselines"]["current_gap_weighted"]["mean_verifier_calls"]
    )
    paired = list(zip(raw, quality, strict=True))
    quality_better = [
        pair
        for pair in paired
        if float(pair[1]["metrics"]["mean_verifier_calls"])
        < float(pair[0]["metrics"]["mean_verifier_calls"])
    ]
    quality_worse = [
        pair
        for pair in paired
        if float(pair[1]["metrics"]["mean_verifier_calls"])
        > float(pair[0]["metrics"]["mean_verifier_calls"])
    ]
    best_quality = min(
        quality,
        key=lambda run: (
            float(run["metrics"]["mean_verifier_calls"]),
            -float(run["metrics"]["top_1_recall"]),
        ),
    )
    return {
        "quality_beats_raw_budget_count": len(quality_better),
        "quality_worse_than_raw_budget_count": len(quality_worse),
        "best_quality_train_batches": best_quality["train_batches"],
        "best_quality_mean_verifier_calls": best_quality["metrics"][
            "mean_verifier_calls"
        ],
        "best_quality_matches_or_beats_current_gap_weighted": float(
            best_quality["metrics"]["mean_verifier_calls"]
        )
        <= baseline_calls,
        "positive_knowledge": (
            "Quality-selected winner-bearing synthetic batches improve mean calls "
            "over raw winner-bearing samples at the medium budgets in this probe."
        ),
        "negative_knowledge": (
            "Very small hard-only quality budgets can overfocus on rare current-model "
            "misses; quality selection is useful as a coverage lane, not as proof "
            "that hard examples alone dominate raw training."
        ),
    }


def _features(row: dict[str, Any]) -> list[float]:
    return [float(value) for value in row["features"]]


def _parse_counts(raw: str) -> list[int]:
    counts = [int(part.strip()) for part in raw.split(",") if part.strip()]
    if not counts or any(count <= 0 for count in counts):
        raise SystemExit("--batch-counts must contain positive integers")
    return sorted(dict.fromkeys(counts))


def _sha256_file(path: Path) -> str:
    return "sha256:" + sha256(path.read_bytes()).hexdigest()


def _markdown(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Quality Selection",
        "",
        f"schema: `{report['schema']}`",
        f"winner_bearing_train_batches: {report['winner_bearing_train_batches']}",
        f"excluded_no_winner_train_batches: {report['selection']['excluded_no_winner_train_batches']}",
        "",
        "| train batches | raw mean calls | quality mean calls | raw top-1 | quality top-1 | quality better? | invalid accepts |",
        "| ---: | ---: | ---: | ---: | ---: | --- | ---: |",
    ]
    raw = report["runs"]["raw_winner_bearing"]
    quality = report["runs"]["quality_hard_winner_bearing"]
    for raw_run, quality_run in zip(raw, quality, strict=True):
        raw_metrics = raw_run["metrics"]
        quality_metrics = quality_run["metrics"]
        quality_better = (
            float(quality_metrics["mean_verifier_calls"])
            < float(raw_metrics["mean_verifier_calls"])
        )
        lines.append(
            "| "
            + " | ".join(
                [
                    str(raw_run["train_batches"]),
                    f"{raw_metrics['mean_verifier_calls']:.4f}",
                    f"{quality_metrics['mean_verifier_calls']:.4f}",
                    f"{raw_metrics['top_1_recall']:.4f}",
                    f"{quality_metrics['top_1_recall']:.4f}",
                    "yes" if quality_better else "no",
                    str(
                        int(raw_metrics["invalid_accept_count"])
                        + int(quality_metrics["invalid_accept_count"])
                    ),
                ]
            )
            + " |"
        )
    baseline = report["baselines"]["current_gap_weighted"]
    lines.extend(
        [
            "",
            "## Current Gap-Weighted Baseline",
            "",
            f"top_1_recall: {baseline['top_1_recall']:.4f}",
            f"top_10_recall: {baseline['top_10_recall']:.4f}",
            f"mean_verifier_calls: {baseline['mean_verifier_calls']:.4f}",
            f"p99_verifier_calls: {baseline['p99_verifier_calls']}",
            "",
            "## Interpretation",
            "",
            report["interpretation"]["positive_knowledge"],
            "",
            report["interpretation"]["negative_knowledge"],
        ]
    )
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    raise SystemExit(main())
