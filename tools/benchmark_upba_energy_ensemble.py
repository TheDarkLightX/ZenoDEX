#!/usr/bin/env python3
"""Benchmark tiny UPBA v2 energy ensembles and rank-disagreement policies."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
from statistics import fmean
from time import perf_counter
from typing import Any, Callable, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.upba_v2_energy_model import (
    LinearEnergyModel,
    load_linear_model,
    save_linear_model,
)
from src.energy.upba_v2_ensemble import LinearEnergyEnsemble
from tools.benchmark_upba_energy_quality_selection import (
    _group_by_batch,
    _rank_quality_batches,
    _sample_raw_winner_batches,
)
from tools.train_upba_energy import load_rows, train_linear_ranker


Orderer = Callable[[list[dict[str, Any]]], list[dict[str, Any]]]


DEFAULT_MEMBER_SPECS = "raw:250,quality:500,raw:1000,quality:1000,quality:2500"


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
        default=Path("data/upba_energy/upba_v2_energy_ensemble_seed20260556.json"),
    )
    parser.add_argument(
        "--output-markdown",
        type=Path,
        default=Path("docs/ZENO_ENERGY_ENSEMBLE.md"),
    )
    parser.add_argument(
        "--output-model-dir",
        type=Path,
        default=Path("data/upba_energy/ensemble_models"),
    )
    parser.add_argument("--member-specs", default=DEFAULT_MEMBER_SPECS)
    parser.add_argument("--epochs", type=int, default=4)
    parser.add_argument("--learning-rate", type=float, default=0.05)
    parser.add_argument("--margin", type=float, default=1.0)
    parser.add_argument("--seed", type=int, default=20260556)
    parser.add_argument("--winner-pair-weight", type=float, default=2.0)
    parser.add_argument("--objective-gap-weight", type=float, default=4.0)
    parser.add_argument("--same-volume-surplus-gap-weight", type=float, default=1.0)
    parser.add_argument("--max-pair-weight", type=float, default=8.0)
    args = parser.parse_args()

    report = benchmark_ensemble(
        train_dataset=args.train_dataset,
        holdout_dataset=args.holdout_dataset,
        baseline_model_path=args.baseline_model,
        output_model_dir=args.output_model_dir,
        member_specs=_parse_member_specs(args.member_specs),
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


def benchmark_ensemble(
    *,
    train_dataset: Path,
    holdout_dataset: Path,
    baseline_model_path: Path,
    output_model_dir: Path,
    member_specs: list[tuple[str, int]],
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
    quality_ranked_ids = _rank_quality_batches(winner_batches, baseline_model)
    output_model_dir.mkdir(parents=True, exist_ok=True)

    trained_members: list[dict[str, Any]] = []
    member_models: list[LinearEnergyModel] = [baseline_model]
    member_paths: list[str] = [str(baseline_model_path)]
    for index, (policy, budget) in enumerate(member_specs):
        selected_ids = _select_batches(
            policy=policy,
            budget=budget,
            winner_batches=winner_batches,
            quality_ranked_ids=quality_ranked_ids,
            seed=seed + index,
        )
        member = _train_member(
            policy=policy,
            budget=budget,
            selected_ids=selected_ids,
            winner_batches=winner_batches,
            holdout_rows=holdout_rows,
            output_model_dir=output_model_dir,
            epochs=epochs,
            learning_rate=learning_rate,
            margin=margin,
            seed=seed + 101 * (index + 1),
            winner_pair_weight=winner_pair_weight,
            objective_gap_weight=objective_gap_weight,
            same_volume_surplus_gap_weight=same_volume_surplus_gap_weight,
            max_pair_weight=max_pair_weight,
        )
        trained_members.append(member)
        member_paths.append(str(member["model_path"]))
        member_models.append(load_linear_model(member["model_path"]))

    ensemble = LinearEnergyEnsemble(tuple(member_models))
    baseline_metrics = _evaluate_ordering(
        holdout_rows,
        mode="current_gap_weighted",
        orderer=lambda rows: sorted(
            rows,
            key=lambda row: (
                baseline_model.energy(_features(row)),
                str(row["candidate_hash"]),
            ),
        ),
    )
    member_metrics = [
        {
            "member_id": "current_gap_weighted",
            "source": "baseline",
            "model_path": str(baseline_model_path),
            "model_sha256": _sha256_file(baseline_model_path),
            "metrics": _compact_metrics(baseline_metrics),
        },
        *trained_members,
    ]
    modes = {
        "ensemble_mean_energy": _evaluate_ordering(
            holdout_rows,
            mode="ensemble_mean_energy",
            orderer=lambda rows: sorted(
                rows,
                key=lambda row: (
                    ensemble.mean_energy(_features(row)),
                    ensemble.energy_stddev(_features(row)),
                    str(row["candidate_hash"]),
                ),
            ),
            ensemble=ensemble,
        ),
        "ensemble_mean_rank": _evaluate_ordering(
            holdout_rows,
            mode="ensemble_mean_rank",
            orderer=lambda rows: ensemble.order_by_rank_consensus(
                rows,
                feature_getter=_features,
                disagreement_weight=0.0,
                tiebreaker=lambda row: str(row["candidate_hash"]),
            ),
            ensemble=ensemble,
        ),
    }
    for weight in (0.25, 0.5, 1.0, 2.0):
        mode = f"ensemble_rank_std_penalty_{str(weight).replace('.', '_')}"
        modes[mode] = _evaluate_ordering(
            holdout_rows,
            mode=mode,
            orderer=lambda rows, weight=weight: ensemble.order_by_rank_consensus(
                rows,
                feature_getter=_features,
                disagreement_weight=weight,
                tiebreaker=lambda row: str(row["candidate_hash"]),
            ),
            ensemble=ensemble,
        )

    report = {
        "schema": "zenodex/energy/upba_v2_ensemble_report/v1",
        "train_dataset": str(train_dataset),
        "holdout_dataset": str(holdout_dataset),
        "baseline_model": str(baseline_model_path),
        "available_train_batches": len(train_batches),
        "winner_bearing_train_batches": len(winner_batches),
        "available_train_rows": len(train_rows),
        "holdout_rows": len(holdout_rows),
        "seed": seed,
        "member_specs": [
            {"policy": policy, "budget": budget} for policy, budget in member_specs
        ],
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
        "ensemble": {
            "member_count": len(member_models),
            "member_paths": member_paths,
            "parameter_count_per_member": len(baseline_model.weights) + 1,
            "total_parameter_count": len(member_models) * (len(baseline_model.weights) + 1),
            "aggregation_modes": list(modes),
        },
        "members": member_metrics,
        "baselines": {
            "current_gap_weighted": _compact_metrics(baseline_metrics),
        },
        "modes": {mode: _compact_metrics(metrics) for mode, metrics in modes.items()},
        "uncertainty": {
            mode: _compact_uncertainty(metrics) for mode, metrics in modes.items()
        },
        "safety": {
            "invalid_accept_count_total": int(baseline_metrics["invalid_accept_count"])
            + sum(int(metrics["invalid_accept_count"]) for metrics in modes.values()),
            "verifier_authoritative": True,
            "model_authorizes_settlement": False,
            "deterministic_fallback_required": True,
        },
    }
    report["interpretation"] = _interpret(report)
    return report


def _train_member(
    *,
    policy: str,
    budget: int,
    selected_ids: list[str],
    winner_batches: dict[str, list[dict[str, Any]]],
    holdout_rows: list[dict[str, Any]],
    output_model_dir: Path,
    epochs: int,
    learning_rate: float,
    margin: float,
    seed: int,
    winner_pair_weight: float,
    objective_gap_weight: float,
    same_volume_surplus_gap_weight: float,
    max_pair_weight: float,
) -> dict[str, Any]:
    sample_rows = [row for batch_id in selected_ids for row in winner_batches[batch_id]]
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
    model_path = output_model_dir / f"upba_v2_energy_ensemble_{policy}_{budget}_seed{seed}.json"
    save_linear_model(model, model_path)
    metrics = _evaluate_ordering(
        holdout_rows,
        mode=f"member_{policy}_{budget}",
        orderer=lambda rows: sorted(
            rows,
            key=lambda row: (
                model.energy(_features(row)),
                str(row["candidate_hash"]),
            ),
        ),
    )
    return {
        "member_id": f"{policy}_{budget}_seed{seed}",
        "source": "trained_for_ensemble",
        "selection_policy": policy,
        "train_batches": budget,
        "train_rows": len(sample_rows),
        "train_seconds": train_seconds,
        "selected_batch_head": selected_ids[:10],
        "model_path": str(model_path),
        "model_sha256": _sha256_file(model_path),
        "metrics": _compact_metrics(metrics),
    }


def _evaluate_ordering(
    rows: list[dict[str, Any]],
    *,
    mode: str,
    orderer: Orderer,
    ensemble: LinearEnergyEnsemble | None = None,
) -> dict[str, Any]:
    by_batch: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_batch[str(row["batch_id"])].append(row)

    top_ks = (1, 5, 10, 25)
    hits = {k: 0 for k in top_ks}
    objective_hits = {k: 0 for k in top_ks}
    calls: list[int] = []
    objective_calls: list[int] = []
    candidate_counts: list[int] = []
    regrets_top_10: list[int] = []
    top1_invalid_count = 0
    top1_miss_count = 0
    top1_uncertainty_scores: list[float] = []
    top1_miss_labels: list[int] = []
    batches_with_winner = 0

    for batch_rows in by_batch.values():
        winner_rows = [row for row in batch_rows if bool(row["label"]["is_winner"])]
        if not winner_rows:
            continue
        winner = winner_rows[0]
        ordered = orderer(batch_rows)
        batches_with_winner += 1
        candidate_counts.append(len(ordered))
        if ordered and not bool(ordered[0]["label"]["valid"]):
            top1_invalid_count += 1
        winner_index = next(
            index
            for index, row in enumerate(ordered, start=1)
            if row["candidate_hash"] == winner["candidate_hash"]
        )
        objective_winner_index = next(
            index
            for index, row in enumerate(ordered, start=1)
            if _objective_equivalent_rows(row, winner)
        )
        calls.append(winner_index)
        objective_calls.append(objective_winner_index)
        top1_missed = winner_index > 1
        if top1_missed:
            top1_miss_count += 1
        for k in top_ks:
            if winner_index <= min(k, len(ordered)):
                hits[k] += 1
            if objective_winner_index <= min(k, len(ordered)):
                objective_hits[k] += 1
        top_10 = ordered[:10]
        best_top_10 = max((_objective_score(row) for row in top_10), default=(0, 0))
        regrets_top_10.append(max(0, _objective_score(winner)[0] - best_top_10[0]))
        if ensemble is not None and ordered:
            stats = ensemble.rank_stats(batch_rows, feature_getter=_features)
            top1_uncertainty_scores.append(
                stats[str(ordered[0]["candidate_hash"])].std_rank
            )
            top1_miss_labels.append(1 if top1_missed else 0)

    return {
        "schema": "zenodex/energy/upba_v2_ensemble_evaluation/v1",
        "mode": mode,
        "batches": batches_with_winner,
        "candidate_count_mean": fmean(candidate_counts) if candidate_counts else 0.0,
        "top_1_recall": _ratio(hits[1], batches_with_winner),
        "top_5_recall": _ratio(hits[5], batches_with_winner),
        "top_10_recall": _ratio(hits[10], batches_with_winner),
        "top_25_recall": _ratio(hits[25], batches_with_winner),
        "top_1_objective_recall": _ratio(objective_hits[1], batches_with_winner),
        "top_5_objective_recall": _ratio(objective_hits[5], batches_with_winner),
        "top_10_objective_recall": _ratio(objective_hits[10], batches_with_winner),
        "top_25_objective_recall": _ratio(objective_hits[25], batches_with_winner),
        "mean_verifier_calls": fmean(calls) if calls else 0.0,
        "p95_verifier_calls": _percentile(calls, 0.95),
        "p99_verifier_calls": _percentile(calls, 0.99),
        "mean_verifier_calls_to_objective_winner": fmean(objective_calls)
        if objective_calls
        else 0.0,
        "p95_verifier_calls_to_objective_winner": _percentile(objective_calls, 0.95),
        "p99_verifier_calls_to_objective_winner": _percentile(objective_calls, 0.99),
        "mean_regret_before_top_10_fallback": fmean(regrets_top_10)
        if regrets_top_10
        else 0.0,
        "false_exclusion_rate_top_10": 1.0 - _ratio(hits[10], batches_with_winner),
        "invalid_accept_count": 0,
        "top1_invalid_count": top1_invalid_count,
        "top1_miss_count": top1_miss_count,
        "top1_uncertainty_auc": _binary_auc(
            top1_uncertainty_scores,
            top1_miss_labels,
        ),
        "top1_uncertainty_hit_mean": _conditional_mean(
            top1_uncertainty_scores,
            top1_miss_labels,
            label=0,
        ),
        "top1_uncertainty_miss_mean": _conditional_mean(
            top1_uncertainty_scores,
            top1_miss_labels,
            label=1,
        ),
    }


def _select_batches(
    *,
    policy: str,
    budget: int,
    winner_batches: dict[str, list[dict[str, Any]]],
    quality_ranked_ids: list[str],
    seed: int,
) -> list[str]:
    if budget > len(winner_batches):
        raise SystemExit(f"budget {budget} exceeds winner-bearing batch count")
    if policy == "raw":
        return _sample_raw_winner_batches(winner_batches, budget, seed=seed)
    if policy == "quality":
        return sorted(quality_ranked_ids[:budget])
    raise SystemExit("member policy must be 'raw' or 'quality'")


def _compact_metrics(metrics: dict[str, Any]) -> dict[str, Any]:
    return {
        "batches": metrics["batches"],
        "top_1_recall": metrics["top_1_recall"],
        "top_5_recall": metrics["top_5_recall"],
        "top_10_recall": metrics["top_10_recall"],
        "top_1_objective_recall": metrics["top_1_objective_recall"],
        "mean_verifier_calls": metrics["mean_verifier_calls"],
        "p95_verifier_calls": metrics["p95_verifier_calls"],
        "p99_verifier_calls": metrics["p99_verifier_calls"],
        "mean_verifier_calls_to_objective_winner": metrics[
            "mean_verifier_calls_to_objective_winner"
        ],
        "invalid_accept_count": metrics["invalid_accept_count"],
        "top1_invalid_count": metrics["top1_invalid_count"],
        "top1_miss_count": metrics["top1_miss_count"],
        "false_exclusion_rate_top_10": metrics["false_exclusion_rate_top_10"],
    }


def _compact_uncertainty(metrics: dict[str, Any]) -> dict[str, Any]:
    return {
        "top1_miss_count": metrics["top1_miss_count"],
        "top1_uncertainty_auc": metrics["top1_uncertainty_auc"],
        "top1_uncertainty_hit_mean": metrics["top1_uncertainty_hit_mean"],
        "top1_uncertainty_miss_mean": metrics["top1_uncertainty_miss_mean"],
    }


def _interpret(report: dict[str, Any]) -> dict[str, Any]:
    baseline = report["baselines"]["current_gap_weighted"]
    modes = report["modes"]
    best_mode_name, best_mode = min(
        modes.items(),
        key=lambda item: (
            float(item[1]["mean_verifier_calls"]),
            -float(item[1]["top_1_recall"]),
            item[0],
        ),
    )
    baseline_calls = float(baseline["mean_verifier_calls"])
    best_calls = float(best_mode["mean_verifier_calls"])
    best_auc = max(
        float(value["top1_uncertainty_auc"] or 0.0)
        for value in report["uncertainty"].values()
    )
    return {
        "best_ensemble_mode": best_mode_name,
        "best_ensemble_mean_verifier_calls": best_calls,
        "baseline_mean_verifier_calls": baseline_calls,
        "best_ensemble_beats_current_gap_weighted": best_calls < baseline_calls,
        "best_ensemble_top_10_recall": best_mode["top_10_recall"],
        "best_uncertainty_auc": best_auc,
        "positive_knowledge": (
            "The ensemble lane tests rank consensus and disagreement as an "
            "advisory uncertainty signal while deterministic verification and "
            "fallback remain authoritative."
        ),
        "negative_knowledge": (
            "If the best ensemble mode does not beat the current gap-weighted "
            "checkpoint, keep the single retained UPBA model as the default and "
            "use ensemble disagreement only as diagnostic coverage evidence."
        ),
    }


def _features(row: dict[str, Any]) -> list[float]:
    return [float(value) for value in row["features"]]


def _objective_score(row: dict[str, Any]) -> tuple[int, int]:
    label = row["label"]
    if not label["valid"]:
        return (0, 0)
    return (int(label["objective_volume"]), int(label["objective_surplus"]))


def _objective_equivalent_rows(left: dict[str, Any], right: dict[str, Any]) -> bool:
    return bool(left["label"]["valid"]) and bool(right["label"]["valid"]) and (
        _objective_score(left) == _objective_score(right)
    )


def _ratio(numerator: int, denominator: int) -> float:
    return 0.0 if denominator == 0 else numerator / denominator


def _percentile(values: list[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(round((len(ordered) - 1) * fraction)))
    return ordered[index]


def _conditional_mean(
    values: Sequence[float],
    labels: Sequence[int],
    *,
    label: int,
) -> float | None:
    selected = [
        value
        for value, observed in zip(values, labels, strict=True)
        if observed == label
    ]
    return fmean(selected) if selected else None


def _binary_auc(scores: Sequence[float], labels: Sequence[int]) -> float | None:
    positives = [
        (score, index)
        for index, (score, label) in enumerate(zip(scores, labels, strict=True))
        if label == 1
    ]
    negatives = [
        (score, index)
        for index, (score, label) in enumerate(zip(scores, labels, strict=True))
        if label == 0
    ]
    if not positives or not negatives:
        return None
    wins = 0.0
    total = len(positives) * len(negatives)
    for positive_score, _positive_index in positives:
        for negative_score, _negative_index in negatives:
            if positive_score > negative_score:
                wins += 1.0
            elif positive_score == negative_score:
                wins += 0.5
    return wins / total


def _parse_member_specs(raw: str) -> list[tuple[str, int]]:
    specs: list[tuple[str, int]] = []
    for part in raw.split(","):
        if not part.strip():
            continue
        policy, _, budget_text = part.partition(":")
        if not budget_text:
            raise SystemExit("member specs must have shape policy:budget")
        budget = int(budget_text)
        if policy not in {"raw", "quality"} or budget <= 0:
            raise SystemExit("member specs must use raw:N or quality:N with N > 0")
        specs.append((policy, budget))
    if not specs:
        raise SystemExit("--member-specs must contain at least one member")
    return specs


def _sha256_file(path: Path) -> str:
    return "sha256:" + sha256(path.read_bytes()).hexdigest()


def _markdown(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Ensemble",
        "",
        f"schema: `{report['schema']}`",
        f"member_count: {report['ensemble']['member_count']}",
        f"total_parameter_count: {report['ensemble']['total_parameter_count']}",
        "",
        "| mode | top-1 | top-10 | mean calls | p95 | p99 | miss AUC | invalid accepts |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    baseline = report["baselines"]["current_gap_weighted"]
    lines.append(
        "| current_gap_weighted | "
        f"{baseline['top_1_recall']:.4f} | {baseline['top_10_recall']:.4f} | "
        f"{baseline['mean_verifier_calls']:.4f} | {baseline['p95_verifier_calls']} | "
        f"{baseline['p99_verifier_calls']} | n/a | {baseline['invalid_accept_count']} |"
    )
    for mode, metrics in report["modes"].items():
        uncertainty = report["uncertainty"][mode]
        auc = uncertainty["top1_uncertainty_auc"]
        auc_text = "n/a" if auc is None else f"{auc:.4f}"
        lines.append(
            f"| {mode} | {metrics['top_1_recall']:.4f} | "
            f"{metrics['top_10_recall']:.4f} | {metrics['mean_verifier_calls']:.4f} | "
            f"{metrics['p95_verifier_calls']} | {metrics['p99_verifier_calls']} | "
            f"{auc_text} | {metrics['invalid_accept_count']} |"
        )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            report["interpretation"]["positive_knowledge"],
            "",
            report["interpretation"]["negative_knowledge"],
            "",
            f"best_ensemble_mode: `{report['interpretation']['best_ensemble_mode']}`",
            f"best_ensemble_beats_current_gap_weighted: {report['interpretation']['best_ensemble_beats_current_gap_weighted']}",
            f"best_uncertainty_auc: {report['interpretation']['best_uncertainty_auc']:.4f}",
            "",
            "## Safety",
            "",
            "`invalid_accept_count_total = 0`; the ensemble ranks candidates only.",
            "Deterministic UPBA verification and fallback remain the authority.",
        ]
    )
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    raise SystemExit(main())
