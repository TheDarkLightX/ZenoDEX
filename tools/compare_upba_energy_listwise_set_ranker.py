#!/usr/bin/env python3
"""Compare a listwise set-context UPBA v2 ranker against linear baselines."""

from __future__ import annotations

import argparse
import json
import sys
from hashlib import sha256
from pathlib import Path
from statistics import mean
from time import perf_counter
from typing import Any, Callable, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.upba_v2_energy_model import LinearEnergyModel, save_linear_model
from src.energy.upba_v2_listwise_set_ranker import (
    LISTWISE_SET_FEATURE_DIM,
    LISTWISE_SET_FEATURE_NAMES,
    order_rows_by_listwise_set_model,
    train_listwise_set_ranker,
)
from tools.evaluate_upba_energy import evaluate_rows
from tools.generate_upba_energy_dataset import generate_dataset_rows
from tools.train_upba_energy import train_linear_ranker

DEFAULT_TOP_KS = (1, 2, 5, 10, 25)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train-batches", type=int, default=200)
    parser.add_argument("--holdout-batches", type=int, default=100)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--train-seed", type=int, default=20260532)
    parser.add_argument("--holdout-seed", type=int, default=20260533)
    parser.add_argument("--pairwise-epochs", type=int, default=6)
    parser.add_argument("--listwise-epochs", type=int, default=10)
    parser.add_argument("--pairwise-learning-rate", type=float, default=0.03)
    parser.add_argument("--listwise-learning-rate", type=float, default=0.08)
    parser.add_argument("--l2", type=float, default=0.0001)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    parser.add_argument("--output-model-dir", type=Path)
    args = parser.parse_args()

    _validate_args(args)
    report = compare_listwise_set_ranker(
        train_batches=args.train_batches,
        holdout_batches=args.holdout_batches,
        candidates_per_batch=args.candidates_per_batch,
        train_seed=args.train_seed,
        holdout_seed=args.holdout_seed,
        pairwise_epochs=args.pairwise_epochs,
        listwise_epochs=args.listwise_epochs,
        pairwise_learning_rate=args.pairwise_learning_rate,
        listwise_learning_rate=args.listwise_learning_rate,
        l2=args.l2,
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


def compare_listwise_set_ranker(
    *,
    train_batches: int,
    holdout_batches: int,
    candidates_per_batch: int,
    train_seed: int,
    holdout_seed: int,
    pairwise_epochs: int,
    listwise_epochs: int,
    pairwise_learning_rate: float,
    listwise_learning_rate: float,
    l2: float,
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
    pairwise_args = {
        "epochs": pairwise_epochs,
        "learning_rate": pairwise_learning_rate,
        "margin": 1.0,
        "seed": train_seed,
        "init": "zero",
        "winner_pair_weight": 2.0,
        "objective_gap_weight": 4.0,
        "same_volume_surplus_gap_weight": 1.0,
        "max_pair_weight": 8.0,
    }
    aggregate = train_linear_ranker(train_rows, feature_block="aggregate", **pairwise_args)
    set_aware_pairwise = train_linear_ranker(train_rows, feature_block="set-aware", **pairwise_args)
    listwise_set = train_listwise_set_ranker(
        train_rows,
        epochs=listwise_epochs,
        learning_rate=listwise_learning_rate,
        seed=train_seed,
        init_model=set_aware_pairwise,
        l2=l2,
    )

    model_paths: dict[str, str] = {}
    if output_model_dir is not None:
        output_model_dir.mkdir(parents=True, exist_ok=True)
        aggregate_path = output_model_dir / "upba_v2_energy_listwise_aggregate_baseline.json"
        set_aware_path = output_model_dir / "upba_v2_energy_listwise_set_aware_pairwise.json"
        listwise_path = output_model_dir / "upba_v2_energy_listwise_set_ranker.json"
        save_linear_model(aggregate, aggregate_path)
        save_linear_model(set_aware_pairwise, set_aware_path)
        save_linear_model(listwise_set, listwise_path)
        model_paths = {
            "aggregate": str(aggregate_path),
            "set_aware_pairwise": str(set_aware_path),
            "listwise_set": str(listwise_path),
        }

    modes = {
        "random": evaluate_rows(holdout_rows, scorer=None, mode="random", seed=holdout_seed),
        "hand": evaluate_rows(
            holdout_rows,
            scorer=lambda row: float(row["label"]["hand_energy"]),
            mode="hand",
            seed=holdout_seed,
        ),
        "aggregate_pairwise": evaluate_rows(
            holdout_rows,
            scorer=_aggregate_scorer(aggregate),
            mode="learned",
            seed=holdout_seed,
        ),
        "set_aware_pairwise": evaluate_rows(
            holdout_rows,
            scorer=_set_aware_scorer(set_aware_pairwise),
            mode="learned",
            seed=holdout_seed,
        ),
        "listwise_set": evaluate_listwise_rows(
            holdout_rows,
            model=listwise_set,
            top_ks=DEFAULT_TOP_KS,
            seed=holdout_seed,
        ),
    }
    elapsed_ms = (perf_counter() - started) * 1000
    return {
        "schema": "zenodex/energy/upba_v2_listwise_set_ranker_comparison/v1",
        "train": {
            "batches": train_batches,
            "rows": len(train_rows),
            "candidate_count_mean": _candidate_count_mean(train_rows),
            "seed": train_seed,
            "sha256": _stable_digest(train_rows),
        },
        "holdout": {
            "batches": holdout_batches,
            "rows": len(holdout_rows),
            "candidate_count_mean": _candidate_count_mean(holdout_rows),
            "seed": holdout_seed,
            "sha256": _stable_digest(holdout_rows),
        },
        "candidates_per_batch": candidates_per_batch,
        "training": {
            "pairwise_epochs": pairwise_epochs,
            "listwise_epochs": listwise_epochs,
            "pairwise_learning_rate": pairwise_learning_rate,
            "listwise_learning_rate": listwise_learning_rate,
            "listwise_l2": l2,
            "loss": "top_one_listwise_softmax",
        },
        "models": {
            "aggregate_pairwise": {
                "feature_dim": len(aggregate.feature_names),
                "parameter_count": len(aggregate.weights) + 1,
            },
            "set_aware_pairwise": {
                "feature_dim": len(set_aware_pairwise.feature_names),
                "parameter_count": len(set_aware_pairwise.weights) + 1,
            },
            "listwise_set": {
                "feature_dim": LISTWISE_SET_FEATURE_DIM,
                "parameter_count": len(listwise_set.weights) + 1,
            },
        },
        "model_paths": model_paths,
        "modes": modes,
        "deltas": _mode_deltas(modes),
        "interpretation": _interpretation(modes),
        "wall_clock_ms": elapsed_ms,
    }


def evaluate_listwise_rows(
    rows: Sequence[dict[str, Any]],
    *,
    model: LinearEnergyModel,
    top_ks: tuple[int, ...] = DEFAULT_TOP_KS,
    seed: int = 20260517,
) -> dict[str, Any]:
    del seed
    by_batch = _rows_by_batch(rows)
    hits = {k: 0 for k in top_ks}
    checked_stop_hits = {k: 0 for k in top_ks}
    calls: list[int] = []
    candidate_counts: list[int] = []
    regrets_top_10: list[int] = []
    batches_with_winner = 0
    permutation_violations = 0
    checked_stop_at_winner_hits = 0

    for batch_rows in by_batch.values():
        winner_rows = [row for row in batch_rows if bool(row["label"]["is_winner"])]
        if not winner_rows:
            continue
        batches_with_winner += 1
        winner = winner_rows[0]
        ordered = order_rows_by_listwise_set_model(batch_rows, model)
        if sorted(row["candidate_hash"] for row in ordered) != sorted(
            row["candidate_hash"] for row in batch_rows
        ):
            permutation_violations += 1
        winner_index = next(
            index
            for index, row in enumerate(ordered, start=1)
            if row["candidate_hash"] == winner["candidate_hash"]
        )
        calls.append(winner_index)
        candidate_counts.append(len(ordered))
        checked_to_winner = ordered[:winner_index]
        suffix_after_winner = ordered[winner_index:]
        if _checked_stop_holds(winner, checked_to_winner, suffix_after_winner):
            checked_stop_at_winner_hits += 1

        for k in top_ks:
            clamped = min(k, len(ordered))
            if winner_index <= clamped:
                hits[k] += 1
            checked = ordered[:clamped]
            suffix = ordered[clamped:]
            best_checked = _best_valid_row(checked)
            if best_checked is not None and _checked_stop_holds(best_checked, checked, suffix):
                checked_stop_hits[k] += 1
        top_10 = ordered[: min(10, len(ordered))]
        best_top_10 = max((_objective_score(row) for row in top_10), default=(0, 0))
        winner_score = _objective_score(winner)
        regrets_top_10.append(max(0, winner_score[0] - best_top_10[0]))

    return {
        "schema": "zenodex/energy/upba_v2_evaluation_report/v1",
        "mode": "listwise_set",
        "batches": batches_with_winner,
        "candidate_count_mean": mean(candidate_counts) if candidate_counts else 0,
        "top_1_recall": _ratio(hits.get(1, 0), batches_with_winner),
        "top_5_recall": _ratio(hits.get(5, 0), batches_with_winner),
        "top_10_recall": _ratio(hits.get(10, 0), batches_with_winner),
        "top_25_recall": _ratio(hits.get(25, 0), batches_with_winner),
        "mean_verifier_calls": mean(calls) if calls else 0,
        "p95_verifier_calls": _percentile(calls, 0.95),
        "p99_verifier_calls": _percentile(calls, 0.99),
        "mean_regret_before_top_10_fallback": mean(regrets_top_10) if regrets_top_10 else 0,
        "false_exclusion_rate_top_10": 1.0 - _ratio(hits.get(10, 0), batches_with_winner),
        "invalid_accept_count": 0,
        "permutation_violation_count": permutation_violations,
        "checked_stop_at_winner_rate": _ratio(checked_stop_at_winner_hits, batches_with_winner),
        "top_k_checked_stop_rates": {
            str(k): _ratio(checked_stop_hits[k], batches_with_winner)
            for k in top_ks
        },
    }


def _aggregate_scorer(model: LinearEnergyModel) -> Callable[[dict[str, Any]], float]:
    return lambda row: model.energy([float(value) for value in row["features"]])


def _set_aware_scorer(model: LinearEnergyModel) -> Callable[[dict[str, Any]], float]:
    return lambda row: model.energy([float(value) for value in row["set_aware_features"]])


def _mode_deltas(modes: dict[str, dict[str, Any]]) -> dict[str, Any]:
    aggregate = modes["aggregate_pairwise"]
    set_aware = modes["set_aware_pairwise"]
    listwise = modes["listwise_set"]
    return {
        "listwise_vs_aggregate_pairwise": _delta(listwise, aggregate),
        "listwise_vs_set_aware_pairwise": _delta(listwise, set_aware),
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
    aggregate = modes["aggregate_pairwise"]
    set_aware = modes["set_aware_pairwise"]
    listwise = modes["listwise_set"]
    baseline = aggregate
    baseline_name = "aggregate_pairwise"
    if (
        float(set_aware["mean_verifier_calls"]),
        -float(set_aware["top_1_recall"]),
    ) < (
        float(aggregate["mean_verifier_calls"]),
        -float(aggregate["top_1_recall"]),
    ):
        baseline = set_aware
        baseline_name = "set_aware_pairwise"
    improved = (
        float(listwise["mean_verifier_calls"]) < float(baseline["mean_verifier_calls"])
        and float(listwise["top_10_recall"]) >= float(baseline["top_10_recall"])
    )
    invalid_accept_count_total = sum(int(stats["invalid_accept_count"]) for stats in modes.values())
    permutation_violation_count_total = int(listwise["permutation_violation_count"])
    if improved:
        recommendation = (
            "Keep the listwise set-context ranker as a candidate for larger cross-seed stress."
        )
        negative_knowledge = ""
    else:
        recommendation = (
            "Keep the aggregate gap-weighted baseline as the measured default and treat "
            "the current listwise context as unpromoted."
        )
        negative_knowledge = (
            "The first listwise set-context ranker did not improve mean verifier calls "
            "against the strongest pairwise baseline on this bounded synthetic split."
        )
    return {
        "best_pairwise_baseline": baseline_name,
        "listwise_improved_over_best_pairwise": improved,
        "all_modes_invalid_accept_count": invalid_accept_count_total,
        "permutation_violation_count": permutation_violation_count_total,
        "negative_knowledge": negative_knowledge,
        "recommendation": recommendation,
    }


def _rows_by_batch(rows: Sequence[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        grouped.setdefault(str(row["batch_id"]), []).append(row)
    return grouped


def _candidate_count_mean(rows: Sequence[dict[str, Any]]) -> float:
    counts = [len(batch_rows) for batch_rows in _rows_by_batch(rows).values()]
    return mean(counts) if counts else 0.0


def _checked_stop_holds(
    winner: dict[str, Any],
    checked: Sequence[dict[str, Any]],
    suffix: Sequence[dict[str, Any]],
) -> bool:
    if not bool(winner["label"]["valid"]):
        return False
    if all(row["candidate_hash"] != winner["candidate_hash"] for row in checked):
        return False
    return all(_row_cannot_beat(winner, row) for row in (*checked, *suffix))


def _row_cannot_beat(winner: dict[str, Any], other: dict[str, Any]) -> bool:
    if not bool(other["label"]["valid"]):
        return True
    winner_score = _objective_score(winner)
    other_score = _objective_score(other)
    if other_score[0] < winner_score[0]:
        return True
    return other_score[0] == winner_score[0] and other_score[1] <= winner_score[1]


def _best_valid_row(rows: Sequence[dict[str, Any]]) -> dict[str, Any] | None:
    valid = [row for row in rows if bool(row["label"]["valid"])]
    if not valid:
        return None
    return max(valid, key=lambda row: (*_objective_score(row), str(row["candidate_hash"])))


def _objective_score(row: dict[str, Any]) -> tuple[int, int]:
    return (
        int(row["label"]["objective_volume"]),
        int(row["label"]["objective_surplus"]),
    )


def _ratio(numerator: int, denominator: int) -> float:
    return 0.0 if denominator == 0 else numerator / denominator


def _percentile(values: Sequence[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(round((len(ordered) - 1) * fraction)))
    return ordered[index]


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Listwise Set Ranker",
        "",
        "```text",
        f"train_batches: {report['train']['batches']}",
        f"train_rows: {report['train']['rows']}",
        f"train_seed: {report['train']['seed']}",
        f"holdout_batches: {report['holdout']['batches']}",
        f"holdout_rows: {report['holdout']['rows']}",
        f"holdout_seed: {report['holdout']['seed']}",
        f"candidates_per_batch: {report['candidates_per_batch']}",
        "loss: top_one_listwise_softmax",
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
            f"Best pairwise baseline: `{report['interpretation']['best_pairwise_baseline']}`.",
            "",
            f"Listwise improved over best pairwise: `{str(report['interpretation']['listwise_improved_over_best_pairwise']).lower()}`.",
            "",
            report["interpretation"]["recommendation"],
        ]
    )
    if report["interpretation"]["negative_knowledge"]:
        lines.extend(["", report["interpretation"]["negative_knowledge"]])
    lines.extend(
        [
            "",
            "The model only changes candidate order. Deterministic verification, full fallback, and checked-stop certificate obligations remain unchanged.",
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
    if args.pairwise_epochs <= 0:
        raise SystemExit("--pairwise-epochs must be positive")
    if args.listwise_epochs <= 0:
        raise SystemExit("--listwise-epochs must be positive")
    if args.pairwise_learning_rate <= 0:
        raise SystemExit("--pairwise-learning-rate must be positive")
    if args.listwise_learning_rate <= 0:
        raise SystemExit("--listwise-learning-rate must be positive")
    if args.l2 < 0:
        raise SystemExit("--l2 must be nonnegative")


def _stable_digest(rows: Sequence[dict[str, Any]]) -> str:
    digest = sha256()
    for row in rows:
        digest.update(json.dumps(row, sort_keys=True, separators=(",", ":")).encode("utf-8"))
        digest.update(b"\n")
    return "0x" + digest.hexdigest()


if __name__ == "__main__":
    raise SystemExit(main())
