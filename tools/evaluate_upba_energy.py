#!/usr/bin/env python3
"""Evaluate UPBA v2 energy rankings from a generated JSONL dataset."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
from statistics import mean
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.upba_v2_energy_model import load_linear_model


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, required=True)
    parser.add_argument("--model", type=Path)
    parser.add_argument("--mode", choices=("hand", "learned", "hybrid", "random"), default="hand")
    parser.add_argument("--seed", type=int, default=20260517)
    args = parser.parse_args()

    rows = _load_rows(args.dataset)
    scorer = _scorer_for_args(args)
    report = evaluate_rows(rows, scorer=scorer, mode=args.mode, seed=args.seed)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


def evaluate_rows(
    rows: list[dict[str, Any]],
    *,
    scorer: Callable[[dict[str, Any]], float] | None,
    mode: str,
    seed: int = 20260517,
) -> dict[str, Any]:
    by_batch: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_batch[str(row["batch_id"])].append(row)

    top_ks = (1, 5, 10, 25)
    hits = {k: 0 for k in top_ks}
    calls: list[int] = []
    candidate_counts: list[int] = []
    regrets_top_10: list[int] = []
    batches_with_winner = 0
    invalid_accept_count = 0

    for batch_rows in by_batch.values():
        winner_rows = [row for row in batch_rows if row["label"]["is_winner"]]
        if not winner_rows:
            continue
        batches_with_winner += 1
        winner = winner_rows[0]
        ordered = _ordered_rows(batch_rows, scorer=scorer, mode=mode, seed=seed)
        candidate_counts.append(len(ordered))
        winner_index = next(
            index for index, row in enumerate(ordered, start=1) if row["candidate_hash"] == winner["candidate_hash"]
        )
        calls.append(winner_index)
        for k in top_ks:
            if winner_index <= min(k, len(ordered)):
                hits[k] += 1
        top_10 = ordered[:10]
        best_top_10 = max((_objective_score(row) for row in top_10), default=(0, 0))
        winner_score = _objective_score(winner)
        regrets_top_10.append(max(0, winner_score[0] - best_top_10[0]))
        invalid_accept_count += sum(1 for row in ordered if row["label"]["valid"] is False and False)

    return {
        "schema": "zenodex/energy/upba_v2_evaluation_report/v1",
        "mode": mode,
        "batches": batches_with_winner,
        "candidate_count_mean": mean(candidate_counts) if candidate_counts else 0,
        "top_1_recall": _ratio(hits[1], batches_with_winner),
        "top_5_recall": _ratio(hits[5], batches_with_winner),
        "top_10_recall": _ratio(hits[10], batches_with_winner),
        "top_25_recall": _ratio(hits[25], batches_with_winner),
        "mean_verifier_calls": mean(calls) if calls else 0,
        "p95_verifier_calls": _percentile(calls, 0.95),
        "p99_verifier_calls": _percentile(calls, 0.99),
        "mean_regret_before_top_10_fallback": mean(regrets_top_10) if regrets_top_10 else 0,
        "false_exclusion_rate_top_10": 1.0 - _ratio(hits[10], batches_with_winner),
        "invalid_accept_count": invalid_accept_count,
    }


def _scorer_for_args(args: argparse.Namespace) -> Callable[[dict[str, Any]], float] | None:
    if args.mode == "hand":
        return lambda row: float(row["label"]["hand_energy"])
    if args.mode == "learned":
        if args.model is None:
            raise SystemExit("--model is required for learned mode")
        model = load_linear_model(args.model)
        return lambda row: model.energy([float(value) for value in row["features"]])
    if args.mode == "hybrid":
        if args.model is None:
            raise SystemExit("--model is required for hybrid mode")
        model = load_linear_model(args.model)
        return lambda row: model.energy([float(value) for value in row["features"]])
    return None


def _ordered_rows(
    rows: list[dict[str, Any]],
    *,
    scorer: Callable[[dict[str, Any]], float] | None,
    mode: str,
    seed: int,
) -> list[dict[str, Any]]:
    if mode == "random":
        return sorted(
            rows,
            key=lambda row: sha256(
                f"{seed}:{row['batch_id']}:{row['candidate_hash']}".encode("utf-8")
            ).hexdigest(),
        )
    if mode == "hybrid":
        if scorer is None:
            raise ValueError("hybrid mode requires a learned scorer")
        return sorted(
            rows,
            key=lambda row: (
                _hard_barrier_from_row(row),
                scorer(row),
                str(row["candidate_hash"]),
            ),
        )
    if scorer is None:
        return list(rows)
    return sorted(rows, key=lambda row: (scorer(row), str(row["candidate_hash"])))


def _objective_score(row: dict[str, Any]) -> tuple[int, int]:
    label = row["label"]
    if not label["valid"]:
        return (0, 0)
    return (int(label["objective_volume"]), int(label["objective_surplus"]))


def _hard_barrier_from_row(row: dict[str, Any]) -> float:
    features = {
        str(name): float(value)
        for name, value in zip(row["feature_names"], row["features"], strict=True)
    }

    def present(name: str) -> int:
        return 1 if features.get(name, 0.0) > 0.0 else 0

    return (
        1_000_000.0
        * (
            present("candidate_balance_violation_count_norm")
            + present("candidate_limit_violation_count_norm")
            + present("candidate_negative_reserve_flag")
            + present("candidate_invariant_violation_flag")
        )
        + 100_000.0
        * (
            present("candidate_noncanonical_fill_vector_flag")
            + present("candidate_schema_policy_mismatch_flag")
            + present("candidate_price_objective_violation_flag")
            + present("candidate_output_mismatch_count_norm")
            + present("candidate_fill_coverage_violation_flag")
            + present("candidate_duplicate_fill_id_flag")
            + present("candidate_unknown_fill_id_count_norm")
            + present("candidate_executed_input_over_amount_count_norm")
            + present("candidate_output_without_input_count_norm")
        )
        + 50_000.0 * present("candidate_price_ratio_unreduced_flag")
        + 10_000.0 * present("candidate_zero_net_input_count_norm")
    )


def _load_rows(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                rows.append(json.loads(line))
    return rows


def _ratio(numerator: int, denominator: int) -> float:
    return 0.0 if denominator == 0 else numerator / denominator


def _percentile(values: list[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(round((len(ordered) - 1) * fraction)))
    return ordered[index]


if __name__ == "__main__":
    raise SystemExit(main())
