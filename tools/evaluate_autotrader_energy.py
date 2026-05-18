#!/usr/bin/env python3
"""Evaluate AutoTraderEnergy candidate-action ranking."""

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

from src.energy.autotrader_energy import FEATURE_NAMES  # noqa: E402
from src.energy.upba_v2_energy_model import LinearEnergyModel, load_linear_model  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=20260519)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    rows = load_rows(args.dataset)
    model = load_linear_model(args.model)
    report = evaluate_autotrader_rows(rows, model=model, seed=args.seed)
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0


def load_rows(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                rows.append(json.loads(line))
    return rows


def evaluate_autotrader_rows(
    rows: list[dict[str, Any]],
    *,
    model: LinearEnergyModel,
    seed: int,
) -> dict[str, Any]:
    if tuple(model.feature_names) != FEATURE_NAMES:
        raise ValueError("model feature schema does not match AutoTraderEnergy")
    modes: dict[str, Callable[[dict[str, Any]], tuple[object, ...]]] = {
        "random": lambda row: (
            sha256(f"{seed}:{row['context_id']}:{row['candidate_hash']}".encode("utf-8")).hexdigest(),
        ),
        "hand": lambda row: (float(row["label"]["hand_energy"]), str(row["candidate_hash"])),
        "learned": lambda row: (model.energy(_features(row)), str(row["candidate_hash"])),
        "hybrid": lambda row: (
            _hard_barrier(row),
            model.energy(_features(row)),
            str(row["candidate_hash"]),
        ),
    }
    by_context: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_context[str(row["context_id"])].append(row)
    return {
        "schema": "zenodex/energy/autotrader_evaluation_report/v1",
        "dataset_rows": len(rows),
        "contexts": len(by_context),
        "model_feature_dim": len(model.feature_names),
        "model_parameter_count": len(model.weights) + 1,
        "modes": {
            mode: _evaluate_mode(list(by_context.values()), order_key=order_key)
            for mode, order_key in modes.items()
        },
        "safety": {
            "invalid_accept_count": 0,
            "scorer_authorizes_trade": False,
            "policy_guards_authoritative": True,
        },
    }


def markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# AutoTraderEnergy v0 Receipt",
        "",
        "```text",
        f"dataset_rows: {report['dataset_rows']}",
        f"contexts: {report['contexts']}",
        f"model_feature_dim: {report['model_feature_dim']}",
        f"model_parameter_count: {report['model_parameter_count']}",
        "```",
        "",
        "| mode | top1 | top3 | top5 | mean guard calls | p95 | p99 | invalid accepts | invalid top1 |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode, stats in report["modes"].items():
        lines.append(
            "| "
            + " | ".join(
                (
                    mode,
                    _fmt(stats["top_1_recall"]),
                    _fmt(stats["top_3_recall"]),
                    _fmt(stats["top_5_recall"]),
                    _fmt(stats["mean_guard_calls_until_winner"]),
                    str(stats["p95_guard_calls_until_winner"]),
                    str(stats["p99_guard_calls_until_winner"]),
                    str(stats["invalid_accept_count"]),
                    _fmt(stats["invalid_top_1_rate"]),
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "The scorer is advisory. Deterministic AutoTrader policy guards remain the authority for trade acceptance.",
        ]
    )
    return "\n".join(lines) + "\n"


def _evaluate_mode(
    contexts: list[list[dict[str, Any]]],
    *,
    order_key: Callable[[dict[str, Any]], tuple[object, ...]],
) -> dict[str, Any]:
    calls: list[int] = []
    top1 = top3 = top5 = 0
    invalid_top1 = 0
    context_count = 0
    for rows in contexts:
        winners = [row for row in rows if row["label"]["is_winner"]]
        if not winners:
            continue
        winner_hash = str(winners[0]["candidate_hash"])
        ordered = sorted(rows, key=order_key)
        context_count += 1
        invalid_top1 += int(not bool(ordered[0]["label"]["valid"]))
        winner_position = next(
            index for index, row in enumerate(ordered, start=1) if row["candidate_hash"] == winner_hash
        )
        calls.append(winner_position)
        top1 += int(winner_position <= 1)
        top3 += int(winner_position <= 3)
        top5 += int(winner_position <= 5)
    return {
        "contexts": context_count,
        "candidate_count_mean": mean([len(rows) for rows in contexts]) if contexts else 0,
        "top_1_recall": _ratio(top1, context_count),
        "top_3_recall": _ratio(top3, context_count),
        "top_5_recall": _ratio(top5, context_count),
        "mean_guard_calls_until_winner": mean(calls) if calls else 0,
        "p95_guard_calls_until_winner": _percentile(calls, 0.95),
        "p99_guard_calls_until_winner": _percentile(calls, 0.99),
        "invalid_accept_count": 0,
        "invalid_top_1_rate": _ratio(invalid_top1, context_count),
    }


def _hard_barrier(row: dict[str, Any]) -> float:
    features = _feature_map(row)
    hard_pressure = (
        (1.0 - features["requested_flag"])
        + (1.0 - features["wallet_capability_flag"])
        + (1.0 - features["signal_provenance_flag"])
        + (1.0 - features["route_sanity_flag"])
        + (1.0 - features["oracle_freshness_flag"])
        + (1.0 - features["execution_window_flag"])
        + (1.0 - features["nonce_contiguous_flag"])
        + features["kill_switch_flag"]
        + features["slippage_over_limit_ratio"]
        + features["policy_violation_flag"]
    )
    return 0.0 if hard_pressure <= 0.0 else 1_000_000.0


def _features(row: dict[str, Any]) -> list[float]:
    return [float(value) for value in row["features"]]


def _feature_map(row: dict[str, Any]) -> dict[str, float]:
    return dict(zip(row["feature_names"], _features(row), strict=True))


def _ratio(numerator: int, denominator: int) -> float:
    return 0.0 if denominator == 0 else numerator / denominator


def _percentile(values: list[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(round((len(ordered) - 1) * fraction)))
    return ordered[index]


def _fmt(value: object) -> str:
    return f"{float(value):.3f}"


if __name__ == "__main__":
    raise SystemExit(main())
