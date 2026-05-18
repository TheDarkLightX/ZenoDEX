#!/usr/bin/env python3
"""Train a tiny no-dependency AutoTraderEnergy linear ranker."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path
from random import Random
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.autotrader_energy import FEATURE_NAMES, initial_autotrader_hand_model  # noqa: E402
from src.energy.upba_v2_energy_model import LinearEnergyModel, save_linear_model  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, required=True)
    parser.add_argument("--output-model", type=Path, required=True)
    parser.add_argument("--epochs", type=int, default=12)
    parser.add_argument("--learning-rate", type=float, default=0.05)
    parser.add_argument("--margin", type=float, default=1.0)
    parser.add_argument("--seed", type=int, default=20260518)
    parser.add_argument("--init", choices=("zero", "hand"), default="zero")
    args = parser.parse_args()

    rows = load_rows(args.dataset)
    model = train_autotrader_linear_ranker(
        rows,
        epochs=args.epochs,
        learning_rate=args.learning_rate,
        margin=args.margin,
        seed=args.seed,
        init=args.init,
    )
    args.output_model.parent.mkdir(parents=True, exist_ok=True)
    save_linear_model(model, args.output_model)
    print(json.dumps({
        "schema": "zenodex/energy/autotrader_training_receipt/v1",
        "backend": "linear_pairwise_hinge",
        "rows": len(rows),
        "feature_dim": len(model.feature_names),
        "parameters": len(model.weights) + 1,
        "epochs": args.epochs,
        "learning_rate": args.learning_rate,
        "margin": args.margin,
        "model_path": str(args.output_model),
    }, indent=2, sort_keys=True))
    return 0


def load_rows(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                rows.append(json.loads(line))
    return rows


def train_autotrader_linear_ranker(
    rows: list[dict[str, Any]],
    *,
    epochs: int,
    learning_rate: float,
    margin: float,
    seed: int,
    init: str,
) -> LinearEnergyModel:
    if not rows:
        raise ValueError("training dataset is empty")
    if tuple(rows[0]["feature_names"]) != FEATURE_NAMES:
        raise ValueError("dataset feature schema does not match AutoTraderEnergy")
    weights = (
        list(initial_autotrader_hand_model().weights)
        if init == "hand"
        else [0.0 for _ in FEATURE_NAMES]
    )
    by_context: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_context[str(row["context_id"])].append(row)
    contexts = list(by_context.values())
    rng = Random(seed)
    for _epoch in range(epochs):
        rng.shuffle(contexts)
        for context_rows in contexts:
            ranked = sorted(context_rows, key=_label_score, reverse=True)
            for good_index, good in enumerate(ranked):
                good_x = _features(good)
                for bad in ranked[good_index + 1 :]:
                    if _label_score(good) <= _label_score(bad):
                        continue
                    bad_x = _features(bad)
                    if margin + _dot(weights, good_x) - _dot(weights, bad_x) <= 0:
                        continue
                    pair_weight = 2.0 if good["label"]["is_winner"] else 1.0
                    for index, (good_value, bad_value) in enumerate(zip(good_x, bad_x, strict=True)):
                        weights[index] -= learning_rate * pair_weight * (good_value - bad_value)
    return LinearEnergyModel(feature_names=FEATURE_NAMES, weights=tuple(weights), bias=0.0)


def _label_score(row: dict[str, Any]) -> tuple[int, int, int, str]:
    label = row["label"]
    return (
        1 if label["valid"] else 0,
        int(label["objective_utility"]),
        -int(label["risk_penalty"]),
        str(row["candidate_hash"]),
    )


def _features(row: dict[str, Any]) -> list[float]:
    return [float(value) for value in row["features"]]


def _dot(weights: list[float], values: list[float]) -> float:
    return sum(weight * value for weight, value in zip(weights, values, strict=True))


if __name__ == "__main__":
    raise SystemExit(main())
