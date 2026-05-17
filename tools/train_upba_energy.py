#!/usr/bin/env python3
"""Train a tiny no-dependency UPBA v2 linear energy ranker."""

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

from src.energy.upba_v2_energy_model import (
    LinearEnergyModel,
    initial_hand_weight_model,
    save_linear_model,
)
from src.energy.upba_v2_features import FEATURE_NAMES
from src.energy.upba_v2_set_features import SET_AWARE_FEATURE_NAMES


def load_rows(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                rows.append(json.loads(line))
    return rows


def train_linear_ranker(
    rows: list[dict[str, Any]],
    *,
    epochs: int,
    learning_rate: float,
    margin: float,
    seed: int,
    init: str,
    feature_block: str = "aggregate",
    winner_pair_weight: float = 1.0,
    objective_gap_weight: float = 0.0,
    same_volume_surplus_gap_weight: float = 0.0,
    max_pair_weight: float = 8.0,
) -> LinearEnergyModel:
    if not rows:
        raise ValueError("training dataset is empty")
    feature_names = _feature_names_for_rows(rows, feature_block=feature_block)
    if init == "hand":
        if feature_block != "aggregate":
            raise ValueError("hand initialization is only defined for aggregate features")
        model = initial_hand_weight_model()
        weights = list(model.weights)
    elif init == "zero":
        weights = [0.0 for _ in feature_names]
    else:
        raise ValueError("init must be 'hand' or 'zero'")

    by_batch: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_batch[str(row["batch_id"])].append(row)

    rng = Random(seed)
    batches = list(by_batch.values())
    for _epoch in range(epochs):
        rng.shuffle(batches)
        for batch_rows in batches:
            if len(batch_rows) < 2:
                continue
            batch_scale = _batch_objective_scale(batch_rows)
            ranked = sorted(batch_rows, key=_label_score, reverse=True)
            for good_index, good in enumerate(ranked):
                good_x = _feature_values(good, feature_block=feature_block)
                for bad in ranked[good_index + 1 :]:
                    if _label_score(good) <= _label_score(bad):
                        continue
                    bad_x = _feature_values(bad, feature_block=feature_block)
                    energy_good = _dot(weights, good_x)
                    energy_bad = _dot(weights, bad_x)
                    if margin + energy_good - energy_bad <= 0:
                        continue
                    pair_weight = _pair_update_weight(
                        good=good,
                        bad=bad,
                        batch_scale=batch_scale,
                        winner_pair_weight=winner_pair_weight,
                        objective_gap_weight=objective_gap_weight,
                        same_volume_surplus_gap_weight=same_volume_surplus_gap_weight,
                        max_pair_weight=max_pair_weight,
                    )
                    for index, (g_value, b_value) in enumerate(zip(good_x, bad_x, strict=True)):
                        weights[index] -= learning_rate * pair_weight * (g_value - b_value)
    return LinearEnergyModel(feature_names=feature_names, weights=tuple(weights), bias=0.0)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dataset", type=Path, required=True)
    parser.add_argument("--output-model", type=Path, required=True)
    parser.add_argument("--epochs", type=int, default=8)
    parser.add_argument("--learning-rate", type=float, default=0.05)
    parser.add_argument("--margin", type=float, default=1.0)
    parser.add_argument("--seed", type=int, default=20260517)
    parser.add_argument("--init", choices=("zero", "hand"), default="zero")
    parser.add_argument("--feature-block", choices=("aggregate", "set-aware"), default="aggregate")
    parser.add_argument("--winner-pair-weight", type=float, default=1.0)
    parser.add_argument("--objective-gap-weight", type=float, default=0.0)
    parser.add_argument("--same-volume-surplus-gap-weight", type=float, default=0.0)
    parser.add_argument("--max-pair-weight", type=float, default=8.0)
    args = parser.parse_args()

    if args.winner_pair_weight <= 0:
        raise SystemExit("--winner-pair-weight must be positive")
    if args.objective_gap_weight < 0:
        raise SystemExit("--objective-gap-weight must be nonnegative")
    if args.same_volume_surplus_gap_weight < 0:
        raise SystemExit("--same-volume-surplus-gap-weight must be nonnegative")
    if args.max_pair_weight < 1:
        raise SystemExit("--max-pair-weight must be at least one")

    rows = load_rows(args.dataset)
    model = train_linear_ranker(
        rows,
        epochs=args.epochs,
        learning_rate=args.learning_rate,
        margin=args.margin,
        seed=args.seed,
        init=args.init,
        feature_block=args.feature_block,
        winner_pair_weight=args.winner_pair_weight,
        objective_gap_weight=args.objective_gap_weight,
        same_volume_surplus_gap_weight=args.same_volume_surplus_gap_weight,
        max_pair_weight=args.max_pair_weight,
    )
    args.output_model.parent.mkdir(parents=True, exist_ok=True)
    save_linear_model(model, args.output_model)
    summary = {
        "schema": "zenodex/energy/upba_v2_training_receipt/v1",
        "backend": "linear_pairwise_hinge",
        "rows": len(rows),
        "feature_dim": len(model.feature_names),
        "feature_block": args.feature_block,
        "parameters": len(model.weights) + 1,
        "epochs": args.epochs,
        "learning_rate": args.learning_rate,
        "margin": args.margin,
        "winner_pair_weight": args.winner_pair_weight,
        "objective_gap_weight": args.objective_gap_weight,
        "same_volume_surplus_gap_weight": args.same_volume_surplus_gap_weight,
        "max_pair_weight": args.max_pair_weight,
        "model_path": str(args.output_model),
    }
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


def _label_score(row: dict[str, Any]) -> tuple[int, int, int]:
    label = row["label"]
    return (
        1 if label["valid"] else 0,
        int(label["objective_volume"]),
        int(label["objective_surplus"]),
    )


def _feature_names_for_rows(rows: list[dict[str, Any]], *, feature_block: str) -> tuple[str, ...]:
    if feature_block == "aggregate":
        feature_names = tuple(rows[0]["feature_names"])
        if feature_names != FEATURE_NAMES:
            raise ValueError("dataset aggregate feature schema does not match current UPBA energy feature schema")
        return feature_names
    if feature_block == "set-aware":
        feature_names = tuple(rows[0].get("set_aware_feature_names", ()))
        if feature_names != SET_AWARE_FEATURE_NAMES:
            raise ValueError("dataset set-aware feature schema does not match current UPBA energy feature schema")
        return feature_names
    raise ValueError("feature_block must be 'aggregate' or 'set-aware'")


def _feature_values(row: dict[str, Any], *, feature_block: str) -> list[float]:
    if feature_block == "aggregate":
        return [float(value) for value in row["features"]]
    if feature_block == "set-aware":
        return [float(value) for value in row["set_aware_features"]]
    raise ValueError("feature_block must be 'aggregate' or 'set-aware'")


def _batch_objective_scale(rows: list[dict[str, Any]]) -> dict[str, int]:
    valid_rows = [row for row in rows if row["label"]["valid"]]
    if not valid_rows:
        return {"volume": 1, "surplus": 1}
    return {
        "volume": max(1, max(abs(int(row["label"]["objective_volume"])) for row in valid_rows)),
        "surplus": max(1, max(abs(int(row["label"]["objective_surplus"])) for row in valid_rows)),
    }


def _pair_update_weight(
    *,
    good: dict[str, Any],
    bad: dict[str, Any],
    batch_scale: dict[str, int],
    winner_pair_weight: float,
    objective_gap_weight: float,
    same_volume_surplus_gap_weight: float,
    max_pair_weight: float,
) -> float:
    good_label = good["label"]
    bad_label = bad["label"]
    weight = winner_pair_weight if good_label.get("is_winner") else 1.0
    if good_label["valid"] and bad_label["valid"]:
        volume_gap = max(
            0,
            int(good_label["objective_volume"]) - int(bad_label["objective_volume"]),
        )
        surplus_gap = max(
            0,
            int(good_label["objective_surplus"]) - int(bad_label["objective_surplus"]),
        )
        weight += objective_gap_weight * (volume_gap / max(1, batch_scale["volume"]))
        if volume_gap == 0:
            weight += same_volume_surplus_gap_weight * (
                surplus_gap / max(1, batch_scale["surplus"])
            )
    return min(max_pair_weight, max(1.0, weight))


def _dot(weights: list[float], features: list[float]) -> float:
    return sum(weight * value for weight, value in zip(weights, features, strict=True))


if __name__ == "__main__":
    raise SystemExit(main())
