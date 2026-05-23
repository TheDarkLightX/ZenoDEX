"""Listwise set-context ranker helpers for advisory UPBA v2 search.

The functions in this module operate on synthetic dataset rows. They build a
deterministic feature vector from each candidate's set-aware features plus
per-candidate-list rank and interaction features. The resulting model is still
an advisory energy scorer: lower energy means "verify earlier", and settlement
validity remains verifier-determined.
"""

from __future__ import annotations

from collections import defaultdict
from math import exp, sqrt
from random import Random
from typing import Any, Iterable, Sequence

from src.energy.upba_v2_energy_model import LinearEnergyModel
from src.energy.upba_v2_set_features import SET_AWARE_FEATURE_NAMES

LISTWISE_INTERACTION_SOURCE_NAMES: tuple[str, ...] = (
    "aggregate::candidate_balance_violation_count_norm",
    "aggregate::candidate_limit_violation_count_norm",
    "aggregate::candidate_negative_reserve_flag",
    "aggregate::candidate_invariant_violation_flag",
    "aggregate::candidate_noncanonical_fill_vector_flag",
    "aggregate::candidate_output_mismatch_count_norm",
    "aggregate::candidate_price_objective_violation_flag",
    "aggregate::candidate_zero_net_input_count_norm",
    "aggregate::candidate_dust_penalty_norm",
    "aggregate::candidate_imbalance_penalty",
    "aggregate::candidate_normalized_executed_volume",
    "aggregate::candidate_normalized_surplus",
    "aggregate::candidate_volume_log1p",
    "aggregate::candidate_surplus_signed",
    "set::set_fill_fraction_mean",
    "set::set_surplus_ratio_mean",
    "set::set_expected_out_ratio_mean",
    "set::set_output_mismatch_mean",
)

LISTWISE_EXTRA_SUFFIXES: tuple[str, ...] = (
    "rank_high",
    "rank_low",
    "x_batch_mean",
    "x_batch_std",
    "x_batch_range",
)

LISTWISE_SET_FEATURE_NAMES: tuple[str, ...] = SET_AWARE_FEATURE_NAMES + tuple(
    f"list::{suffix}::{name}"
    for name in LISTWISE_INTERACTION_SOURCE_NAMES
    for suffix in LISTWISE_EXTRA_SUFFIXES
)
LISTWISE_SET_FEATURE_DIM = len(LISTWISE_SET_FEATURE_NAMES)


def listwise_feature_rows(
    batch_rows: Sequence[dict[str, Any]],
) -> list[tuple[dict[str, Any], tuple[float, ...]]]:
    """Return listwise feature rows for one candidate batch."""

    if not batch_rows:
        return []
    _require_set_aware_schema(batch_rows)
    name_to_index = {name: index for index, name in enumerate(SET_AWARE_FEATURE_NAMES)}
    missing = [name for name in LISTWISE_INTERACTION_SOURCE_NAMES if name not in name_to_index]
    if missing:
        raise ValueError(f"missing listwise source feature(s): {', '.join(missing)}")

    base_rows = [
        tuple(float(value) for value in row["set_aware_features"])
        for row in batch_rows
    ]
    source_stats = {
        name: _column_stats([base[name_to_index[name]] for base in base_rows])
        for name in LISTWISE_INTERACTION_SOURCE_NAMES
    }
    output: list[tuple[dict[str, Any], tuple[float, ...]]] = []
    for row, base in zip(batch_rows, base_rows, strict=True):
        extras: list[float] = []
        for name in LISTWISE_INTERACTION_SOURCE_NAMES:
            value = base[name_to_index[name]]
            stats = source_stats[name]
            extras.extend(
                (
                    _rank_high(value, stats["values"]),
                    _rank_low(value, stats["values"]),
                    value * stats["mean"],
                    value * stats["std"],
                    value * stats["range"],
                )
            )
        output.append((row, base + tuple(extras)))
    return output


def train_listwise_set_ranker(
    rows: Sequence[dict[str, Any]],
    *,
    epochs: int,
    learning_rate: float,
    seed: int,
    init_model: LinearEnergyModel | None = None,
    l2: float = 0.0,
) -> LinearEnergyModel:
    """Train a linear energy model with top-one listwise softmax loss."""

    if not rows:
        raise ValueError("training dataset is empty")
    if epochs <= 0:
        raise ValueError("epochs must be positive")
    if learning_rate <= 0:
        raise ValueError("learning_rate must be positive")
    if l2 < 0:
        raise ValueError("l2 must be nonnegative")

    weights = _initial_score_weights(init_model)
    by_batch = rows_by_batch(rows)
    rng = Random(seed)
    batches = list(by_batch.values())
    for _epoch in range(epochs):
        rng.shuffle(batches)
        for batch_rows in batches:
            winner_hashes = {
                str(row["candidate_hash"])
                for row in batch_rows
                if bool(row["label"]["is_winner"])
            }
            if not winner_hashes:
                continue
            featured = listwise_feature_rows(batch_rows)
            logits = [_dot(weights, features) for _row, features in featured]
            probs = _softmax(logits)
            gradient = [0.0 for _ in weights]
            for probability, (row, features) in zip(probs, featured, strict=True):
                target = 1.0 if str(row["candidate_hash"]) in winner_hashes else 0.0
                coefficient = probability - target
                for index, value in enumerate(features):
                    gradient[index] += coefficient * value
            scale = max(1, len(featured))
            for index, grad in enumerate(gradient):
                regularizer = l2 * weights[index]
                weights[index] -= learning_rate * ((grad / scale) + regularizer)

    energy_weights = tuple(-weight for weight in weights)
    return LinearEnergyModel(
        feature_names=LISTWISE_SET_FEATURE_NAMES,
        weights=energy_weights,
        bias=0.0,
    )


def rows_by_batch(rows: Iterable[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    by_batch: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_batch[str(row["batch_id"])].append(row)
    return by_batch


def score_listwise_batch(
    batch_rows: Sequence[dict[str, Any]],
    model: LinearEnergyModel,
) -> list[tuple[float, dict[str, Any]]]:
    """Score one batch with a listwise feature model."""

    if model.feature_names != LISTWISE_SET_FEATURE_NAMES:
        raise ValueError("model feature schema does not match listwise set schema")
    return [
        (float(model.energy(features)), row)
        for row, features in listwise_feature_rows(batch_rows)
    ]


def order_rows_by_listwise_set_model(
    batch_rows: Sequence[dict[str, Any]],
    model: LinearEnergyModel,
) -> list[dict[str, Any]]:
    """Return a deterministic lower-energy-first candidate order."""

    scored = score_listwise_batch(batch_rows, model)
    scored.sort(key=lambda item: (item[0], str(item[1]["candidate_hash"])))
    return [row for _energy, row in scored]


def _initial_score_weights(init_model: LinearEnergyModel | None) -> list[float]:
    weights_by_name: dict[str, float] = {}
    if init_model is not None:
        weights_by_name = dict(zip(init_model.feature_names, init_model.weights, strict=True))
    weights: list[float] = []
    for name in LISTWISE_SET_FEATURE_NAMES:
        energy_weight = weights_by_name.get(name, 0.0)
        weights.append(-float(energy_weight))
    return weights


def _require_set_aware_schema(rows: Sequence[dict[str, Any]]) -> None:
    for row in rows:
        names = tuple(row.get("set_aware_feature_names", ()))
        if names != SET_AWARE_FEATURE_NAMES:
            raise ValueError("dataset set-aware feature schema does not match current UPBA energy schema")
        if len(row.get("set_aware_features", ())) != len(SET_AWARE_FEATURE_NAMES):
            raise ValueError("dataset set-aware feature length does not match schema")


def _column_stats(values: Sequence[float]) -> dict[str, Any]:
    vals = [float(value) for value in values] or [0.0]
    avg = sum(vals) / len(vals)
    variance = sum((value - avg) ** 2 for value in vals) / len(vals)
    return {
        "values": vals,
        "mean": avg,
        "std": sqrt(variance),
        "range": max(vals) - min(vals),
    }


def _rank_high(value: float, values: Sequence[float]) -> float:
    if len(values) <= 1:
        return 1.0
    count = sum(1 for item in values if item <= value)
    return (count - 1) / (len(values) - 1)


def _rank_low(value: float, values: Sequence[float]) -> float:
    if len(values) <= 1:
        return 1.0
    count = sum(1 for item in values if item >= value)
    return (count - 1) / (len(values) - 1)


def _softmax(values: Sequence[float]) -> list[float]:
    if not values:
        return []
    offset = max(values)
    exps = [exp(max(-80.0, min(80.0, value - offset))) for value in values]
    total = sum(exps)
    return [value / total for value in exps]


def _dot(weights: Sequence[float], features: Sequence[float]) -> float:
    return sum(weight * value for weight, value in zip(weights, features, strict=True))
