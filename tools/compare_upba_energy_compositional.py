#!/usr/bin/env python3
"""Compare monolithic and compositional UPBA v2 advisory energy rankers."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from random import Random
from statistics import mean
from time import perf_counter
from typing import Any, Callable, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.upba_v2_energy_model import LinearEnergyModel, save_linear_model
from src.energy.upba_v2_set_features import SET_AWARE_FEATURE_NAMES
from tools.evaluate_upba_energy import evaluate_rows
from tools.generate_upba_energy_dataset import generate_dataset_rows
from tools.train_upba_energy import train_linear_ranker


LocalTargetFn = Callable[[dict[str, Any], Sequence[dict[str, Any]]], float]


AGGREGATE_VALIDITY_SUFFIXES = frozenset(
    {
        "candidate_balance_violation_count_norm",
        "candidate_limit_violation_count_norm",
        "candidate_negative_reserve_flag",
        "candidate_invariant_violation_flag",
        "candidate_noncanonical_fill_vector_flag",
        "candidate_price_objective_violation_flag",
        "candidate_output_mismatch_count_norm",
        "candidate_all_zero_fill_vector_flag",
        "candidate_schema_policy_mismatch_flag",
        "candidate_price_ratio_unreduced_flag",
        "candidate_fill_coverage_violation_flag",
        "candidate_duplicate_fill_id_flag",
        "candidate_unknown_fill_id_count_norm",
        "candidate_executed_input_over_amount_count_norm",
        "candidate_output_without_input_count_norm",
        "candidate_zero_net_input_count_norm",
    }
)

AGGREGATE_MARKET_SUFFIX_PREFIXES = (
    "pool_",
    "candidate_price_",
    "candidate_reserve",
    "candidate_k_",
    "candidate_net_",
    "candidate_total_fee_",
)

AGGREGATE_OBJECTIVE_SUFFIX_PREFIXES = (
    "candidate_positive_fill_",
    "candidate_zero_fill_",
    "candidate_partial_fill_",
    "candidate_executed_",
    "candidate_volume_",
    "candidate_surplus_",
    "candidate_dust_",
    "candidate_imbalance_",
    "candidate_normalized_",
)

SET_FEASIBILITY_SUFFIX_PREFIXES = (
    "set_balance_",
    "set_insufficient_",
    "set_overfill_",
    "set_output_",
    "set_surplus_",
    "set_expected_",
    "set_limit_",
    "set_balance_violation_",
    "set_output_mismatch_",
    "set_dust_",
    "set_zero_net_",
    "set_fee_",
)

SET_SHAPE_SUFFIX_PREFIXES = (
    "set_size_",
    "set_amount_",
    "set_min_out_",
    "set_base_to_quote_",
    "set_quote_to_base_",
    "set_direction_",
    "set_fill_",
    "set_positive_",
    "set_zero_fill_",
    "set_partial_",
)


@dataclass(frozen=True)
class ScoreCalibrator:
    group_names: tuple[str, ...]
    weights: tuple[float, ...]
    means: tuple[float, ...]
    scales: tuple[float, ...]

    def energy(
        self,
        row: dict[str, Any],
        scorers: dict[str, Callable[[dict[str, Any]], float]],
    ) -> float:
        total = 0.0
        for index, group_name in enumerate(self.group_names):
            raw = scorers[group_name](row)
            total += self.weights[index] * ((raw - self.means[index]) / self.scales[index])
        return total


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train-batches", type=int, default=200)
    parser.add_argument("--holdout-batches", type=int, default=100)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--train-seed", type=int, default=20260560)
    parser.add_argument("--holdout-seed", type=int, default=20260561)
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
    report = compare_compositional_rankers(
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


def compare_compositional_rankers(
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
    group_specs = _group_specs(SET_AWARE_FEATURE_NAMES)
    group_models: dict[str, LinearEnergyModel] = {}
    for group_name, indices in group_specs.items():
        projected_rows = _project_rows_to_indices(train_rows, indices)
        group_models[group_name] = train_linear_ranker(
            projected_rows,
            feature_block="set-aware",
            **train_args,
        )
    local_target_models = _train_local_target_models(
        train_rows=train_rows,
        group_specs=group_specs,
        epochs=epochs,
        learning_rate=learning_rate,
        margin=margin,
        seed=train_seed + 10_000,
        max_pair_weight=max_pair_weight,
    )
    local_target_scorers = {
        group_name: _set_aware_scorer(model)
        for group_name, model in local_target_models.items()
    }
    formula_component_scorers = _formula_component_scorers()
    formula_calibrator = _train_score_calibrator(
        rows=train_rows,
        scorers=formula_component_scorers,
        epochs=max(3, epochs),
        learning_rate=min(0.1, max(0.01, learning_rate)),
        margin=margin,
        seed=train_seed + 15_000,
        max_pair_weight=max_pair_weight,
    )
    local_target_calibrator = _train_score_calibrator(
        rows=train_rows,
        scorers=local_target_scorers,
        epochs=max(3, epochs),
        learning_rate=min(0.1, max(0.01, learning_rate)),
        margin=margin,
        seed=train_seed + 20_000,
        max_pair_weight=max_pair_weight,
    )

    model_paths: dict[str, str] = {}
    if output_model_dir is not None:
        output_model_dir.mkdir(parents=True, exist_ok=True)
        aggregate_path = output_model_dir / "upba_v2_energy_compositional_aggregate_baseline.json"
        set_aware_path = output_model_dir / "upba_v2_energy_compositional_set_aware_baseline.json"
        save_linear_model(aggregate, aggregate_path)
        save_linear_model(set_aware, set_aware_path)
        model_paths = {
            "aggregate": str(aggregate_path),
            "set_aware": str(set_aware_path),
        }
        for group_name, model in group_models.items():
            path = output_model_dir / f"upba_v2_energy_compositional_{group_name}.json"
            save_linear_model(model, path)
            model_paths[f"group::{group_name}"] = str(path)
        for group_name, model in local_target_models.items():
            path = output_model_dir / f"upba_v2_energy_local_target_{group_name}.json"
            save_linear_model(model, path)
            model_paths[f"local_target::{group_name}"] = str(path)

    compositional_scorer = _compositional_scorer(group_models)
    local_target_scorer = _compositional_scorer(local_target_models)
    formula_calibrated_scorer = lambda row: formula_calibrator.energy(
        row,
        formula_component_scorers,
    )
    calibrated_scorer = lambda row: local_target_calibrator.energy(
        row,
        local_target_scorers,
    )
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
            scorer=_set_aware_scorer(set_aware),
            mode="learned",
            seed=holdout_seed,
        ),
        "obligation_formula_sum": evaluate_rows(
            holdout_rows,
            scorer=_obligation_formula_scorer,
            mode="learned",
            seed=holdout_seed,
        ),
        "obligation_formula_calibrated": evaluate_rows(
            holdout_rows,
            scorer=formula_calibrated_scorer,
            mode="learned",
            seed=holdout_seed,
        ),
        "compositional_sum": evaluate_rows(
            holdout_rows,
            scorer=compositional_scorer,
            mode="learned",
            seed=holdout_seed,
        ),
        "compositional_hybrid": evaluate_rows(
            holdout_rows,
            scorer=compositional_scorer,
            mode="hybrid",
            seed=holdout_seed,
        ),
        "local_target_sum": evaluate_rows(
            holdout_rows,
            scorer=local_target_scorer,
            mode="learned",
            seed=holdout_seed,
        ),
        "local_target_calibrated": evaluate_rows(
            holdout_rows,
            scorer=calibrated_scorer,
            mode="learned",
            seed=holdout_seed,
        ),
        "local_target_hybrid": evaluate_rows(
            holdout_rows,
            scorer=local_target_scorer,
            mode="hybrid",
            seed=holdout_seed,
        ),
    }
    elapsed_ms = (perf_counter() - started) * 1000
    return {
        "schema": "zenodex/energy/upba_v2_compositional_comparison/v1",
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
            "epochs": epochs,
            "learning_rate": learning_rate,
            "margin": margin,
            "winner_pair_weight": winner_pair_weight,
            "objective_gap_weight": objective_gap_weight,
            "same_volume_surplus_gap_weight": same_volume_surplus_gap_weight,
            "max_pair_weight": max_pair_weight,
            "loss": "pairwise_hinge",
            "composition_rule": "sum_local_energy_models",
        },
        "models": {
            "aggregate_pairwise": {
                "feature_dim": len(aggregate.feature_names),
                "parameter_count": len(aggregate.weights) + 1,
            },
            "set_aware_pairwise": {
                "feature_dim": len(set_aware.feature_names),
                "parameter_count": len(set_aware.weights) + 1,
            },
            "compositional_sum": {
                "group_count": len(group_models),
                "stored_parameter_count": sum(len(model.weights) + 1 for model in group_models.values()),
                "active_parameter_count": sum(len(indices) + 1 for indices in group_specs.values()),
                "groups": {
                    name: {
                        "active_feature_count": len(indices),
                        "active_features_sha256": _feature_digest(
                            SET_AWARE_FEATURE_NAMES[index] for index in indices
                        ),
                    }
                    for name, indices in group_specs.items()
                },
            },
            "local_target_sum": {
                "group_count": len(local_target_models),
                "stored_parameter_count": sum(
                    len(model.weights) + 1 for model in local_target_models.values()
                ),
                "active_parameter_count": sum(len(indices) + 1 for indices in group_specs.values()),
                "calibrator_parameter_count": len(local_target_calibrator.weights),
                "calibrator_group_names": list(local_target_calibrator.group_names),
                "calibrator_weights": list(local_target_calibrator.weights),
            },
            "obligation_formula_calibrated": {
                "component_count": len(formula_calibrator.weights),
                "calibrator_group_names": list(formula_calibrator.group_names),
                "calibrator_weights": list(formula_calibrator.weights),
            },
        },
        "model_paths": model_paths,
        "modes": modes,
        "deltas": _mode_deltas(modes),
        "interpretation": _interpretation(modes),
        "wall_clock_ms": elapsed_ms,
    }


def _group_specs(feature_names: Sequence[str]) -> dict[str, tuple[int, ...]]:
    groups = {
        "aggregate_validity": tuple(
            index
            for index, name in enumerate(feature_names)
            if _block(name) == "aggregate" and _suffix(name) in AGGREGATE_VALIDITY_SUFFIXES
        ),
        "aggregate_market": tuple(
            index
            for index, name in enumerate(feature_names)
            if _block(name) == "aggregate"
            and _suffix(name).startswith(AGGREGATE_MARKET_SUFFIX_PREFIXES)
        ),
        "aggregate_objective": tuple(
            index
            for index, name in enumerate(feature_names)
            if _block(name) == "aggregate"
            and _suffix(name).startswith(AGGREGATE_OBJECTIVE_SUFFIX_PREFIXES)
        ),
        "set_feasibility": tuple(
            index
            for index, name in enumerate(feature_names)
            if _block(name) == "set" and _suffix(name).startswith(SET_FEASIBILITY_SUFFIX_PREFIXES)
        ),
        "set_fill_shape": tuple(
            index
            for index, name in enumerate(feature_names)
            if _block(name) == "set" and _suffix(name).startswith(SET_SHAPE_SUFFIX_PREFIXES)
        ),
    }
    empty = [name for name, indices in groups.items() if not indices]
    if empty:
        raise ValueError(f"empty compositional feature groups: {empty}")
    return groups


def _project_rows_to_indices(rows: Sequence[dict[str, Any]], indices: Sequence[int]) -> list[dict[str, Any]]:
    active = frozenset(indices)
    projected: list[dict[str, Any]] = []
    for row in rows:
        values = [float(value) for value in row["set_aware_features"]]
        cloned = dict(row)
        cloned["set_aware_features"] = [
            value if index in active else 0.0 for index, value in enumerate(values)
        ]
        projected.append(cloned)
    return projected


def _train_local_target_models(
    *,
    train_rows: Sequence[dict[str, Any]],
    group_specs: dict[str, tuple[int, ...]],
    epochs: int,
    learning_rate: float,
    margin: float,
    seed: int,
    max_pair_weight: float,
) -> dict[str, LinearEnergyModel]:
    target_specs = _local_target_specs()
    missing = sorted(set(group_specs) - set(target_specs))
    if missing:
        raise ValueError(f"missing local target specs: {missing}")
    return {
        group_name: _train_local_pairwise_model(
            rows=train_rows,
            active_indices=indices,
            target_fn=target_specs[group_name],
            epochs=epochs,
            learning_rate=learning_rate,
            margin=margin,
            seed=seed + index * 101,
            max_pair_weight=max_pair_weight,
        )
        for index, (group_name, indices) in enumerate(sorted(group_specs.items()))
    }


def _train_local_pairwise_model(
    *,
    rows: Sequence[dict[str, Any]],
    active_indices: Sequence[int],
    target_fn: LocalTargetFn,
    epochs: int,
    learning_rate: float,
    margin: float,
    seed: int,
    max_pair_weight: float,
) -> LinearEnergyModel:
    if not rows:
        raise ValueError("training rows are empty")
    active = tuple(active_indices)
    weights = [0.0 for _ in SET_AWARE_FEATURE_NAMES]
    by_batch = _rows_by_batch(rows)
    batches = list(by_batch.values())
    rng = Random(seed)
    for _epoch in range(epochs):
        rng.shuffle(batches)
        for batch_rows in batches:
            if len(batch_rows) < 2:
                continue
            targets = {id(row): float(target_fn(row, batch_rows)) for row in batch_rows}
            ranked = sorted(batch_rows, key=lambda row: targets[id(row)])
            scale = max(1.0, max(targets.values()) - min(targets.values()))
            for good_index, good in enumerate(ranked):
                good_target = targets[id(good)]
                good_x = _set_aware_values(good)
                for bad in ranked[good_index + 1 :]:
                    bad_target = targets[id(bad)]
                    if good_target >= bad_target:
                        continue
                    bad_x = _set_aware_values(bad)
                    energy_good = _active_dot(weights, good_x, active)
                    energy_bad = _active_dot(weights, bad_x, active)
                    if margin + energy_good - energy_bad <= 0:
                        continue
                    pair_weight = min(
                        max_pair_weight,
                        max(1.0, 1.0 + 4.0 * ((bad_target - good_target) / scale)),
                    )
                    for index in active:
                        weights[index] -= learning_rate * pair_weight * (
                            good_x[index] - bad_x[index]
                        )
    return LinearEnergyModel(
        feature_names=SET_AWARE_FEATURE_NAMES,
        weights=tuple(weights),
        bias=0.0,
    )


def _train_score_calibrator(
    *,
    rows: Sequence[dict[str, Any]],
    scorers: dict[str, Callable[[dict[str, Any]], float]],
    epochs: int,
    learning_rate: float,
    margin: float,
    seed: int,
    max_pair_weight: float,
) -> ScoreCalibrator:
    group_names = tuple(sorted(scorers))
    raw_by_group = {
        group_name: [float(scorers[group_name](row)) for row in rows]
        for group_name in group_names
    }
    means = tuple(mean(raw_by_group[group_name]) if raw_by_group[group_name] else 0.0 for group_name in group_names)
    scales = tuple(_std(raw_by_group[group_name]) or 1.0 for group_name in group_names)
    weights = [1.0 for _ in group_names]
    by_batch = _rows_by_batch(rows)
    batches = list(by_batch.values())
    rng = Random(seed)
    for _epoch in range(epochs):
        rng.shuffle(batches)
        for batch_rows in batches:
            ranked = sorted(batch_rows, key=_global_label_score, reverse=True)
            if len(ranked) < 2:
                continue
            batch_scale = _batch_objective_scale(batch_rows)
            for good_index, good in enumerate(ranked):
                good_score = _global_label_score(good)
                good_x = _calibrator_features(good, group_names, scorers, means, scales)
                for bad in ranked[good_index + 1 :]:
                    bad_score = _global_label_score(bad)
                    if good_score <= bad_score:
                        continue
                    bad_x = _calibrator_features(bad, group_names, scorers, means, scales)
                    energy_good = _dot(weights, good_x)
                    energy_bad = _dot(weights, bad_x)
                    if margin + energy_good - energy_bad <= 0:
                        continue
                    pair_weight = _global_pair_weight(
                        good=good,
                        bad=bad,
                        batch_scale=batch_scale,
                        max_pair_weight=max_pair_weight,
                    )
                    for index, (g_value, b_value) in enumerate(zip(good_x, bad_x, strict=True)):
                        weights[index] -= learning_rate * pair_weight * (g_value - b_value)
                        weights[index] = max(-10.0, min(10.0, weights[index]))
    return ScoreCalibrator(
        group_names=group_names,
        weights=tuple(weights),
        means=means,
        scales=scales,
    )


def _local_target_specs() -> dict[str, LocalTargetFn]:
    return {
        "aggregate_validity": _target_aggregate_validity,
        "aggregate_market": _target_aggregate_market,
        "aggregate_objective": _target_aggregate_objective,
        "set_feasibility": _target_set_feasibility,
        "set_fill_shape": _target_set_fill_shape,
    }


def _target_aggregate_validity(row: dict[str, Any], batch_rows: Sequence[dict[str, Any]]) -> float:
    del batch_rows
    invalid_label = 0.0 if bool(row["label"]["valid"]) else 2.0
    return invalid_label + _aggregate_validity_formula(row)


def _target_aggregate_market(row: dict[str, Any], batch_rows: Sequence[dict[str, Any]]) -> float:
    del batch_rows
    return (
        4.0 * _agg(row, "candidate_negative_reserve_flag")
        + 4.0 * _agg(row, "candidate_invariant_violation_flag")
        + 2.0 * _agg(row, "candidate_price_objective_violation_flag")
        + 1.0 * _agg(row, "candidate_price_ratio_unreduced_flag")
        + 0.5 * max(0.0, -_agg(row, "candidate_k_margin_signed"))
        + 0.1 * abs(_agg(row, "candidate_price_ratio_vs_spot") - 1.0)
    )


def _target_aggregate_objective(row: dict[str, Any], batch_rows: Sequence[dict[str, Any]]) -> float:
    valid_rows = [item for item in batch_rows if bool(item["label"]["valid"])]
    volume_scale = max([1, *(int(item["label"]["objective_volume"]) for item in valid_rows)])
    surplus_scale = max([1, *(abs(int(item["label"]["objective_surplus"])) for item in valid_rows)])
    if not bool(row["label"]["valid"]):
        return 2.0 + _aggregate_validity_formula(row)
    volume = int(row["label"]["objective_volume"]) / volume_scale
    surplus = int(row["label"]["objective_surplus"]) / surplus_scale
    return -(volume + 0.05 * surplus)


def _target_set_feasibility(row: dict[str, Any], batch_rows: Sequence[dict[str, Any]]) -> float:
    del batch_rows
    invalid_label = 0.0 if bool(row["label"]["valid"]) else 0.5
    return invalid_label + _set_feasibility_formula(row)


def _target_set_fill_shape(row: dict[str, Any], batch_rows: Sequence[dict[str, Any]]) -> float:
    del batch_rows
    return _set_fill_shape_formula(row)


def _compositional_scorer(models: dict[str, LinearEnergyModel]) -> Callable[[dict[str, Any]], float]:
    ordered_models = tuple(model for _, model in sorted(models.items()))

    def score(row: dict[str, Any]) -> float:
        features = [float(value) for value in row["set_aware_features"]]
        return sum(model.energy(features) for model in ordered_models)

    return score


def _obligation_formula_scorer(row: dict[str, Any]) -> float:
    return (
        20.0 * _aggregate_validity_formula(row)
        + 5.0 * _target_aggregate_market(row, ())
        + 4.0 * _set_feasibility_formula(row)
        + 1.0 * _set_fill_shape_formula(row)
        - 10.0 * _agg(row, "candidate_normalized_executed_volume")
        - 1.0 * _agg(row, "candidate_normalized_surplus")
    )


def _formula_component_scorers() -> dict[str, Callable[[dict[str, Any]], float]]:
    return {
        "aggregate_validity_formula": _aggregate_validity_formula,
        "aggregate_market_formula": lambda row: _target_aggregate_market(row, ()),
        "set_feasibility_formula": _set_feasibility_formula,
        "set_fill_shape_formula": _set_fill_shape_formula,
        "objective_formula": lambda row: (
            -_agg(row, "candidate_normalized_executed_volume")
            - 0.1 * _agg(row, "candidate_normalized_surplus")
        ),
    }


def _aggregate_validity_formula(row: dict[str, Any]) -> float:
    return (
        10.0
        * (
            _agg(row, "candidate_balance_violation_count_norm")
            + _agg(row, "candidate_limit_violation_count_norm")
            + _agg(row, "candidate_negative_reserve_flag")
            + _agg(row, "candidate_invariant_violation_flag")
        )
        + 2.0
        * (
            _agg(row, "candidate_noncanonical_fill_vector_flag")
            + _agg(row, "candidate_price_objective_violation_flag")
            + _agg(row, "candidate_output_mismatch_count_norm")
            + _agg(row, "candidate_all_zero_fill_vector_flag")
            + _agg(row, "candidate_schema_policy_mismatch_flag")
            + _agg(row, "candidate_price_ratio_unreduced_flag")
            + _agg(row, "candidate_fill_coverage_violation_flag")
            + _agg(row, "candidate_duplicate_fill_id_flag")
            + _agg(row, "candidate_unknown_fill_id_count_norm")
            + _agg(row, "candidate_executed_input_over_amount_count_norm")
            + _agg(row, "candidate_output_without_input_count_norm")
        )
        + _agg(row, "candidate_zero_net_input_count_norm")
    )


def _set_feasibility_formula(row: dict[str, Any]) -> float:
    return (
        8.0 * _set(row, "set_limit_violation_max")
        + 8.0 * _set(row, "set_balance_violation_max")
        + 8.0 * _set(row, "set_output_mismatch_max")
        + 4.0 * _set(row, "set_overfill_max")
        + 2.0 * _set(row, "set_insufficient_balance_max")
        + 1.0 * _set(row, "set_dust_fill_max")
        + 1.0 * _set(row, "set_zero_net_input_max")
        + max(0.0, 1.0 - _set(row, "set_expected_out_ratio_mean"))
        + 0.25 * max(0.0, 1.0 - _set(row, "set_output_to_min_required_ratio_mean"))
    )


def _set_fill_shape_formula(row: dict[str, Any]) -> float:
    return (
        0.5 * _set(row, "set_zero_fill_mean")
        + 0.25 * _set(row, "set_partial_fill_mean")
        + 0.25 * _set(row, "set_direction_fill_fraction_gap_abs")
        + 0.5 * _set(row, "set_dust_fill_mean")
        + 0.5 * _set(row, "set_zero_net_input_mean")
        - 0.75 * _set(row, "set_positive_fill_mean")
        - 0.25 * _set(row, "set_fill_fraction_mean")
    )


def _agg(row: dict[str, Any], suffix: str) -> float:
    return _set_aware_feature(row, f"aggregate::{suffix}")


def _set(row: dict[str, Any], suffix: str) -> float:
    return _set_aware_feature(row, f"set::{suffix}")


def _set_aware_feature(row: dict[str, Any], name: str) -> float:
    index = SET_AWARE_FEATURE_NAMES.index(name)
    return float(row["set_aware_features"][index])


def _set_aware_values(row: dict[str, Any]) -> list[float]:
    return [float(value) for value in row["set_aware_features"]]


def _rows_by_batch(rows: Sequence[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[str(row["batch_id"])].append(row)
    return dict(grouped)


def _active_dot(weights: Sequence[float], features: Sequence[float], active: Sequence[int]) -> float:
    return sum(float(weights[index]) * float(features[index]) for index in active)


def _dot(weights: Sequence[float], features: Sequence[float]) -> float:
    return sum(float(weight) * float(value) for weight, value in zip(weights, features, strict=True))


def _std(values: Sequence[float]) -> float:
    vals = [float(value) for value in values]
    if len(vals) <= 1:
        return 0.0
    mu = mean(vals)
    return (sum((value - mu) ** 2 for value in vals) / len(vals)) ** 0.5


def _global_label_score(row: dict[str, Any]) -> tuple[int, int, int]:
    label = row["label"]
    return (
        1 if bool(label["valid"]) else 0,
        int(label["objective_volume"]),
        int(label["objective_surplus"]),
    )


def _batch_objective_scale(rows: Sequence[dict[str, Any]]) -> dict[str, int]:
    valid_rows = [row for row in rows if bool(row["label"]["valid"])]
    if not valid_rows:
        return {"volume": 1, "surplus": 1}
    return {
        "volume": max(1, max(abs(int(row["label"]["objective_volume"])) for row in valid_rows)),
        "surplus": max(1, max(abs(int(row["label"]["objective_surplus"])) for row in valid_rows)),
    }


def _global_pair_weight(
    *,
    good: dict[str, Any],
    bad: dict[str, Any],
    batch_scale: dict[str, int],
    max_pair_weight: float,
) -> float:
    good_label = good["label"]
    bad_label = bad["label"]
    weight = 2.0 if bool(good_label.get("is_winner")) else 1.0
    if bool(good_label["valid"]) and bool(bad_label["valid"]):
        volume_gap = max(
            0,
            int(good_label["objective_volume"]) - int(bad_label["objective_volume"]),
        )
        surplus_gap = max(
            0,
            int(good_label["objective_surplus"]) - int(bad_label["objective_surplus"]),
        )
        weight += 4.0 * (volume_gap / max(1, batch_scale["volume"]))
        if volume_gap == 0:
            weight += surplus_gap / max(1, batch_scale["surplus"])
    return min(max_pair_weight, max(1.0, weight))


def _calibrator_features(
    row: dict[str, Any],
    group_names: Sequence[str],
    scorers: dict[str, Callable[[dict[str, Any]], float]],
    means: Sequence[float],
    scales: Sequence[float],
) -> list[float]:
    return [
        (float(scorers[group_name](row)) - float(means[index])) / float(scales[index])
        for index, group_name in enumerate(group_names)
    ]


def _aggregate_scorer(model: LinearEnergyModel) -> Callable[[dict[str, Any]], float]:
    return lambda row: model.energy([float(value) for value in row["features"]])


def _set_aware_scorer(model: LinearEnergyModel) -> Callable[[dict[str, Any]], float]:
    return lambda row: model.energy([float(value) for value in row["set_aware_features"]])


def _mode_deltas(modes: dict[str, dict[str, Any]]) -> dict[str, Any]:
    return {
        "compositional_vs_aggregate_pairwise": _delta(
            modes["compositional_sum"], modes["aggregate_pairwise"]
        ),
        "compositional_vs_set_aware_pairwise": _delta(
            modes["compositional_sum"], modes["set_aware_pairwise"]
        ),
        "compositional_hybrid_vs_compositional_sum": _delta(
            modes["compositional_hybrid"], modes["compositional_sum"]
        ),
        "obligation_formula_vs_aggregate_pairwise": _delta(
            modes["obligation_formula_sum"], modes["aggregate_pairwise"]
        ),
        "obligation_formula_calibrated_vs_aggregate_pairwise": _delta(
            modes["obligation_formula_calibrated"], modes["aggregate_pairwise"]
        ),
        "local_target_sum_vs_aggregate_pairwise": _delta(
            modes["local_target_sum"], modes["aggregate_pairwise"]
        ),
        "local_target_calibrated_vs_aggregate_pairwise": _delta(
            modes["local_target_calibrated"], modes["aggregate_pairwise"]
        ),
        "local_target_hybrid_vs_aggregate_pairwise": _delta(
            modes["local_target_hybrid"], modes["aggregate_pairwise"]
        ),
    }


def _delta(left: dict[str, Any], right: dict[str, Any]) -> dict[str, float]:
    return {
        "top_1_recall_delta": float(left["top_1_recall"]) - float(right["top_1_recall"]),
        "top_5_recall_delta": float(left["top_5_recall"]) - float(right["top_5_recall"]),
        "top_10_recall_delta": float(left["top_10_recall"]) - float(right["top_10_recall"]),
        "mean_verifier_calls_delta": float(left["mean_verifier_calls"])
        - float(right["mean_verifier_calls"]),
        "p99_verifier_calls_delta": float(left["p99_verifier_calls"])
        - float(right["p99_verifier_calls"]),
    }


def _interpretation(modes: dict[str, dict[str, Any]]) -> dict[str, Any]:
    baseline_candidates = {
        "aggregate_pairwise": modes["aggregate_pairwise"],
        "set_aware_pairwise": modes["set_aware_pairwise"],
    }
    best_baseline_name, best_baseline = min(
        baseline_candidates.items(),
        key=lambda item: (
            float(item[1]["mean_verifier_calls"]),
            -float(item[1]["top_1_recall"]),
        ),
    )
    compositional_candidates = {
        "obligation_formula_sum": modes["obligation_formula_sum"],
        "obligation_formula_calibrated": modes["obligation_formula_calibrated"],
        "compositional_sum": modes["compositional_sum"],
        "compositional_hybrid": modes["compositional_hybrid"],
        "local_target_sum": modes["local_target_sum"],
        "local_target_calibrated": modes["local_target_calibrated"],
        "local_target_hybrid": modes["local_target_hybrid"],
    }
    best_compositional_name, best_compositional = min(
        compositional_candidates.items(),
        key=lambda item: (
            float(item[1]["mean_verifier_calls"]),
            -float(item[1]["top_1_recall"]),
        ),
    )
    invalid_accept_count_total = sum(int(stats["invalid_accept_count"]) for stats in modes.values())
    helped = (
        invalid_accept_count_total == 0
        and float(best_compositional["mean_verifier_calls"])
        < float(best_baseline["mean_verifier_calls"])
        and float(best_compositional["top_10_recall"]) >= float(best_baseline["top_10_recall"])
    )
    if helped:
        recommendation = (
            "Keep the best compositional local-energy variant for cross-seed "
            "stress and larger hard-negative sweeps."
        )
        negative_knowledge = ""
    else:
        recommendation = (
            "Do not promote these compositional local-energy variants on this "
            "run; keep the best monolithic pairwise baseline as the measured "
            "checkpoint."
        )
        negative_knowledge = (
            "The tested local-energy decompositions did not reduce mean verifier "
            "calls against the strongest monolithic pairwise baseline on this "
            "bounded synthetic split."
        )
    return {
        "best_pairwise_baseline": best_baseline_name,
        "best_compositional_mode": best_compositional_name,
        "best_pairwise_mean_verifier_calls": best_baseline["mean_verifier_calls"],
        "best_compositional_mean_verifier_calls": best_compositional["mean_verifier_calls"],
        "compositional_helped": helped,
        "all_modes_invalid_accept_count": invalid_accept_count_total,
        "recommendation": recommendation,
        "negative_knowledge": negative_knowledge,
    }


def _candidate_count_mean(rows: Sequence[dict[str, Any]]) -> float:
    counts: dict[str, int] = {}
    for row in rows:
        batch_id = str(row["batch_id"])
        counts[batch_id] = counts.get(batch_id, 0) + 1
    return mean(counts.values()) if counts else 0.0


def _stable_digest(rows: Sequence[dict[str, Any]]) -> str:
    digest = sha256()
    for row in rows:
        encoded = json.dumps(row, sort_keys=True, separators=(",", ":"))
        digest.update(encoded.encode("utf-8"))
        digest.update(b"\n")
    return "0x" + digest.hexdigest()


def _feature_digest(names: Sequence[str]) -> str:
    digest = sha256()
    for name in names:
        digest.update(str(name).encode("utf-8"))
        digest.update(b"\n")
    return "0x" + digest.hexdigest()


def _block(name: str) -> str:
    return name.split("::", 1)[0]


def _suffix(name: str) -> str:
    return name.split("::", 1)[1] if "::" in name else name


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Compositional Energy Probe",
        "",
        "```text",
        f"train_batches: {report['train']['batches']}",
        f"train_rows: {report['train']['rows']}",
        f"train_seed: {report['train']['seed']}",
        f"holdout_batches: {report['holdout']['batches']}",
        f"holdout_rows: {report['holdout']['rows']}",
        f"holdout_seed: {report['holdout']['seed']}",
        f"candidates_per_batch: {report['candidates_per_batch']}",
        "composition_rule: sum_local_energy_models",
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
            "## Interpretation",
            "",
            f"best_pairwise_baseline: `{report['interpretation']['best_pairwise_baseline']}`",
            f"best_compositional_mode: `{report['interpretation']['best_compositional_mode']}`",
            f"compositional_helped: {report['interpretation']['compositional_helped']}",
            f"invalid_accept_count_total: {report['interpretation']['all_modes_invalid_accept_count']}",
            "",
            report["interpretation"]["recommendation"],
        ]
    )
    negative = str(report["interpretation"].get("negative_knowledge", ""))
    if negative:
        lines.extend(["", negative])
    lines.extend(
        [
            "",
            "This is bounded synthetic evidence for advisory search ordering only. "
            "The deterministic verifier remains authoritative.",
        ]
    )
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    return f"{float(value):.4f}"


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
