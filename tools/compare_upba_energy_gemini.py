#!/usr/bin/env python3
"""Compare the current UPBA v2 gap-weighted checkpoint against the Gemini checkpoint."""

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

from src.energy.upba_v2_cross_features import GEMINI_FEATURE_NAMES, feature_values_for_energy_model
from src.energy.upba_v2_energy_model import LinearEnergyModel, initial_hand_weight_model
from src.energy.upba_v2_mlp_energy import load_advisory_energy_model
from src.energy.upba_v2_set_features import SET_AWARE_FEATURE_NAMES
from tools.evaluate_upba_energy import evaluate_rows
from tools.train_upba_energy import _label_score, load_rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dataset",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_holdout_seed20260518.jsonl"),
    )
    parser.add_argument(
        "--gap-model",
        type=Path,
        default=Path("data/upba_energy/best_models/upba_v2_linear_gap_weighted_seed20260517.json"),
    )
    parser.add_argument(
        "--gemini-model",
        type=Path,
        default=Path("internal/Gemini/gemini_linear_model_10k.json"),
    )
    parser.add_argument("--seed", type=int, default=20260518)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = compare_gemini_models(
        dataset=args.dataset,
        gap_model_path=args.gap_model,
        gemini_model_path=args.gemini_model,
        seed=args.seed,
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


def compare_gemini_models(
    *,
    dataset: Path,
    gap_model_path: Path,
    gemini_model_path: Path,
    seed: int,
) -> dict[str, Any]:
    rows = load_rows(dataset)
    hand = initial_hand_weight_model()
    gap = _load_advisory_model(gap_model_path)
    gemini = _load_advisory_model(gemini_model_path)
    modes = {
        "hand": evaluate_rows(
            rows,
            scorer=lambda row: float(row["label"]["hand_energy"]),
            mode="hand",
            seed=seed,
        ),
        "gap_weighted": _evaluate_model_rows(rows, model=gap, seed=seed, mode="learned"),
        "gemini": _evaluate_model_rows(rows, model=gemini, seed=seed, mode="learned"),
    }
    pairwise = {
        "hand": _pairwise_accuracy(rows, model=hand),
        "gap_weighted": _pairwise_accuracy(rows, model=gap),
        "gemini": _pairwise_accuracy(rows, model=gemini),
    }
    return {
        "schema": "zenodex/energy/upba_v2_gemini_comparison/v1",
        "dataset": {
            "path": str(dataset),
            "rows": len(rows),
            "batches": _batch_count(rows),
            "sha256": _sha256_file(dataset),
        },
        "models": {
            "hand": _model_summary(hand, source_path=None),
            "gap_weighted": _model_summary(gap, source_path=gap_model_path),
            "gemini": _model_summary(gemini, source_path=gemini_model_path),
        },
        "modes": modes,
        "pairwise_accuracy": pairwise,
        "deltas": {
            "gap_weighted_vs_hand": _delta(modes["gap_weighted"], modes["hand"]),
            "gemini_vs_hand": _delta(modes["gemini"], modes["hand"]),
            "gemini_vs_gap_weighted": _delta(modes["gemini"], modes["gap_weighted"]),
            "pairwise_gemini_vs_gap_weighted": {
                "accuracy_delta": float(pairwise["gemini"]["accuracy"])
                - float(pairwise["gap_weighted"]["accuracy"]),
            },
        },
        "interpretation": _interpretation(modes=modes, pairwise=pairwise),
    }


def _evaluate_model_rows(
    rows: list[dict[str, Any]],
    *,
    model: LinearEnergyModel,
    seed: int,
    mode: str,
) -> dict[str, Any]:
    return evaluate_rows(
        rows,
        scorer=_row_scorer(model),
        mode=mode,
        seed=seed,
    )


def _row_scorer(model: LinearEnergyModel) -> Callable[[dict[str, Any]], float]:
    def score(row: dict[str, Any]) -> float:
        return model.energy(_model_features_for_row(model, row))

    return score


def _model_features_for_row(model: LinearEnergyModel, row: dict[str, Any]) -> list[float]:
    feature_names = tuple(model.feature_names)
    if feature_names == SET_AWARE_FEATURE_NAMES:
        return [float(value) for value in row["set_aware_features"]]
    return list(feature_values_for_energy_model(model, row["features"]))


def _pairwise_accuracy(
    rows: list[dict[str, Any]],
    *,
    model: LinearEnergyModel,
) -> dict[str, Any]:
    by_batch: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        by_batch[str(row["batch_id"])].append(row)

    total_pairs = 0
    correct_pairs = 0
    for batch_rows in by_batch.values():
        if len(batch_rows) < 2:
            continue
        ranked = sorted(batch_rows, key=_label_score, reverse=True)
        for good_index, good in enumerate(ranked):
            good_score = _label_score(good)
            good_energy = model.energy(_model_features_for_row(model, good))
            for bad in ranked[good_index + 1 :]:
                bad_score = _label_score(bad)
                if good_score <= bad_score:
                    continue
                bad_energy = model.energy(_model_features_for_row(model, bad))
                total_pairs += 1
                if good_energy < bad_energy:
                    correct_pairs += 1
    return {
        "accuracy": 0.0 if total_pairs == 0 else correct_pairs / total_pairs,
        "pairs": total_pairs,
    }


def _model_summary(model: LinearEnergyModel, *, source_path: Path | None) -> dict[str, Any]:
    return {
        "source_path": None if source_path is None else str(source_path),
        "schema": _model_schema(model),
        "feature_dim": len(model.feature_names),
        "parameter_count": _model_parameter_count(model),
        "uses_gemini_crosses": tuple(model.feature_names) == GEMINI_FEATURE_NAMES,
        "uses_set_aware_features": tuple(model.feature_names) == SET_AWARE_FEATURE_NAMES,
    }


def _load_advisory_model(path: Path) -> object:
    return load_advisory_energy_model(path)


def _model_schema(model: object) -> str:
    if hasattr(model, "w1"):
        return "zenodex/energy/gemini_mlp/v1"
    return "zenodex/energy/linear_ranker/v1"


def _model_parameter_count(model: object) -> int:
    if hasattr(model, "w1") and hasattr(model, "b1") and hasattr(model, "w2"):
        w1 = getattr(model, "w1")
        b1 = getattr(model, "b1")
        w2 = getattr(model, "w2")
        return sum(len(row) for row in w1) + len(b1) + len(w2) + 1
    return len(getattr(model, "weights")) + 1


def _delta(left: dict[str, Any], right: dict[str, Any]) -> dict[str, float]:
    return {
        "top_1_recall_delta": float(left["top_1_recall"]) - float(right["top_1_recall"]),
        "top_5_recall_delta": float(left["top_5_recall"]) - float(right["top_5_recall"]),
        "top_10_recall_delta": float(left["top_10_recall"]) - float(right["top_10_recall"]),
        "mean_verifier_calls_delta": float(left["mean_verifier_calls"]) - float(right["mean_verifier_calls"]),
        "mean_verifier_calls_to_objective_winner_delta": float(left["mean_verifier_calls_to_objective_winner"])
        - float(right["mean_verifier_calls_to_objective_winner"]),
    }


def _interpretation(
    *,
    modes: dict[str, dict[str, Any]],
    pairwise: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    gemini = modes["gemini"]
    gap = modes["gap_weighted"]
    preferred = "gap_weighted"
    if (
        float(gemini["mean_verifier_calls"]),
        -float(gemini["top_1_recall"]),
    ) < (
        float(gap["mean_verifier_calls"]),
        -float(gap["top_1_recall"]),
    ):
        preferred = "gemini"
    return {
        "preferred_measured_checkpoint": preferred,
        "gemini_beats_gap_weighted_on_mean_calls": float(gemini["mean_verifier_calls"])
        < float(gap["mean_verifier_calls"]),
        "gemini_matches_gap_weighted_top_10_recall": float(gemini["top_10_recall"])
        == float(gap["top_10_recall"]),
        "gemini_beats_gap_weighted_on_top_1_recall": float(gemini["top_1_recall"])
        > float(gap["top_1_recall"]),
        "gemini_beats_gap_weighted_on_pairwise_accuracy": float(pairwise["gemini"]["accuracy"])
        > float(pairwise["gap_weighted"]["accuracy"]),
        "negative_knowledge": (
            "This report compares replayable synthetic holdout performance only. "
            "It does not promote Gemini into the retained-best registry or the production gate."
        ),
    }


def _batch_count(rows: list[dict[str, Any]]) -> int:
    return len({str(row["batch_id"]) for row in rows if row["label"]["is_winner"]})


def _sha256_file(path: Path) -> str:
    digest = sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# UPBA v2 Gemini Comparison",
        "",
        f"- Dataset: `{report['dataset']['path']}`",
        f"- Rows: `{report['dataset']['rows']}`",
        f"- Winner-bearing batches: `{report['dataset']['batches']}`",
        f"- Dataset sha256: `{report['dataset']['sha256']}`",
        "",
        "| Mode | Top-1 recall | Top-10 recall | Mean verifier calls | Pairwise accuracy |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for mode in ("hand", "gap_weighted", "gemini"):
        stats = report["modes"][mode]
        pairwise = report["pairwise_accuracy"][mode]
        lines.append(
            f"| `{mode}` | `{stats['top_1_recall']:.6f}` | `{stats['top_10_recall']:.6f}` | "
            f"`{stats['mean_verifier_calls']:.6f}` | `{pairwise['accuracy']:.6f}` |"
        )
    lines.extend(
        [
            "",
            f"- Preferred measured checkpoint on this dataset: `{report['interpretation']['preferred_measured_checkpoint']}`",
            f"- Gemini beats gap-weighted on mean calls: `{report['interpretation']['gemini_beats_gap_weighted_on_mean_calls']}`",
            f"- Gemini beats gap-weighted on top-1 recall: `{report['interpretation']['gemini_beats_gap_weighted_on_top_1_recall']}`",
            f"- Gemini beats gap-weighted on pairwise accuracy: `{report['interpretation']['gemini_beats_gap_weighted_on_pairwise_accuracy']}`",
        ]
    )
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    raise SystemExit(main())
