#!/usr/bin/env python3
"""Inspect a trained UPBA v2 linear energy model."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.upba_v2_energy_model import initial_hand_weight_model, load_linear_model
from src.energy.upba_v2_features import FEATURE_NAMES
from src.energy.upba_v2_set_features import SET_AWARE_FEATURE_NAMES

FORBIDDEN_FEATURE_SUBSTRINGS = (
    "verifier",
    "is_winner",
    "target_energy",
    "valid_objective",
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--top-n", type=int, default=16)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    if args.top_n <= 0:
        raise SystemExit("--top-n must be positive")
    if not args.model.exists():
        raise SystemExit(f"model does not exist: {args.model}")

    report = inspect_model(args.model, top_n=args.top_n)
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0


def inspect_model(model_path: Path, *, top_n: int) -> dict[str, Any]:
    model = load_linear_model(model_path)
    hand = initial_hand_weight_model()
    if model.feature_names == FEATURE_NAMES:
        feature_block = "aggregate"
    elif model.feature_names == SET_AWARE_FEATURE_NAMES:
        feature_block = "set-aware"
    else:
        raise ValueError("model feature schema does not match current UPBA energy schema")
    hand_weights = dict(zip(hand.feature_names, hand.weights, strict=True))
    hand_weights.update({f"aggregate::{name}": weight for name, weight in zip(hand.feature_names, hand.weights, strict=True)})

    rows = [
        {
            "feature": feature,
            "weight": float(weight),
            "hand_init_weight": float(hand_weights.get(feature, 0.0)),
            "delta_from_hand_init": float(weight - hand_weights.get(feature, 0.0)),
        }
        for feature, weight in zip(
            model.feature_names,
            model.weights,
            strict=True,
        )
    ]
    forbidden = [
        feature
        for feature in model.feature_names
        if any(fragment in feature for fragment in FORBIDDEN_FEATURE_SUBSTRINGS)
    ]
    reserved = [
        row
        for row in rows
        if str(row["feature"]).startswith("reserved_")
        or str(row["feature"]).startswith("aggregate::reserved_")
    ]
    reserved_nonzero = [
        row for row in reserved if abs(float(row["weight"])) > 1e-12
    ]
    nonzero = [row for row in rows if abs(float(row["weight"])) > 1e-12]
    return {
        "schema": "zenodex/energy/upba_v2_model_inspection/v1",
        "model_path": str(model_path),
        "feature_block": feature_block,
        "parameter_count": len(model.weights) + 1,
        "feature_dim": len(model.feature_names),
        "bias": float(model.bias),
        "nonzero_weight_count": len(nonzero),
        "weight_abs_sum": sum(abs(float(row["weight"])) for row in rows),
        "reserved_feature_count": len(reserved),
        "reserved_nonzero_count": len(reserved_nonzero),
        "reserved_weight_abs_sum": sum(abs(float(row["weight"])) for row in reserved),
        "forbidden_feature_names": forbidden,
        "top_positive_weights": sorted(rows, key=lambda row: float(row["weight"]), reverse=True)[:top_n],
        "top_negative_weights": sorted(rows, key=lambda row: float(row["weight"]))[:top_n],
        "largest_delta_from_hand_init": sorted(
            rows,
            key=lambda row: abs(float(row["delta_from_hand_init"])),
            reverse=True,
        )[:top_n],
    }


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Model Audit",
        "",
        "```text",
        f"model: {report['model_path']}",
        f"feature_block: {report['feature_block']}",
        f"parameters: {report['parameter_count']}",
        f"feature_dim: {report['feature_dim']}",
        f"nonzero_weight_count: {report['nonzero_weight_count']}",
        f"reserved_nonzero_count: {report['reserved_nonzero_count']}",
        f"forbidden_feature_names: {', '.join(report['forbidden_feature_names']) if report['forbidden_feature_names'] else 'none'}",
        "```",
        "",
        "Negative weights lower energy and move a candidate earlier. Positive weights raise energy and move a candidate later.",
        "",
        "## Largest Positive Weights",
        "",
        _weight_table(report["top_positive_weights"]),
        "",
        "## Largest Negative Weights",
        "",
        _weight_table(report["top_negative_weights"]),
        "",
        "## Largest Changes From Hand Initialization",
        "",
        _weight_table(report["largest_delta_from_hand_init"], include_delta=True),
        "",
    ]
    return "\n".join(lines)


def _weight_table(rows: list[dict[str, Any]], *, include_delta: bool = False) -> str:
    if include_delta:
        lines = [
            "| feature | weight | hand_init | delta |",
            "| --- | ---: | ---: | ---: |",
        ]
        for row in rows:
            lines.append(
                f"| {row['feature']} | {_fmt(row['weight'])} | "
                f"{_fmt(row['hand_init_weight'])} | {_fmt(row['delta_from_hand_init'])} |"
            )
        return "\n".join(lines)

    lines = [
        "| feature | weight |",
        "| --- | ---: |",
    ]
    for row in rows:
        lines.append(f"| {row['feature']} | {_fmt(row['weight'])} |")
    return "\n".join(lines)


def _fmt(value: object) -> str:
    return f"{float(value):.6g}"


if __name__ == "__main__":
    raise SystemExit(main())
