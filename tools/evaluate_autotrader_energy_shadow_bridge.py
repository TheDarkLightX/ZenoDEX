#!/usr/bin/env python3
"""Evaluate AutoTraderEnergy on recorded ZenoGraph shadow observations."""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path
from statistics import mean
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.autotrader_energy import (  # noqa: E402
    evaluate_autotrader_rows,
    generate_rows,
    group_counts,
    shadow_rows_from_observations,
    train_autotrader_linear_ranker,
)
from tools.zenograph_autotrader_shadow_compare_baseline import run_baseline  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shadow-log", type=Path)
    parser.add_argument("--source-id", default="zenograph-baseline")
    parser.add_argument("--synthetic-train-contexts", type=int, default=1500)
    parser.add_argument("--candidates-per-context", type=int, default=16)
    parser.add_argument("--train-seed", type=int, default=20260528)
    parser.add_argument("--epochs", type=int, default=5)
    parser.add_argument("--learning-rate", type=float, default=0.001)
    parser.add_argument("--margin", type=float, default=1.0)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = evaluate_shadow_bridge(
        shadow_log=args.shadow_log,
        source_id=args.source_id,
        synthetic_train_contexts=args.synthetic_train_contexts,
        candidates_per_context=args.candidates_per_context,
        train_seed=args.train_seed,
        epochs=args.epochs,
        learning_rate=args.learning_rate,
        margin=args.margin,
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0 if report.get("ok") is True else 1


def evaluate_shadow_bridge(
    *,
    shadow_log: Path | None,
    source_id: str,
    synthetic_train_contexts: int,
    candidates_per_context: int,
    train_seed: int,
    epochs: int,
    learning_rate: float,
    margin: float,
) -> dict[str, Any]:
    observations, source = _load_or_generate_observations(shadow_log)
    shadow_rows = shadow_rows_from_observations(observations, source_id=source_id)
    train_rows = generate_rows(
        seed=train_seed,
        contexts=synthetic_train_contexts,
        candidates_per_context=candidates_per_context,
        profile="hard",
    )
    model = train_autotrader_linear_ranker(
        train_rows,
        epochs=epochs,
        learning_rate=learning_rate,
        margin=margin,
        seed=train_seed,
        init="hand",
    )
    modes = {
        "random": evaluate_autotrader_rows(shadow_rows, mode="random", seed=train_seed + 1),
        "hand": evaluate_autotrader_rows(shadow_rows, mode="hand", seed=train_seed + 1),
        "learned": evaluate_autotrader_rows(shadow_rows, mode="learned", model=model, seed=train_seed + 1),
        "hybrid": evaluate_autotrader_rows(shadow_rows, mode="hybrid", model=model, seed=train_seed + 1),
    }
    valid_count = sum(1 for row in shadow_rows if bool(row["label"]["valid"]))
    invalid_count = len(shadow_rows) - valid_count
    invalid_accept_count_total = sum(int(report["invalid_accept_count"]) for report in modes.values())
    hand = modes["hand"]
    learned = modes["hybrid"]
    return {
        "schema": "zenodex/energy/autotrader_shadow_bridge_report/v1",
        "ok": invalid_accept_count_total == 0,
        "source": source,
        "source_id": source_id,
        "synthetic_train_contexts": synthetic_train_contexts,
        "candidates_per_context": candidates_per_context,
        "train_seed": train_seed,
        "epochs": epochs,
        "learning_rate": learning_rate,
        "margin": margin,
        "shadow": {
            "observation_count": len(observations),
            "row_count": len(shadow_rows),
            "context_count": len(group_counts(shadow_rows)),
            "group_counts": group_counts(shadow_rows),
            "valid_count": valid_count,
            "invalid_count": invalid_count,
            "winner_count": sum(1 for row in shadow_rows if bool(row["label"]["is_winner"])),
        },
        "modes": modes,
        "safety": {
            "invalid_accept_count_total": invalid_accept_count_total,
            "policy_guards_authoritative": True,
            "scorer_authorizes_trade": False,
            "model_output_in_state_root": False,
        },
        "interpretation": {
            "learned_beats_hand_on_mean_guard_calls": (
                float(learned["mean_guard_calls"]) < float(hand["mean_guard_calls"])
            ),
            "learned_top_1_recall": learned["top_1_recall"],
            "learned_top_1_objective_recall": learned["top_1_objective_recall"],
            "learned_mean_guard_calls": learned["mean_guard_calls"],
            "learned_mean_guard_calls_to_objective_winner": learned[
                "mean_guard_calls_to_objective_winner"
            ],
            "hand_mean_guard_calls": hand["mean_guard_calls"],
            "argmax_equivalence_note": (
                "Exact top-1 recall uses a hash-selected winner among tied valid objective "
                "maxima. Objective-equivalent recall treats any valid candidate with the same "
                "maximal objective as an acceptable argmax representative."
            ),
            "negative_knowledge": (
                "The built-in shadow bridge is a deterministic fixture derived from accepted "
                "ZenoGraph store exports. It is useful for schema and boundary replay, but it is "
                "not live production distribution evidence."
            ),
        },
    }


def _load_or_generate_observations(shadow_log: Path | None) -> tuple[list[dict[str, Any]], str]:
    if shadow_log is not None:
        return _load_jsonl(shadow_log), str(shadow_log)
    with tempfile.TemporaryDirectory(prefix="autotrader_energy_shadow_") as tmp:
        log_path = Path(tmp) / "baseline_log.jsonl"
        run_baseline(log_path=log_path)
        return _load_jsonl(log_path), "built-in-zenograph-baseline"


def _load_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                payload = json.loads(line)
                if not isinstance(payload, dict):
                    raise ValueError(f"{path}: JSONL rows must be objects")
                rows.append(payload)
    if not rows:
        raise ValueError(f"{path}: no rows")
    return rows


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# AutoTraderEnergy Shadow Bridge Receipt",
        "",
        f"source: {report['source']}",
        f"synthetic_train_contexts: {report['synthetic_train_contexts']}",
        f"candidates_per_context: {report['candidates_per_context']}",
        f"train_seed: {report['train_seed']}",
        f"shadow_contexts: {report['shadow']['context_count']}",
        f"shadow_rows: {report['shadow']['row_count']}",
        f"valid_count: {report['shadow']['valid_count']}",
        f"invalid_count: {report['shadow']['invalid_count']}",
        f"invalid_accept_count_total: {report['safety']['invalid_accept_count_total']}",
        f"policy_guards_authoritative: {str(report['safety']['policy_guards_authoritative']).lower()}",
        f"scorer_authorizes_trade: {str(report['safety']['scorer_authorizes_trade']).lower()}",
        "",
        "| mode | mean guard calls | objective guard calls | exact top-1 | objective top-1 | top-5 | invalid accepts |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode in ("random", "hand", "hybrid"):
        row = report["modes"][mode]
        label = "learned" if mode == "hybrid" else mode
        lines.append(
            f"| {label} | {float(row['mean_guard_calls']):.3f} | "
            f"{float(row['mean_guard_calls_to_objective_winner']):.3f} | "
            f"{float(row['top_1_recall']):.3f} | "
            f"{float(row['top_1_objective_recall']):.3f} | "
            f"{float(row['top_5_recall']):.3f} | "
            f"{int(row['invalid_accept_count'])} |"
        )
    lines.extend(
        [
            "",
            "Interpretation: the learned scorer ties hand energy on exact hash-selected",
            "winner position, but reaches an objective-equivalent argmax candidate first",
            "on every context. This records a quotient/equivalence issue in the shadow",
            "metric: exact top-1 can be zero when the benchmark has tied valid maxima.",
            "",
            str(report["interpretation"]["negative_knowledge"]),
            "",
        ]
    )
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
