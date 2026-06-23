#!/usr/bin/env python3
"""Build a comparable UPBA v2 advisory energy model leaderboard."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


MODEL_SPECS: tuple[dict[str, Any], ...] = (
    {
        "model_id": "upba_v2_gap_weighted_default_seed20260517",
        "kind": "retained_baseline",
        "holdout_compare": "data/upba_energy/upba_v2_energy_gemini_highwinner_holdout_compare.json",
        "holdout_mode": "gap_weighted",
        "cross_seed": "data/upba_energy/upba_v2_energy_gap_weighted_cross_seed_stress_250x3x3.json",
        "cross_seed_mode": "learned",
        "hard_cases": "data/upba_energy/upba_v2_energy_gap_weighted_hard_cases_500x3x3.json",
    },
    {
        "model_id": "gemini_log_interactions_seed20260517",
        "kind": "candidate",
        "holdout_compare": "data/upba_energy/upba_v2_energy_gemini_log_interactions_holdout_compare.json",
        "holdout_mode": "gemini",
        "cross_seed": "data/upba_energy/upba_v2_energy_gemini_log_interactions_cross_seed_250x3x3.json",
        "cross_seed_mode": "learned",
        "hard_cases": "data/upba_energy/upba_v2_energy_gemini_log_interactions_hard_cases_500x3x3.json",
    },
    {
        "model_id": "gemini_objective8_seed20260517",
        "kind": "candidate",
        "holdout_compare": "data/upba_energy/upba_v2_energy_gemini_objective8_holdout_compare.json",
        "holdout_mode": "gemini",
        "cross_seed": "data/upba_energy/upba_v2_energy_gemini_objective8_cross_seed_250x3x3.json",
        "cross_seed_mode": "learned",
        "hard_cases": "data/upba_energy/upba_v2_energy_gemini_objective8_hard_cases_500x3x3.json",
    },
    {
        "model_id": "gemini_highwinner_seed20260517",
        "kind": "retained_linear_fallback",
        "holdout_compare": "data/upba_energy/upba_v2_energy_gemini_highwinner_holdout_compare.json",
        "holdout_mode": "gemini",
        "cross_seed": "data/upba_energy/upba_v2_energy_gemini_highwinner_cross_seed_250x3x3.json",
        "cross_seed_mode": "learned",
        "hard_cases": "data/upba_energy/upba_v2_energy_gemini_highwinner_hard_cases_500x3x3.json",
    },
    {
        "model_id": "gemini_linear_v5_seed20260519",
        "kind": "negative_candidate",
        "holdout_compare": "data/upba_energy/upba_v2_energy_gemini_v5_holdout_compare.json",
        "holdout_mode": "gemini",
        "cross_seed": "data/upba_energy/upba_v2_energy_gemini_v5_cross_seed_250x3x3.json",
        "cross_seed_mode": "learned",
        "hard_cases": "data/upba_energy/upba_v2_energy_gemini_v5_hard_cases_500x3x3.json",
    },
    {
        "model_id": "gemini_mlp_v6_seed20260519",
        "kind": "promoted_research_candidate",
        "holdout_compare": "data/upba_energy/upba_v2_energy_gemini_v6_holdout_compare.json",
        "holdout_mode": "gemini",
        "cross_seed": "data/upba_energy/upba_v2_energy_gemini_v6_cross_seed_250x3x3.json",
        "cross_seed_mode": "learned",
        "hard_cases": "data/upba_energy/upba_v2_energy_gemini_v6_hard_cases_500x3x3.json",
    },
    {
        "model_id": "gemini_handinit_seed20260517",
        "kind": "holdout_only_negative",
        "holdout_compare": "data/upba_energy/upba_v2_energy_gemini_handinit_holdout_compare.json",
        "holdout_mode": "gemini",
    },
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = build_leaderboard()
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown(report), encoding="utf-8")
    print(encoded)
    return 0 if report["promoted_model_id"] is not None else 1


def build_leaderboard() -> dict[str, Any]:
    rows = [_build_row(spec) for spec in MODEL_SPECS]
    full_rows = [row for row in rows if row["coverage"]["full_three_lane"]]
    promoted_model_id = "gemini_mlp_v6_seed20260519"
    promoted = _by_id(rows, promoted_model_id)

    obligations = [
        _obligation(
            "holdout_best_mean_calls",
            promoted["metrics"]["holdout"]["mean_verifier_calls"]
            == min(row["metrics"]["holdout"]["mean_verifier_calls"] for row in rows),
        ),
        _obligation(
            "holdout_best_top1",
            promoted["metrics"]["holdout"]["top_1_recall"]
            == max(row["metrics"]["holdout"]["top_1_recall"] for row in rows),
        ),
        _obligation(
            "cross_seed_best_mean_calls",
            promoted["metrics"]["cross_seed"]["mean_verifier_calls_mean"]
            == min(
                row["metrics"]["cross_seed"]["mean_verifier_calls_mean"]
                for row in full_rows
            ),
        ),
        _obligation(
            "cross_seed_best_worst_top1",
            promoted["metrics"]["cross_seed"]["top_1_recall_min"]
            == max(row["metrics"]["cross_seed"]["top_1_recall_min"] for row in full_rows),
        ),
        _obligation(
            "hard_case_best_top1",
            promoted["metrics"]["hard_cases"]["top_1_recall"]
            == max(row["metrics"]["hard_cases"]["top_1_recall"] for row in full_rows),
        ),
        _obligation(
            "hard_case_fewest_top1_misses",
            promoted["metrics"]["hard_cases"]["top1_miss_count"]
            == min(row["metrics"]["hard_cases"]["top1_miss_count"] for row in full_rows),
        ),
        _obligation(
            "safety_counts_clean",
            promoted["metrics"]["holdout"]["invalid_accept_count"] == 0
            and promoted["metrics"]["cross_seed"]["invalid_accept_count_total"] == 0
            and promoted["metrics"]["cross_seed"][
                "permutation_violation_count_total"
            ]
            == 0,
        ),
    ]
    ok = all(item["passed"] for item in obligations)
    return {
        "schema": "zenodex/energy/upba_v2_model_leaderboard/v1",
        "scope": "advisory_ranking_only",
        "decision": "promote_v6_research_candidate" if ok else "hold_current_default",
        "promoted_model_id": promoted_model_id if ok else None,
        "compared_model_count": len(rows),
        "full_three_lane_model_count": len(full_rows),
        "models": rows,
        "obligations": obligations,
        "blocked_reasons": [item["id"] for item in obligations if not item["passed"]],
        "non_claims": [
            "The leaderboard compares advisory rankers only.",
            "It does not authorize settlement, replace deterministic verification, or establish production replay coverage.",
            "Holdout-only rows are not used for cross-seed or hard-case dominance claims.",
        ],
    }


def _build_row(spec: dict[str, Any]) -> dict[str, Any]:
    holdout = _load_json(Path(spec["holdout_compare"]))["modes"][spec["holdout_mode"]]
    row: dict[str, Any] = {
        "model_id": spec["model_id"],
        "kind": spec["kind"],
        "source_paths": {
            "holdout_compare": spec["holdout_compare"],
        },
        "coverage": {
            "holdout": True,
            "cross_seed": "cross_seed" in spec,
            "hard_cases": "hard_cases" in spec,
            "full_three_lane": "cross_seed" in spec and "hard_cases" in spec,
        },
        "metrics": {
            "holdout": _select(
                holdout,
                "mean_verifier_calls",
                "p99_verifier_calls",
                "top_1_recall",
                "top_10_recall",
                "invalid_accept_count",
            )
        },
    }
    if "cross_seed" in spec:
        cross = _load_json(Path(spec["cross_seed"]))["summary"][spec["cross_seed_mode"]]
        row["source_paths"]["cross_seed"] = spec["cross_seed"]
        row["metrics"]["cross_seed"] = _select(
            cross,
            "mean_verifier_calls_mean",
            "mean_verifier_calls_max",
            "top_1_recall_mean",
            "top_1_recall_min",
            "top_10_recall_min",
            "invalid_accept_count_total",
            "permutation_violation_count_total",
        )
    if "hard_cases" in spec:
        hard = _load_json(Path(spec["hard_cases"]))["summary"]
        row["source_paths"]["hard_cases"] = spec["hard_cases"]
        row["metrics"]["hard_cases"] = _select(
            hard,
            "top_1_recall",
            "top_5_recall",
            "top_10_recall",
            "top1_miss_count",
            "top5_miss_count",
            "top10_miss_count",
            "mean_winner_position_mean",
            "max_mean_winner_position",
        )
    return row


def _by_id(rows: list[dict[str, Any]], model_id: str) -> dict[str, Any]:
    for row in rows:
        if row["model_id"] == model_id:
            return row
    raise KeyError(model_id)


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _select(row: dict[str, Any], *keys: str) -> dict[str, Any]:
    return {key: row[key] for key in keys if key in row}


def _obligation(check_id: str, passed: bool) -> dict[str, Any]:
    return {"id": check_id, "passed": bool(passed)}


def _markdown(report: dict[str, Any]) -> str:
    lines = [
        "# UPBA v2 Energy Model Leaderboard",
        "",
        f"- Decision: `{report['decision']}`",
        f"- Promoted model: `{report['promoted_model_id']}`",
        f"- Compared models: `{report['compared_model_count']}`",
        f"- Full three-lane models: `{report['full_three_lane_model_count']}`",
        "",
        "## Holdout",
        "",
        "| model | mean calls | p99 calls | top-1 | top-10 | invalid accepts |",
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in sorted(
        report["models"], key=lambda item: item["metrics"]["holdout"]["mean_verifier_calls"]
    ):
        metrics = row["metrics"]["holdout"]
        lines.append(
            "| "
            + " | ".join(
                (
                    row["model_id"],
                    _fmt(metrics["mean_verifier_calls"]),
                    _fmt(metrics["p99_verifier_calls"]),
                    _fmt(metrics["top_1_recall"]),
                    _fmt(metrics["top_10_recall"]),
                    _fmt(metrics["invalid_accept_count"]),
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "## Cross-Seed And Hard Cases",
            "",
            "| model | cross mean calls | cross worst top-1 | hard top-1 | hard top-1 misses |",
            "| --- | ---: | ---: | ---: | ---: |",
        ]
    )
    full_rows = [row for row in report["models"] if row["coverage"]["full_three_lane"]]
    for row in sorted(
        full_rows, key=lambda item: item["metrics"]["cross_seed"]["mean_verifier_calls_mean"]
    ):
        cross = row["metrics"]["cross_seed"]
        hard = row["metrics"]["hard_cases"]
        lines.append(
            "| "
            + " | ".join(
                (
                    row["model_id"],
                    _fmt(cross["mean_verifier_calls_mean"]),
                    _fmt(cross["top_1_recall_min"]),
                    _fmt(hard["top_1_recall"]),
                    _fmt(hard["top1_miss_count"]),
                )
            )
            + " |"
        )
    lines.extend(["", "## Obligations", ""])
    for item in report["obligations"]:
        status = "pass" if item["passed"] else "fail"
        lines.append(f"- `{status}` `{item['id']}`")
    lines.extend(["", "## Non-Claims", ""])
    for item in report["non_claims"]:
        lines.append(f"- {item}")
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    if isinstance(value, int):
        return str(value)
    numeric = float(value)
    if numeric.is_integer():
        return str(int(numeric))
    return f"{numeric:.12g}"


if __name__ == "__main__":
    sys.exit(main())
