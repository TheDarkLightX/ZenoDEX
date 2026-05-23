#!/usr/bin/env python3
"""Build a compact UPBA v2 ZenoEnergy candidate promotion review."""

from __future__ import annotations

import argparse
import json
import sys
from hashlib import sha256
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--candidate-model",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_gemini_log_interactions_seed20260517.json"),
    )
    parser.add_argument(
        "--holdout-compare",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_gemini_log_interactions_holdout_compare.json"),
    )
    parser.add_argument(
        "--candidate-cross-seed",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_gemini_log_interactions_cross_seed_250x3x3.json"),
    )
    parser.add_argument(
        "--candidate-hard-cases",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_gemini_log_interactions_hard_cases_500x3x3.json"),
    )
    parser.add_argument(
        "--baseline-cross-seed",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_gap_weighted_cross_seed_stress_250x3x3.json"),
    )
    parser.add_argument(
        "--baseline-hard-cases",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_gap_weighted_hard_cases_500x3x3.json"),
    )
    parser.add_argument("--candidate-id", default="gemini_log_interactions_seed20260517")
    parser.add_argument("--baseline-id", default="upba_v2_gap_weighted_default_seed20260517")
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = build_review(
        candidate_id=args.candidate_id,
        baseline_id=args.baseline_id,
        candidate_model=args.candidate_model,
        holdout_compare=_load_json(args.holdout_compare),
        candidate_cross_seed=_load_json(args.candidate_cross_seed),
        candidate_hard_cases=_load_json(args.candidate_hard_cases),
        baseline_cross_seed=_load_json(args.baseline_cross_seed),
        baseline_hard_cases=_load_json(args.baseline_hard_cases),
        source_paths={
            "candidate_model": str(args.candidate_model),
            "holdout_compare": str(args.holdout_compare),
            "candidate_cross_seed": str(args.candidate_cross_seed),
            "candidate_hard_cases": str(args.candidate_hard_cases),
            "baseline_cross_seed": str(args.baseline_cross_seed),
            "baseline_hard_cases": str(args.baseline_hard_cases),
        },
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0 if report["decision"] in {"promote_candidate", "hold_candidate"} else 1


def build_review(
    *,
    candidate_id: str = "gemini_log_interactions_seed20260517",
    baseline_id: str = "upba_v2_gap_weighted_default_seed20260517",
    candidate_model: Path,
    holdout_compare: dict[str, Any],
    candidate_cross_seed: dict[str, Any],
    candidate_hard_cases: dict[str, Any],
    baseline_cross_seed: dict[str, Any],
    baseline_hard_cases: dict[str, Any],
    source_paths: dict[str, str],
) -> dict[str, Any]:
    holdout_gap = holdout_compare["modes"]["gap_weighted"]
    holdout_candidate = holdout_compare["modes"]["gemini"]
    baseline_cross = baseline_cross_seed["summary"]["learned"]
    candidate_cross = candidate_cross_seed["summary"]["learned"]
    baseline_hard = baseline_hard_cases["summary"]
    candidate_hard = candidate_hard_cases["summary"]

    obligations = [
        _obligation(
            "holdout_beats_baseline_mean_calls",
            float(holdout_candidate["mean_verifier_calls"]) < float(holdout_gap["mean_verifier_calls"]),
            {
                "candidate": holdout_candidate["mean_verifier_calls"],
                "baseline": holdout_gap["mean_verifier_calls"],
            },
        ),
        _obligation(
            "holdout_preserves_top10",
            float(holdout_candidate["top_10_recall"]) >= float(holdout_gap["top_10_recall"]),
            {
                "candidate": holdout_candidate["top_10_recall"],
                "baseline": holdout_gap["top_10_recall"],
            },
        ),
        _obligation(
            "cross_seed_beats_mean_calls",
            float(candidate_cross["mean_verifier_calls_mean"]) <= float(baseline_cross["mean_verifier_calls_mean"]),
            {
                "candidate": candidate_cross["mean_verifier_calls_mean"],
                "baseline": baseline_cross["mean_verifier_calls_mean"],
            },
        ),
        _obligation(
            "cross_seed_preserves_worst_top1",
            float(candidate_cross["top_1_recall_min"]) >= float(baseline_cross["top_1_recall_min"]),
            {
                "candidate": candidate_cross["top_1_recall_min"],
                "baseline": baseline_cross["top_1_recall_min"],
            },
        ),
        _obligation(
            "hard_cases_preserve_top1",
            float(candidate_hard["top_1_recall"]) >= float(baseline_hard["top_1_recall"]),
            {
                "candidate": candidate_hard["top_1_recall"],
                "baseline": baseline_hard["top_1_recall"],
            },
        ),
        _obligation(
            "safety_counts_clean",
            int(holdout_candidate["invalid_accept_count"]) == 0
            and int(candidate_cross["invalid_accept_count_total"]) == 0
            and int(candidate_cross["permutation_violation_count_total"]) == 0,
            {
                "holdout_invalid_accept_count": holdout_candidate["invalid_accept_count"],
                "cross_seed_invalid_accept_count_total": candidate_cross["invalid_accept_count_total"],
                "cross_seed_permutation_violation_count_total": candidate_cross[
                    "permutation_violation_count_total"
                ],
            },
        ),
    ]
    promote_ready = all(bool(item["passed"]) for item in obligations)
    decision = "promote_candidate" if promote_ready else "hold_candidate"
    review_note = (
        "The candidate passes the configured advisory-ranking promotion obligations "
        f"against `{baseline_id}`."
        if promote_ready
        else (
            "The candidate improves some metrics, but is not promoted while one or more "
            "configured tail, hard-case, or safety obligations are below the retained "
            f"baseline `{baseline_id}`."
        )
    )
    return {
        "schema": "zenodex/energy/upba_v2_candidate_promotion_review/v1",
        "candidate_id": candidate_id,
        "baseline_id": baseline_id,
        "decision": decision,
        "promotion_allowed": promote_ready,
        "scope": "advisory_ranking_only",
        "source_paths": source_paths,
        "candidate_model_sha256": _sha256_file(candidate_model),
        "metrics": {
            "holdout": {
                "baseline": _select(
                    holdout_gap,
                    "top_1_recall",
                    "top_10_recall",
                    "mean_verifier_calls",
                    "invalid_accept_count",
                ),
                "candidate": _select(
                    holdout_candidate,
                    "top_1_recall",
                    "top_10_recall",
                    "mean_verifier_calls",
                    "invalid_accept_count",
                ),
                "delta": _delta(
                    candidate=holdout_candidate,
                    baseline=holdout_gap,
                    keys=("top_1_recall", "top_10_recall", "mean_verifier_calls"),
                ),
            },
            "cross_seed": {
                "baseline": _select(
                    baseline_cross,
                    "top_1_recall_mean",
                    "top_1_recall_min",
                    "top_10_recall_min",
                    "mean_verifier_calls_mean",
                    "mean_verifier_calls_max",
                    "invalid_accept_count_total",
                    "permutation_violation_count_total",
                ),
                "candidate": _select(
                    candidate_cross,
                    "top_1_recall_mean",
                    "top_1_recall_min",
                    "top_10_recall_min",
                    "mean_verifier_calls_mean",
                    "mean_verifier_calls_max",
                    "invalid_accept_count_total",
                    "permutation_violation_count_total",
                ),
                "delta": _delta(
                    candidate=candidate_cross,
                    baseline=baseline_cross,
                    keys=(
                        "top_1_recall_mean",
                        "top_1_recall_min",
                        "top_10_recall_min",
                        "mean_verifier_calls_mean",
                        "mean_verifier_calls_max",
                    ),
                ),
            },
            "hard_cases": {
                "baseline": _select(
                    baseline_hard,
                    "top_1_recall",
                    "top_5_recall",
                    "top_10_recall",
                    "top1_miss_count",
                    "top5_miss_count",
                    "top10_miss_count",
                    "mean_winner_position_mean",
                    "max_mean_winner_position",
                ),
                "candidate": _select(
                    candidate_hard,
                    "top_1_recall",
                    "top_5_recall",
                    "top_10_recall",
                    "top1_miss_count",
                    "top5_miss_count",
                    "top10_miss_count",
                    "mean_winner_position_mean",
                    "max_mean_winner_position",
                ),
                "delta": _delta(
                    candidate=candidate_hard,
                    baseline=baseline_hard,
                    keys=(
                        "top_1_recall",
                        "top_5_recall",
                        "top_10_recall",
                        "top1_miss_count",
                        "mean_winner_position_mean",
                        "max_mean_winner_position",
                    ),
                ),
            },
        },
        "obligations": obligations,
        "blocked_reasons": [item["id"] for item in obligations if not bool(item["passed"])],
        "safety_contract": {
            "deterministic_verifier_authoritative": True,
            "model_authorizes_settlement": False,
            "model_output_in_state_root": False,
            "deterministic_fallback_required": True,
        },
        "review_note": review_note,
    }


def _obligation(check_id: str, passed: bool, observed: dict[str, Any]) -> dict[str, Any]:
    return {"id": check_id, "passed": bool(passed), "observed": observed}


def _select(row: dict[str, Any], *keys: str) -> dict[str, Any]:
    return {key: row.get(key, 0) for key in keys}


def _delta(
    *,
    candidate: dict[str, Any],
    baseline: dict[str, Any],
    keys: tuple[str, ...],
) -> dict[str, float]:
    return {key: float(candidate[key]) - float(baseline[key]) for key in keys}


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256_file(path: Path) -> str:
    digest = sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return f"sha256:{digest.hexdigest()}"


def _markdown_report(report: dict[str, Any]) -> str:
    metrics = report["metrics"]
    lines = [
        "# UPBA v2 Energy Candidate Promotion Review",
        "",
        f"- Candidate: `{report['candidate_id']}`",
        f"- Baseline: `{report['baseline_id']}`",
        f"- Decision: `{report['decision']}`",
        f"- Promotion allowed: `{report['promotion_allowed']}`",
        f"- Scope: `{report['scope']}`",
        f"- Candidate model sha256: `{report['candidate_model_sha256']}`",
        "",
        report["review_note"],
        "",
        "## Safety Contract",
        "",
    ]
    for key, value in report["safety_contract"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Evidence Sources",
            "",
        ]
    )
    for key, value in sorted(report["source_paths"].items()):
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Key Metrics",
            "",
            "| lane | metric | baseline | candidate | delta |",
            "| --- | --- | ---: | ---: | ---: |",
        ]
    )
    for lane, lane_metrics in metrics.items():
        for key, candidate_value in lane_metrics["candidate"].items():
            if key not in lane_metrics["baseline"]:
                continue
            baseline_value = lane_metrics["baseline"][key]
            delta = lane_metrics["delta"].get(key)
            delta_text = "n/a" if delta is None else _fmt(delta)
            lines.append(
                f"| `{lane}` | `{key}` | `{_fmt(baseline_value)}` | `{_fmt(candidate_value)}` | `{delta_text}` |"
            )
    lines.extend(["", "## Obligations", ""])
    for item in report["obligations"]:
        status = "pass" if item["passed"] else "fail"
        lines.append(f"- `{status}` `{item['id']}`")
    if report["blocked_reasons"]:
        lines.extend(["", "Blocked reasons:"])
        for reason in report["blocked_reasons"]:
            lines.append(f"- `{reason}`")
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    if isinstance(value, int):
        return str(value)
    numeric = float(value)
    if numeric.is_integer():
        return str(int(numeric))
    return f"{numeric:.12g}"


if __name__ == "__main__":
    raise SystemExit(main())
