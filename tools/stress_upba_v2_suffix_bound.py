#!/usr/bin/env python3
"""Run cross-seed stress for UPBA v2 suffix-bound early stop."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from statistics import mean
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.check_upba_v2_suffix_bound import run_suffix_bound_benchmark


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=60)
    parser.add_argument("--seeds", default="20260541,20260542,20260543")
    parser.add_argument("--candidate-counts", default="20,32,50")
    parser.add_argument(
        "--model",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json"),
    )
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    seeds = _parse_int_csv(args.seeds, name="--seeds")
    candidate_counts = _parse_int_csv(args.candidate_counts, name="--candidate-counts")
    if args.batches <= 0:
        raise SystemExit("--batches must be positive")
    if not seeds:
        raise SystemExit("--seeds must contain at least one integer")
    if not candidate_counts or any(count <= 1 for count in candidate_counts):
        raise SystemExit("--candidate-counts must contain integers greater than one")
    if not args.model.exists():
        raise SystemExit(f"model does not exist: {args.model}")

    report = stress_suffix_bound(
        batches=args.batches,
        seeds=tuple(seeds),
        candidate_counts=tuple(candidate_counts),
        model_path=args.model,
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    print(encoded)
    return 0 if report["ok"] else 1


def stress_suffix_bound(
    *,
    batches: int,
    seeds: tuple[int, ...],
    candidate_counts: tuple[int, ...],
    model_path: Path,
) -> dict[str, Any]:
    configs: list[dict[str, Any]] = []
    for candidate_count in candidate_counts:
        for seed in seeds:
            report = run_suffix_bound_benchmark(
                batches=batches,
                candidates_per_batch=candidate_count,
                seed=seed,
                model_path=model_path,
            )
            configs.append(
                {
                    "seed": seed,
                    "candidate_count": candidate_count,
                    "report": report,
                }
            )

    summary = _summarize(configs)
    learned = summary["learned"]
    hybrid = summary["hybrid"]
    hand = summary["hand"]
    random = summary["random"]
    ok = (
        int(learned["invalid_accept_count_total"]) == 0
        and int(hybrid["invalid_accept_count_total"]) == 0
        and float(learned["objective_equiv_accept_rate_min"]) == 1.0
        and float(hybrid["objective_equiv_accept_rate_min"]) == 1.0
        and float(learned["mean_verifier_calls_mean"]) <= float(hand["mean_verifier_calls_mean"])
        and float(hybrid["mean_verifier_calls_mean"]) <= float(hand["mean_verifier_calls_mean"])
        and float(learned["mean_verifier_calls_mean"]) < float(random["mean_verifier_calls_mean"])
    )
    return {
        "schema": "zenodex/energy/upba_v2_suffix_bound_cross_seed/v1",
        "ok": ok,
        "batches_per_config": batches,
        "seeds": list(seeds),
        "candidate_counts": list(candidate_counts),
        "model_path": str(model_path),
        "synthetic_batches_requested": batches * len(seeds) * len(candidate_counts),
        "synthetic_candidates_requested": batches * len(seeds) * sum(candidate_counts),
        "configs": configs,
        "summary": summary,
        "safety": {
            "invalid_accept_count_total": sum(
                int(mode["invalid_accept_count_total"]) for mode in summary.values()
            ),
            "verifier_authoritative": True,
            "scorer_authorizes_settlement": False,
            "model_output_in_state_root": False,
            "deterministic_suffix_bound_required": True,
        },
        "negative_knowledge": [
            "Cross-seed suffix-bound stress remains bounded synthetic evidence.",
            "A stable suffix-bound stress result still does not prove candidate-family coverage.",
        ],
    }


def _parse_int_csv(value: str, *, name: str) -> list[int]:
    out: list[int] = []
    for part in value.split(","):
        stripped = part.strip()
        if not stripped:
            continue
        try:
            out.append(int(stripped))
        except ValueError as exc:
            raise SystemExit(f"{name} contains a non-integer value: {stripped}") from exc
    return out


def _summarize(configs: list[dict[str, Any]]) -> dict[str, Any]:
    by_mode: dict[str, list[dict[str, Any]]] = {}
    for config in configs:
        report = config["report"]
        for mode, stats in report["summary"].items():
            row = dict(stats)
            row["evaluated_batches"] = report["evaluated_batches"]
            by_mode.setdefault(str(mode), []).append(row)
    return {
        mode: {
            "configs": len(rows),
            "evaluated_batches_total": sum(int(row["evaluated_batches"]) for row in rows),
            "mean_verifier_calls_mean": _mean_key(rows, "mean_verifier_calls"),
            "mean_verifier_calls_max": _max_key(rows, "mean_verifier_calls"),
            "p95_verifier_calls_max": _max_key(rows, "p95_verifier_calls"),
            "p99_verifier_calls_max": _max_key(rows, "p99_verifier_calls"),
            "max_verifier_calls_max": _max_key(rows, "max_verifier_calls"),
            "mean_checked_ratio_mean": _mean_key(rows, "mean_checked_ratio"),
            "full_fallback_count_total": sum(int(row["full_fallback_count"]) for row in rows),
            "suffix_stop_rate_min": _min_rate(rows, "stopped_by_suffix_bound_count"),
            "objective_equiv_accept_rate_min": _min_rate(rows, "objective_equiv_accept_count"),
            "certificate_ok_rate_min": _min_rate(rows, "certificate_ok_count"),
            "invalid_accept_count_total": sum(int(row["invalid_accept_count"]) for row in rows),
            "mean_suffix_disqualified_count_mean": _mean_key(rows, "mean_suffix_disqualified_count"),
        }
        for mode, rows in sorted(by_mode.items())
    }


def _mean_key(rows: list[dict[str, Any]], key: str) -> float:
    return mean(float(row[key]) for row in rows) if rows else 0.0


def _max_key(rows: list[dict[str, Any]], key: str) -> float:
    return max((float(row[key]) for row in rows), default=0.0)


def _min_rate(rows: list[dict[str, Any]], numerator_key: str) -> float:
    return min(
        (float(row[numerator_key]) / max(1.0, float(row["count"])) for row in rows),
        default=0.0,
    )


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Suffix-Bound Cross-Seed Stress",
        "",
        "```text",
        f"batches_per_config: {report['batches_per_config']}",
        f"seeds: {', '.join(str(seed) for seed in report['seeds'])}",
        f"candidate_counts: {', '.join(str(count) for count in report['candidate_counts'])}",
        f"synthetic_batches_requested: {report['synthetic_batches_requested']}",
        f"synthetic_candidates_requested: {report['synthetic_candidates_requested']}",
        f"model: {report['model_path']}",
        "```",
        "",
        "| mode | configs | mean calls | max mean calls | p95 max | p99 max | max calls | objective-equiv min | suffix-stop min | full fallbacks | invalid accepts |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode, stats in report["summary"].items():
        lines.append(
            "| "
            + " | ".join(
                (
                    mode,
                    str(stats["configs"]),
                    _fmt(stats["mean_verifier_calls_mean"]),
                    _fmt(stats["mean_verifier_calls_max"]),
                    _fmt(stats["p95_verifier_calls_max"]),
                    _fmt(stats["p99_verifier_calls_max"]),
                    _fmt(stats["max_verifier_calls_max"]),
                    _fmt(stats["objective_equiv_accept_rate_min"]),
                    _fmt(stats["suffix_stop_rate_min"]),
                    str(stats["full_fallback_count_total"]),
                    str(stats["invalid_accept_count_total"]),
                )
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "## Negative Knowledge",
            "",
        ]
    )
    for item in report["negative_knowledge"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


def _fmt(value: object) -> str:
    return f"{float(value):.4f}"


if __name__ == "__main__":
    raise SystemExit(main())
