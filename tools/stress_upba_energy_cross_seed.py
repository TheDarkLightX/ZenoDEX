#!/usr/bin/env python3
"""Run streaming cross-seed UPBA v2 energy stress benchmarks."""

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

from src.energy.upba_v2_mlp_energy import load_advisory_energy_model
from tools.benchmark_upba_energy_search import benchmark_modes


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=250)
    parser.add_argument("--seeds", default="20260518,20260519,20260520")
    parser.add_argument("--candidate-counts", default="20,32,50")
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--top-k", type=int, default=10)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    if args.batches <= 0:
        raise SystemExit("--batches must be positive")
    seeds = _parse_int_csv(args.seeds, name="--seeds")
    candidate_counts = _parse_int_csv(args.candidate_counts, name="--candidate-counts")
    if not seeds:
        raise SystemExit("--seeds must contain at least one integer")
    if not candidate_counts or any(count <= 1 for count in candidate_counts):
        raise SystemExit("--candidate-counts must contain integers greater than one")
    if not args.model.exists():
        raise SystemExit(f"model does not exist: {args.model}")

    model = load_advisory_energy_model(args.model)
    configs: list[dict[str, Any]] = []
    for candidate_count in candidate_counts:
        for seed in seeds:
            report = benchmark_modes(
                batches=args.batches,
                candidates_per_batch=candidate_count,
                seed=seed,
                model=model,
                top_k=args.top_k,
            )
            configs.append(
                {
                    "seed": seed,
                    "candidate_count": candidate_count,
                    "report": report,
                }
            )

    result = {
        "schema": "zenodex/energy/upba_v2_cross_seed_stress/v1",
        "batches_per_config": args.batches,
        "candidate_counts": candidate_counts,
        "seeds": seeds,
        "top_k": args.top_k,
        "model": str(args.model),
        "synthetic_batches_requested": args.batches * len(candidate_counts) * len(seeds),
        "synthetic_candidates_requested": args.batches
        * sum(candidate_counts)
        * len(seeds),
        "configs": configs,
        "summary": _summarize(configs),
    }
    encoded = json.dumps(result, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(result), encoding="utf-8")
    print(encoded)
    return 0


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
        modes = config["report"]["modes"]
        for mode, stats in modes.items():
            by_mode.setdefault(str(mode), []).append(stats)
    return {
        mode: {
            "configs": len(stats_list),
            "top_1_recall_mean": _mean_key(stats_list, "top_1_recall"),
            "top_1_recall_min": _min_key(stats_list, "top_1_recall"),
            "top_5_recall_mean": _mean_key(stats_list, "top_5_recall"),
            "top_5_recall_min": _min_key(stats_list, "top_5_recall"),
            "top_10_recall_mean": _mean_key(stats_list, "top_10_recall"),
            "top_10_recall_min": _min_key(stats_list, "top_10_recall"),
            "checked_stop_top_k_rate_mean": _mean_key(stats_list, "checked_stop_top_k_rate"),
            "checked_stop_top_k_rate_min": _min_key(stats_list, "checked_stop_top_k_rate"),
            "checked_stop_at_winner_rate_mean": _mean_key(stats_list, "checked_stop_at_winner_rate"),
            "mean_verifier_calls_mean": _mean_key(stats_list, "mean_verifier_calls"),
            "mean_verifier_calls_max": _max_key(stats_list, "mean_verifier_calls"),
            "p99_verifier_calls_max": _max_key(stats_list, "p99_verifier_calls"),
            "invalid_accept_count_total": sum(int(stats["invalid_accept_count"]) for stats in stats_list),
            "permutation_violation_count_total": sum(
                int(stats.get("permutation_violation_count", 0)) for stats in stats_list
            ),
        }
        for mode, stats_list in sorted(by_mode.items())
    }


def _mean_key(rows: list[dict[str, Any]], key: str) -> float:
    return mean(float(row[key]) for row in rows) if rows else 0.0


def _min_key(rows: list[dict[str, Any]], key: str) -> float:
    return min((float(row[key]) for row in rows), default=0.0)


def _max_key(rows: list[dict[str, Any]], key: str) -> float:
    return max((float(row[key]) for row in rows), default=0.0)


def _markdown_report(result: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Cross-Seed Stress Receipt",
        "",
        "```text",
        f"batches_per_config: {result['batches_per_config']}",
        f"seeds: {', '.join(str(seed) for seed in result['seeds'])}",
        f"candidate_counts: {', '.join(str(count) for count in result['candidate_counts'])}",
        f"synthetic_batches_requested: {result['synthetic_batches_requested']}",
        f"synthetic_candidates_requested: {result['synthetic_candidates_requested']}",
        f"top_k: {result['top_k']}",
        f"model: {result['model']}",
        "```",
        "",
        "| mode | configs | top1_mean | top1_min | top5_mean | top10_mean | top10_min | stop_top_k_mean | stop_top_k_min | stop_at_winner_mean | mean_calls | max_mean_calls | p99_max | invalid_accepts | perm_violations |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode, stats in result["summary"].items():
        lines.append(
            "| "
            + " | ".join(
                (
                    mode,
                    str(stats["configs"]),
                    _fmt(stats["top_1_recall_mean"]),
                    _fmt(stats["top_1_recall_min"]),
                    _fmt(stats["top_5_recall_mean"]),
                    _fmt(stats["top_10_recall_mean"]),
                    _fmt(stats["top_10_recall_min"]),
                    _fmt(stats["checked_stop_top_k_rate_mean"]),
                    _fmt(stats["checked_stop_top_k_rate_min"]),
                    _fmt(stats["checked_stop_at_winner_rate_mean"]),
                    _fmt(stats["mean_verifier_calls_mean"]),
                    _fmt(stats["mean_verifier_calls_max"]),
                    _fmt(stats["p99_verifier_calls_max"]),
                    str(stats["invalid_accept_count_total"]),
                    str(stats["permutation_violation_count_total"]),
                )
            )
            + " |"
        )
    lines.append("")
    lines.append("Per-configuration details are stored in the JSON receipt.")
    return "\n".join(lines) + "\n"


def _fmt(value: object) -> str:
    return f"{float(value):.3f}"


if __name__ == "__main__":
    raise SystemExit(main())
