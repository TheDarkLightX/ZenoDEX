#!/usr/bin/env python3
"""Mine compact hard-case reports from streaming UPBA v2 synthetic batches."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from random import Random
from statistics import mean
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.energy.upba_v2_energy_model import load_linear_model
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import primary_energy_failure_from_record
from src.energy.upba_v2_ranker import advisory_candidate_hash, verify_candidates_in_order
from tools.generate_upba_energy_dataset import generate_synthetic_batch


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=1_000)
    parser.add_argument("--seeds", default="20260521,20260522,20260523")
    parser.add_argument("--candidate-counts", default="50")
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--max-examples", type=int, default=25)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    if args.batches <= 0:
        raise SystemExit("--batches must be positive")
    if args.max_examples < 0:
        raise SystemExit("--max-examples must be nonnegative")
    seeds = _parse_int_csv(args.seeds, name="--seeds")
    candidate_counts = _parse_int_csv(args.candidate_counts, name="--candidate-counts")
    if not seeds:
        raise SystemExit("--seeds must contain at least one integer")
    if not candidate_counts or any(count <= 1 for count in candidate_counts):
        raise SystemExit("--candidate-counts must contain integers greater than one")
    if not args.model.exists():
        raise SystemExit(f"model does not exist: {args.model}")

    model = load_linear_model(args.model)
    configs = [
        _mine_config(
            seed=seed,
            batches=args.batches,
            candidate_count=candidate_count,
            model=model,
            max_examples=args.max_examples,
        )
        for candidate_count in candidate_counts
        for seed in seeds
    ]
    result = {
        "schema": "zenodex/energy/upba_v2_hard_case_mining/v1",
        "batches_per_config": args.batches,
        "candidate_counts": candidate_counts,
        "seeds": seeds,
        "model": str(args.model),
        "synthetic_batches_requested": args.batches * len(candidate_counts) * len(seeds),
        "synthetic_candidates_requested": args.batches * sum(candidate_counts) * len(seeds),
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


def _mine_config(
    *,
    seed: int,
    batches: int,
    candidate_count: int,
    model: object,
    max_examples: int,
) -> dict[str, Any]:
    rng = Random(seed)
    positions: list[int] = []
    examples: list[dict[str, Any]] = []
    candidate_type_counts: Counter[str] = Counter()
    winner_type_counts: Counter[str] = Counter()
    top1_miss_top_type_counts: Counter[str] = Counter()
    top1_miss_winner_type_counts: Counter[str] = Counter()
    top1_miss_top_error_counts: Counter[str] = Counter()
    top1_miss_primary_failure_counts: Counter[str] = Counter()
    no_winner_count = 0

    for batch_index in range(batches):
        batch = generate_synthetic_batch(
            rng=rng,
            batch_index=batch_index,
            target_candidate_count=candidate_count,
        )
        candidates = [item.candidate for item in batch.candidates]
        type_by_hash = {
            advisory_candidate_hash(item.candidate): item.candidate_type
            for item in batch.candidates
        }
        candidate_type_counts.update(type_by_hash.values())
        verified = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=candidates,
        )
        accepted = [result for result in verified if result.ok]
        if not accepted:
            no_winner_count += 1
            continue
        winner = max(accepted, key=lambda result: (result.volume, result.surplus, result.certificate_hash))
        winner_type = type_by_hash.get(winner.certificate_hash, "unknown")
        winner_type_counts[winner_type] += 1

        scored = []
        records_by_hash = {}
        for candidate in candidates:
            candidate_hash = advisory_candidate_hash(candidate)
            record = extract_upba_v2_feature_record(
                pool=batch.pool,
                intents=batch.intents,
                balances=batch.balances,
                candidate=candidate,
                include_verifier_label=False,
            )
            records_by_hash[candidate_hash] = record
            scored.append((float(model.energy(record.values)), candidate_hash, candidate))
        scored.sort(key=lambda item: (item[0], item[1]))
        winner_position = next(
            index
            for index, (_, candidate_hash, _) in enumerate(scored, start=1)
            if candidate_hash == winner.certificate_hash
        )
        positions.append(winner_position)
        if winner_position == 1:
            continue

        top_energy, top_hash, _ = scored[0]
        top_result = next(result for result in verified if result.certificate_hash == top_hash)
        top_type = type_by_hash.get(top_hash, "unknown")
        top1_miss_top_type_counts[top_type] += 1
        top1_miss_winner_type_counts[winner_type] += 1
        top1_miss_top_error_counts[str(top_result.error)] += 1
        primary_failure = primary_energy_failure_from_record(records_by_hash[top_hash])
        top1_miss_primary_failure_counts[str(primary_failure)] += 1
        if len(examples) < max_examples:
            examples.append(
                {
                    "seed": seed,
                    "batch_index": batch_index,
                    "candidate_count": candidate_count,
                    "winner_position": winner_position,
                    "winner_hash": winner.certificate_hash,
                    "winner_type": winner_type,
                    "winner_volume": winner.volume,
                    "winner_surplus": winner.surplus,
                    "top_hash": top_hash,
                    "top_type": top_type,
                    "top_energy": top_energy,
                    "top_verifier_ok": top_result.ok,
                    "top_verifier_error": top_result.error,
                    "top_volume": top_result.volume,
                    "top_surplus": top_result.surplus,
                    "volume_gap": winner.volume - top_result.volume,
                    "surplus_gap": winner.surplus - top_result.surplus,
                    "top_primary_hand_failure": primary_failure,
                }
            )

    return {
        "seed": seed,
        "candidate_count": candidate_count,
        "batches_requested": batches,
        "batches_with_winner": len(positions),
        "batches_without_winner": no_winner_count,
        "top_1_recall": _ratio(sum(1 for position in positions if position <= 1), len(positions)),
        "top_5_recall": _ratio(sum(1 for position in positions if position <= 5), len(positions)),
        "top_10_recall": _ratio(sum(1 for position in positions if position <= 10), len(positions)),
        "mean_winner_position": mean(positions) if positions else 0,
        "p95_winner_position": _percentile(positions, 0.95),
        "p99_winner_position": _percentile(positions, 0.99),
        "top1_miss_count": sum(1 for position in positions if position > 1),
        "top5_miss_count": sum(1 for position in positions if position > 5),
        "top10_miss_count": sum(1 for position in positions if position > 10),
        "candidate_type_counts": dict(candidate_type_counts.most_common()),
        "winner_type_counts": dict(winner_type_counts.most_common()),
        "top1_miss_top_type_counts": dict(top1_miss_top_type_counts.most_common()),
        "top1_miss_winner_type_counts": dict(top1_miss_winner_type_counts.most_common()),
        "top1_miss_top_error_counts": dict(top1_miss_top_error_counts.most_common()),
        "top1_miss_primary_failure_counts": dict(top1_miss_primary_failure_counts.most_common()),
        "examples": examples,
    }


def _summarize(configs: list[dict[str, Any]]) -> dict[str, Any]:
    total_winner_batches = sum(int(config["batches_with_winner"]) for config in configs)
    total_top1_hits = sum(
        int(round(float(config["top_1_recall"]) * int(config["batches_with_winner"])))
        for config in configs
    )
    total_top5_hits = sum(
        int(round(float(config["top_5_recall"]) * int(config["batches_with_winner"])))
        for config in configs
    )
    total_top10_hits = sum(
        int(round(float(config["top_10_recall"]) * int(config["batches_with_winner"])))
        for config in configs
    )
    miss_top_types: Counter[str] = Counter()
    miss_winner_types: Counter[str] = Counter()
    miss_errors: Counter[str] = Counter()
    miss_failures: Counter[str] = Counter()
    for config in configs:
        miss_top_types.update(config["top1_miss_top_type_counts"])
        miss_winner_types.update(config["top1_miss_winner_type_counts"])
        miss_errors.update(config["top1_miss_top_error_counts"])
        miss_failures.update(config["top1_miss_primary_failure_counts"])
    return {
        "configs": len(configs),
        "batches_with_winner": total_winner_batches,
        "top_1_recall": _ratio(total_top1_hits, total_winner_batches),
        "top_5_recall": _ratio(total_top5_hits, total_winner_batches),
        "top_10_recall": _ratio(total_top10_hits, total_winner_batches),
        "mean_winner_position_mean": mean(float(config["mean_winner_position"]) for config in configs)
        if configs
        else 0,
        "max_mean_winner_position": max((float(config["mean_winner_position"]) for config in configs), default=0),
        "max_p99_winner_position": max((int(config["p99_winner_position"]) for config in configs), default=0),
        "top1_miss_count": sum(int(config["top1_miss_count"]) for config in configs),
        "top5_miss_count": sum(int(config["top5_miss_count"]) for config in configs),
        "top10_miss_count": sum(int(config["top10_miss_count"]) for config in configs),
        "top1_miss_top_type_counts": dict(miss_top_types.most_common()),
        "top1_miss_winner_type_counts": dict(miss_winner_types.most_common()),
        "top1_miss_top_error_counts": dict(miss_errors.most_common()),
        "top1_miss_primary_failure_counts": dict(miss_failures.most_common()),
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


def _markdown_report(result: dict[str, Any]) -> str:
    summary = result["summary"]
    lines = [
        "# ZenoEnergy Hard-Case Mining Receipt",
        "",
        "```text",
        f"batches_per_config: {result['batches_per_config']}",
        f"seeds: {', '.join(str(seed) for seed in result['seeds'])}",
        f"candidate_counts: {', '.join(str(count) for count in result['candidate_counts'])}",
        f"synthetic_batches_requested: {result['synthetic_batches_requested']}",
        f"synthetic_candidates_requested: {result['synthetic_candidates_requested']}",
        f"model: {result['model']}",
        "```",
        "",
        "| metric | value |",
        "| --- | ---: |",
        f"| batches_with_winner | {summary['batches_with_winner']} |",
        f"| top_1_recall | {_fmt(summary['top_1_recall'])} |",
        f"| top_5_recall | {_fmt(summary['top_5_recall'])} |",
        f"| top_10_recall | {_fmt(summary['top_10_recall'])} |",
        f"| mean_winner_position_mean | {_fmt(summary['mean_winner_position_mean'])} |",
        f"| max_mean_winner_position | {_fmt(summary['max_mean_winner_position'])} |",
        f"| max_p99_winner_position | {summary['max_p99_winner_position']} |",
        f"| top1_miss_count | {summary['top1_miss_count']} |",
        f"| top5_miss_count | {summary['top5_miss_count']} |",
        f"| top10_miss_count | {summary['top10_miss_count']} |",
        "",
        "## Top-1 Misses",
        "",
        "`candidate_type` records generator provenance. The deterministic verifier result",
        "is authoritative; a mutation-family label can still produce a valid candidate in",
        "edge cases.",
        "",
        "Top ranked candidate type on top-1 misses:",
        "",
        _counter_block(summary["top1_miss_top_type_counts"]),
        "Winner type on top-1 misses:",
        "",
        _counter_block(summary["top1_miss_winner_type_counts"]),
        "Top ranked verifier error on top-1 misses:",
        "",
        _counter_block(summary["top1_miss_top_error_counts"]),
        "Primary hand-energy failure on top-1 misses:",
        "",
        _counter_block(summary["top1_miss_primary_failure_counts"]),
        "Per-configuration examples are stored in the JSON receipt.",
    ]
    return "\n".join(lines) + "\n"


def _counter_block(payload: dict[str, int]) -> str:
    if not payload:
        return "```text\nnone\n```\n"
    lines = ["```text"]
    for key, value in payload.items():
        lines.append(f"{key}: {value}")
    lines.append("```")
    lines.append("")
    return "\n".join(lines)


def _ratio(numerator: int, denominator: int) -> float:
    return 0.0 if denominator == 0 else numerator / denominator


def _percentile(values: list[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = min(len(ordered) - 1, int(round((len(ordered) - 1) * fraction)))
    return ordered[index]


def _fmt(value: object) -> str:
    return f"{float(value):.3f}"


if __name__ == "__main__":
    raise SystemExit(main())
