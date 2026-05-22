#!/usr/bin/env python3
"""Audit bounded synthetic UPBA v2 candidate coverage for ZenoEnergy."""

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

from tools.generate_upba_energy_dataset import generate_synthetic_batch, rows_for_batch
from tools.operator_report_output import emit_operator_json


EXPECTED_MUTATION_TYPES = {
    "invalid_limit_price",
    "invalid_negative_reserve",
    "invalid_noncanonical_fill_vector",
    "invalid_all_zero",
    "invalid_balance",
    "near_miss_adversarial",
    "hard_attractive_output_mismatch",
    "hard_unreduced_price",
    "hard_schema_policy_mismatch",
    "random_noisy",
}

HARD_NEGATIVE_TYPES = {
    "near_miss_adversarial",
    "hard_attractive_output_mismatch",
    "hard_unreduced_price",
    "hard_schema_policy_mismatch",
}

LIVE_SECRET_KEYS = {
    "private_key",
    "secret",
    "seed_phrase",
    "mnemonic",
    "sender_pubkey",
    "sender",
    "balance_table",
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=100)
    parser.add_argument("--candidates-per-batch", type=int, default=32)
    parser.add_argument("--seed", type=int, default=20260540)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = audit_synthetic_candidate_coverage(
        batches=args.batches,
        candidates_per_batch=args.candidates_per_batch,
        seed=args.seed,
    )
    encoded = json.dumps(report, indent=2, sort_keys=True)
    if args.output_json is not None:
        args.output_json.parent.mkdir(parents=True, exist_ok=True)
        args.output_json.write_text(encoded + "\n", encoding="utf-8")
    if args.output_markdown is not None:
        args.output_markdown.parent.mkdir(parents=True, exist_ok=True)
        args.output_markdown.write_text(_markdown_report(report), encoding="utf-8")
    emit_operator_json(report)
    return 0 if bool(report["coverage_ok"]) else 1


def audit_synthetic_candidate_coverage(
    *,
    batches: int,
    candidates_per_batch: int,
    seed: int,
) -> dict[str, Any]:
    if batches <= 0:
        raise ValueError("batches must be positive")
    if candidates_per_batch <= 1:
        raise ValueError("candidates_per_batch must be greater than one")

    rng = Random(seed)
    candidate_type_counts: Counter[str] = Counter()
    verifier_error_counts: Counter[str] = Counter()
    feature_dim_counts: Counter[int] = Counter()
    set_feature_dim_counts: Counter[int] = Counter()
    set_aware_feature_dim_counts: Counter[int] = Counter()
    source_counts: Counter[str] = Counter()
    missing_mutation_by_batch: Counter[str] = Counter()
    duplicate_hash_batches = 0
    live_secret_key_hits: Counter[str] = Counter()
    candidate_counts: list[int] = []
    valid_candidate_count = 0
    invalid_candidate_count = 0
    winner_batch_count = 0
    all_negative_batch_count = 0
    hard_negative_count = 0

    for batch_index in range(batches):
        batch = generate_synthetic_batch(
            rng=rng,
            batch_index=batch_index,
            target_candidate_count=candidates_per_batch,
        )
        rows = rows_for_batch(batch)
        candidate_counts.append(len(rows))
        batch_hashes = [str(row["candidate_hash"]) for row in rows]
        if len(batch_hashes) != len(set(batch_hashes)):
            duplicate_hash_batches += 1

        batch_types = {str(row["candidate_type"]) for row in rows}
        for missing in sorted(EXPECTED_MUTATION_TYPES - batch_types):
            missing_mutation_by_batch[missing] += 1

        winner_seen = False
        valid_seen = False
        for row in rows:
            candidate_type = str(row["candidate_type"])
            label = row["label"]
            if not isinstance(label, dict):
                raise TypeError("dataset row label must be an object")
            candidate_type_counts[candidate_type] += 1
            source_counts[str(row.get("source", ""))] += 1
            feature_dim_counts[len(row["features"])] += 1  # type: ignore[arg-type]
            set_feature_dim_counts[len(row["set_features"])] += 1  # type: ignore[arg-type]
            set_aware_feature_dim_counts[len(row["set_aware_features"])] += 1  # type: ignore[arg-type]
            for key in LIVE_SECRET_KEYS:
                if _contains_key(row, key):
                    live_secret_key_hits[key] += 1

            if candidate_type in HARD_NEGATIVE_TYPES:
                hard_negative_count += 1
            if bool(label["valid"]):
                valid_candidate_count += 1
                valid_seen = True
            else:
                invalid_candidate_count += 1
                verifier_error_counts[str(label["verifier_error"])] += 1
            if bool(label["is_winner"]):
                winner_seen = True
        if winner_seen:
            winner_batch_count += 1
        if not valid_seen:
            all_negative_batch_count += 1

    observed_types = set(candidate_type_counts)
    missing_required_types = sorted(EXPECTED_MUTATION_TYPES - observed_types)
    hard_negative_missing = sorted(HARD_NEGATIVE_TYPES - observed_types)
    synthetic_only = set(source_counts) == {"synthetic"}
    winner_batch_rate = winner_batch_count / batches
    hard_negative_rate = hard_negative_count / max(1, sum(candidate_counts))
    coverage_ok = (
        not missing_required_types
        and not hard_negative_missing
        and not live_secret_key_hits
        and synthetic_only
        and duplicate_hash_batches == 0
        and candidate_counts
        and min(candidate_counts) >= max(1, candidates_per_batch - 2)
        and winner_batch_rate >= 0.90
        and invalid_candidate_count > valid_candidate_count
        and hard_negative_rate >= 0.10
        and set(feature_dim_counts) == {96}
        and set(set_feature_dim_counts) == {51}
        and set(set_aware_feature_dim_counts) == {147}
    )
    return {
        "schema": "zenodex/energy/upba_v2_synthetic_candidate_coverage/v1",
        "source": "synthetic",
        "seed": seed,
        "batches": batches,
        "candidates_per_batch": candidates_per_batch,
        "synthetic_batches_requested": batches,
        "synthetic_candidates_requested": batches * candidates_per_batch,
        "candidate_count_total": sum(candidate_counts),
        "candidate_count_min": min(candidate_counts),
        "candidate_count_mean": mean(candidate_counts),
        "candidate_count_max": max(candidate_counts),
        "dedup_loss_count": batches * candidates_per_batch - sum(candidate_counts),
        "candidate_type_counts": dict(sorted(candidate_type_counts.items())),
        "verifier_error_counts": dict(sorted(verifier_error_counts.items())),
        "observed_candidate_types": sorted(observed_types),
        "missing_required_candidate_types": missing_required_types,
        "hard_negative_missing_types": hard_negative_missing,
        "hard_negative_count": hard_negative_count,
        "hard_negative_rate": hard_negative_rate,
        "valid_candidate_count": valid_candidate_count,
        "invalid_candidate_count": invalid_candidate_count,
        "winner_batch_count": winner_batch_count,
        "winner_batch_rate": winner_batch_rate,
        "all_negative_batch_count": all_negative_batch_count,
        "duplicate_hash_batches": duplicate_hash_batches,
        "source_counts": dict(sorted(source_counts.items())),
        "synthetic_only": synthetic_only,
        "live_secret_key_hits": dict(sorted(live_secret_key_hits.items())),
        "feature_dim_counts": {str(k): v for k, v in sorted(feature_dim_counts.items())},
        "set_feature_dim_counts": {
            str(k): v for k, v in sorted(set_feature_dim_counts.items())
        },
        "set_aware_feature_dim_counts": {
            str(k): v for k, v in sorted(set_aware_feature_dim_counts.items())
        },
        "missing_mutation_by_batch": dict(sorted(missing_mutation_by_batch.items())),
        "coverage_ok": bool(coverage_ok),
        "interpretation": {
            "synthetic_boundary": (
                "Rows are generated from fixed seeded synthetic pools, intents, balances, "
                "and candidate mutations; this is distributional coverage evidence, not live-order evidence."
            ),
            "real_data_promotion_requirement": (
                "A production-shadow audit should rerun the same coverage checks on real candidate "
                "distributions after removing user identifiers and secrets."
            ),
        },
    }


def _contains_key(value: object, key: str) -> bool:
    if isinstance(value, dict):
        return any(
            str(child_key) == key or _contains_key(child_value, key)
            for child_key, child_value in value.items()
        )
    if isinstance(value, list | tuple):
        return any(_contains_key(item, key) for item in value)
    return False


def _markdown_report(report: dict[str, Any]) -> str:
    lines = [
        "# ZenoEnergy Synthetic Candidate Coverage",
        "",
        "```text",
        f"coverage_ok: {str(report['coverage_ok']).lower()}",
        f"seed: {report['seed']}",
        f"batches: {report['batches']}",
        f"candidate_count_total: {report['candidate_count_total']}",
        f"winner_batch_rate: {float(report['winner_batch_rate']):.4f}",
        f"hard_negative_rate: {float(report['hard_negative_rate']):.4f}",
        f"synthetic_only: {str(report['synthetic_only']).lower()}",
        f"duplicate_hash_batches: {report['duplicate_hash_batches']}",
        "```",
        "",
        "## Candidate Types",
        "",
        "| type | count |",
        "| --- | ---: |",
    ]
    for name, count in report["candidate_type_counts"].items():
        lines.append(f"| {name} | {count} |")
    lines.extend(["", "## Verifier Errors", "", "| error | count |", "| --- | ---: |"])
    for name, count in report["verifier_error_counts"].items():
        lines.append(f"| {name} | {count} |")
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            str(report["interpretation"]["synthetic_boundary"]),
            "",
            str(report["interpretation"]["real_data_promotion_requirement"]),
            "",
        ]
    )
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
