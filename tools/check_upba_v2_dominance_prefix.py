#!/usr/bin/env python3
"""Audit ranked prefixes for UPBA v2 dominance-cover certificates.

This research harness measures how many ranked verifier calls are needed before
the accepted prefix has a deterministic dominance-cover certificate over the
verified finite candidate list. It is an offline audit; live early stop still
needs a deterministic unchecked-suffix bound or full fallback.
"""

from __future__ import annotations

import argparse
import json
import sys
from hashlib import sha256
from math import ceil
from pathlib import Path
from random import Random
from statistics import mean
from time import perf_counter
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.uniform_batch_clearing import UniformBatchCertificateV1
from src.energy.upba_v2_dominance_cover import (
    PREFIX_DOMINANCE_COVER_SCHEMA,
    build_upba_v2_prefix_dominance_cover_audit,
    verify_upba_v2_prefix_dominance_cover_audit,
)
from src.energy.upba_v2_energy_model import load_linear_model
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import (
    hand_energy_from_record,
    hard_barrier_energy_from_record,
)
from src.energy.upba_v2_ranker import (
    VerifiedCandidateResult,
    advisory_candidate_hash,
    scorer_from_linear_model,
    verify_candidates_in_order,
)
from tools.generate_upba_energy_dataset import SyntheticBatch, generate_synthetic_batch


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=120)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20260540)
    parser.add_argument(
        "--model",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json"),
    )
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = run_dominance_prefix_benchmark(
        batches=args.batches,
        candidates_per_batch=args.candidates_per_batch,
        seed=args.seed,
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
    return 0 if report.get("ok") is True else 1


def run_dominance_prefix_benchmark(
    *,
    batches: int,
    candidates_per_batch: int,
    seed: int,
    model_path: Path | None,
) -> dict[str, Any]:
    started = perf_counter()
    rng = Random(seed)
    model = load_linear_model(model_path) if model_path is not None and model_path.exists() else None
    mode_reports: dict[str, list[dict[str, object]]] = {
        "exhaustive": [],
        "random": [],
        "hand": [],
        "learned": [],
        "hybrid": [],
    }
    skipped_without_winner = 0

    for batch_index in range(batches):
        batch = generate_synthetic_batch(
            rng=rng,
            batch_index=batch_index,
            target_candidate_count=candidates_per_batch,
        )
        candidates = tuple(item.candidate for item in batch.candidates)
        full_results = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=candidates,
        )
        if not any(result.ok for result in full_results):
            skipped_without_winner += 1
            continue
        for mode, ordered_candidates in _candidate_orders(
            batch=batch,
            candidates=candidates,
            model=model,
            seed=seed,
            batch_index=batch_index,
        ).items():
            ordered_results = verify_candidates_in_order(
                pool=batch.pool,
                intents=batch.intents,
                balances=batch.balances,
                candidates=ordered_candidates,
            )
            audit = build_upba_v2_prefix_dominance_cover_audit(
                full_results=full_results,
                ordered_results=ordered_results,
                full_list_complete_for_claim=True,
                scope=f"synthetic-bounded-prefix:{mode}",
            )
            mode_reports[mode].append(
                {
                    "mode": mode,
                    "ok": audit.get("ok") is True,
                    "structural_verify_ok": verify_upba_v2_prefix_dominance_cover_audit(audit),
                    "prefix_checked_count": int(audit["prefix_checked_count"]),
                    "prefix_valid_count": int(audit["prefix_valid_count"]),
                    "prefix_invalid_count": int(audit["prefix_invalid_count"]),
                    "full_candidate_count": int(audit["full_candidate_count"]),
                    "full_valid_count": int(audit["full_valid_count"]),
                    "permutation_ok": audit.get("permutation_ok") is True,
                    "global_claim_ok": audit.get("global_claim_ok") is True,
                    "certificate_hash": audit["certificate_hash"],
                    "audit_hash": audit["audit_hash"],
                }
            )

    elapsed_ms = (perf_counter() - started) * 1000.0
    summary = {mode: _summarize_reports(reports) for mode, reports in mode_reports.items()}
    required_modes = ("exhaustive", "hand", "learned", "hybrid")
    ok = (
        all(summary[mode]["count"] > 0 for mode in required_modes)
        and all(summary[mode]["ok_count"] == summary[mode]["count"] for mode in required_modes)
        and all(summary[mode]["structural_verify_ok_count"] == summary[mode]["count"] for mode in required_modes)
        and summary["learned"]["mean_prefix_checked_count"] <= summary["hand"]["mean_prefix_checked_count"]
        and summary["hybrid"]["mean_prefix_checked_count"] <= summary["hand"]["mean_prefix_checked_count"]
    )
    return {
        "schema": "zenodex/energy/upba_v2_dominance_prefix_benchmark/v1",
        "ok": ok,
        "audit_schema": PREFIX_DOMINANCE_COVER_SCHEMA,
        "batches": batches,
        "evaluated_batches": summary["exhaustive"]["count"],
        "skipped_without_winner": skipped_without_winner,
        "candidates_per_batch": candidates_per_batch,
        "seed": seed,
        "model_path": str(model_path) if model_path is not None else None,
        "learned_model_present": model is not None,
        "wall_clock_ms": elapsed_ms,
        "summary": summary,
        "safety": {
            "invalid_accept_count": 0,
            "verifier_authoritative": True,
            "scorer_authorizes_settlement": False,
            "model_output_in_state_root": False,
        },
        "limits": [
            "This is an offline prefix audit over bounded synthetic verified finite lists.",
            "A live early stop still needs a verifier-facing unchecked-suffix bound or deterministic full fallback.",
            "Prefix dominance-cover success is equivalent to finding an objective-equivalent verified winner under the current lexicographic objective.",
            "This is not a UPBA v2 bounded-grid optimality verifier without a separate full-list completeness proof.",
        ],
        "negative_knowledge": [
            "Dominance-prefix certificates measure ranked search cost; they do not make model scores authoritative.",
            "If a ranked prefix reaches the full candidate list, the certificate gives no verifier-call savings over full fallback.",
        ],
    }


def _candidate_orders(
    *,
    batch: SyntheticBatch,
    candidates: Sequence[UniformBatchCertificateV1],
    model: object | None,
    seed: int,
    batch_index: int,
) -> dict[str, tuple[UniformBatchCertificateV1, ...]]:
    hand_scores = {
        advisory_candidate_hash(candidate): hand_energy_from_record(
            extract_upba_v2_feature_record(
                pool=batch.pool,
                intents=batch.intents,
                balances=batch.balances,
                candidate=candidate,
                include_verifier_label=False,
            )
        )
        for candidate in candidates
    }
    hard_barrier_scores = {
        advisory_candidate_hash(candidate): hard_barrier_energy_from_record(
            extract_upba_v2_feature_record(
                pool=batch.pool,
                intents=batch.intents,
                balances=batch.balances,
                candidate=candidate,
                include_verifier_label=False,
            )
        )
        for candidate in candidates
    }
    orders: dict[str, tuple[UniformBatchCertificateV1, ...]] = {
        "exhaustive": tuple(candidates),
        "random": tuple(
            sorted(
                candidates,
                key=lambda candidate: _random_order_key(
                    seed=seed,
                    batch_index=batch_index,
                    candidate=candidate,
                ),
            )
        ),
        "hand": tuple(
            sorted(
                candidates,
                key=lambda candidate: (
                    hand_scores[advisory_candidate_hash(candidate)],
                    advisory_candidate_hash(candidate),
                ),
            )
        ),
    }
    if model is None:
        orders["learned"] = orders["exhaustive"]
        orders["hybrid"] = orders["hand"]
        return orders
    scorer = scorer_from_linear_model(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        model=model,
    )
    orders["learned"] = tuple(
        sorted(
            candidates,
            key=lambda candidate: (scorer(candidate), advisory_candidate_hash(candidate)),
        )
    )
    orders["hybrid"] = tuple(
        sorted(
            candidates,
            key=lambda candidate: (
                hard_barrier_scores[advisory_candidate_hash(candidate)],
                scorer(candidate),
                advisory_candidate_hash(candidate),
            ),
        )
    )
    return orders


def _random_order_key(
    *,
    seed: int,
    batch_index: int,
    candidate: UniformBatchCertificateV1,
) -> str:
    digest = sha256(
        f"{seed}:{batch_index}:{advisory_candidate_hash(candidate)}".encode("utf-8")
    ).hexdigest()
    return digest


def _summarize_reports(reports: Sequence[dict[str, object]]) -> dict[str, object]:
    prefix_checked = [int(report["prefix_checked_count"]) for report in reports]
    prefix_valid = [int(report["prefix_valid_count"]) for report in reports]
    prefix_invalid = [int(report["prefix_invalid_count"]) for report in reports]
    full_counts = [int(report["full_candidate_count"]) for report in reports]
    checked_ratios = [
        checked / max(1, full_count)
        for checked, full_count in zip(prefix_checked, full_counts, strict=True)
    ]
    return {
        "count": len(reports),
        "ok_count": sum(1 for report in reports if report.get("ok") is True),
        "failed_count": sum(1 for report in reports if report.get("ok") is not True),
        "structural_verify_ok_count": sum(
            1 for report in reports if report.get("structural_verify_ok") is True
        ),
        "permutation_ok_count": sum(1 for report in reports if report.get("permutation_ok") is True),
        "mean_prefix_checked_count": mean(prefix_checked) if prefix_checked else 0.0,
        "p95_prefix_checked_count": _percentile(prefix_checked, 0.95),
        "p99_prefix_checked_count": _percentile(prefix_checked, 0.99),
        "max_prefix_checked_count": max(prefix_checked) if prefix_checked else 0,
        "mean_prefix_valid_count": mean(prefix_valid) if prefix_valid else 0.0,
        "mean_prefix_invalid_count": mean(prefix_invalid) if prefix_invalid else 0.0,
        "mean_checked_ratio": mean(checked_ratios) if checked_ratios else 0.0,
        "full_fallback_count": sum(
            1
            for checked, full_count in zip(prefix_checked, full_counts, strict=True)
            if checked >= full_count
        ),
    }


def _percentile(values: Sequence[int], q: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, ceil(q * len(ordered)) - 1))
    return float(ordered[index])


def _markdown_report(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# ZenoEnergy Dominance-Prefix Cover",
        "",
        "This offline audit measures how many ranked verifier calls are needed before the accepted prefix has a dominance-cover certificate over the verified finite candidate list.",
        "",
        "## Summary",
        "",
        "| mode | count | ok | mean checked | p95 checked | p99 checked | mean checked ratio | full fallback count |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode in ("exhaustive", "random", "hand", "learned", "hybrid"):
        item = summary[mode]
        lines.append(
            "| {mode} | {count} | {ok_count} | {mean_prefix_checked_count:.4f} | {p95_prefix_checked_count:.0f} | {p99_prefix_checked_count:.0f} | {mean_checked_ratio:.4f} | {full_fallback_count} |".format(
                mode=mode,
                **item,
            )
        )
    lines.extend(
        [
            "",
            "## Safety Boundary",
            "",
            "- The audit consumes deterministic verifier results and never accepts a settlement.",
            "- A passing prefix certificate is a finite-list statement over already verified candidates.",
            "- Live early stop still needs a verifier-facing unchecked-suffix bound or deterministic full fallback.",
            "- A bounded-grid production claim still needs a separate full-list completeness proof.",
            "",
            "## Negative Knowledge",
            "",
        ]
    )
    for item in report["negative_knowledge"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
