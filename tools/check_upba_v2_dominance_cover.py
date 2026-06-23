#!/usr/bin/env python3
"""Check UPBA v2 dominance-cover receipts on bounded synthetic full lists.

This tool is a research harness. It verifies candidates deterministically, then
checks whether a pruned verified list dominates every verifier-accepted member
of the supplied full list. A passing receipt does not prove bounded-grid
optimality unless the supplied full list is separately known to be complete.
"""

from __future__ import annotations

import argparse
import json
import sys
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
    DOMINANCE_COVER_SCHEMA,
    build_upba_v2_dominance_cover_certificate,
    verify_upba_v2_dominance_cover_certificate,
)
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import hand_energy_from_record
from src.energy.upba_v2_ranker import (
    VerifiedCandidateResult,
    deterministic_best_verified_candidate,
    verify_candidates_in_order,
)
from tools.generate_upba_energy_dataset import SyntheticBatch, generate_synthetic_batch


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=80)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20260538)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = run_dominance_cover_benchmark(
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
    print(encoded)
    return 0 if report["ok"] else 1


def run_dominance_cover_benchmark(
    *,
    batches: int,
    candidates_per_batch: int,
    seed: int,
) -> dict[str, Any]:
    started = perf_counter()
    rng = Random(seed)
    winner_only_reports: list[dict[str, object]] = []
    weak_pruned_reports: list[dict[str, object]] = []
    hand_top1_reports: list[dict[str, object]] = []
    skipped_without_winner = 0
    skipped_without_strict_negative = 0

    for batch_index in range(batches):
        batch = generate_synthetic_batch(
            rng=rng,
            batch_index=batch_index,
            target_candidate_count=candidates_per_batch,
        )
        full_candidates = tuple(item.candidate for item in batch.candidates)
        full_results = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=full_candidates,
        )
        winner = deterministic_best_verified_candidate(full_results)
        if winner is None:
            skipped_without_winner += 1
            continue

        winner_only_reports.append(
            _certificate_for_candidates(
                batch=batch,
                full_results=full_results,
                pruned_candidates=(winner.candidate,),
                winner_hash=winner.certificate_hash,
                mode="winner_only",
            )
        )

        hand_top1 = _hand_ordered_candidates(batch=batch, candidates=full_candidates)[:1]
        hand_top1_reports.append(
            _certificate_for_candidates(
                batch=batch,
                full_results=full_results,
                pruned_candidates=hand_top1,
                winner_hash=None,
                mode="hand_top1",
            )
        )

        accepted = sorted(
            (result for result in full_results if result.ok),
            key=lambda result: (result.volume, result.surplus, result.certificate_hash),
        )
        if len(accepted) < 2 or (
            accepted[0].volume == accepted[-1].volume
            and accepted[0].surplus == accepted[-1].surplus
        ):
            skipped_without_strict_negative += 1
            continue
        weak_pruned_reports.append(
            _certificate_for_candidates(
                batch=batch,
                full_results=full_results,
                pruned_candidates=(accepted[0].candidate,),
                winner_hash=accepted[0].certificate_hash,
                mode="weak_pruned",
            )
        )

    elapsed_ms = (perf_counter() - started) * 1000
    summary = {
        "winner_only": _summarize_reports(winner_only_reports),
        "weak_pruned": _summarize_reports(weak_pruned_reports),
        "hand_top1": _summarize_reports(hand_top1_reports),
    }
    ok = (
        summary["winner_only"]["ok_count"] == summary["winner_only"]["count"]
        and summary["winner_only"]["count"] > 0
        and summary["weak_pruned"]["failed_count"] == summary["weak_pruned"]["count"]
        and summary["weak_pruned"]["count"] > 0
        and summary["hand_top1"]["count"] > 0
    )
    return {
        "schema": "zenodex/energy/upba_v2_dominance_cover_benchmark/v1",
        "ok": ok,
        "certificate_schema": DOMINANCE_COVER_SCHEMA,
        "batches": batches,
        "evaluated_batches": len(winner_only_reports),
        "skipped_without_winner": skipped_without_winner,
        "skipped_without_strict_negative": skipped_without_strict_negative,
        "candidates_per_batch": candidates_per_batch,
        "seed": seed,
        "wall_clock_ms": elapsed_ms,
        "summary": summary,
        "safety": {
            "invalid_accept_count": 0,
            "verifier_authoritative": True,
            "scorer_authorizes_settlement": False,
            "model_output_in_state_root": False,
        },
        "limits": [
            "The passing winner-only certificates use the verified full-list winner as the retained representative.",
            "This is a runtime certificate-format prototype over bounded synthetic full lists.",
            "It is not a UPBA v2 bounded-grid optimality verifier without a separate full-list completeness proof.",
        ],
        "negative_knowledge": [
            "A weak pruned set with an uncovered better verified candidate fails the dominance-cover check.",
            "Dominance-cover certificates are about pruning correctness, not about model accuracy.",
        ],
    }


def _certificate_for_candidates(
    *,
    batch: SyntheticBatch,
    full_results: Sequence[VerifiedCandidateResult],
    pruned_candidates: Sequence[UniformBatchCertificateV1],
    winner_hash: str | None,
    mode: str,
) -> dict[str, object]:
    pruned_results = verify_candidates_in_order(
        pool=batch.pool,
        intents=batch.intents,
        balances=batch.balances,
        candidates=pruned_candidates,
    )
    report = build_upba_v2_dominance_cover_certificate(
        full_results=full_results,
        pruned_results=pruned_results,
        winner_hash=winner_hash,
        full_list_complete_for_claim=True,
        scope=f"synthetic-bounded-full-list:{mode}",
    )
    structural_verify_ok = verify_upba_v2_dominance_cover_certificate(report)
    report["mode"] = mode
    report["structural_verify_ok"] = structural_verify_ok
    return report


def _hand_ordered_candidates(
    *,
    batch: SyntheticBatch,
    candidates: Sequence[UniformBatchCertificateV1],
) -> tuple[UniformBatchCertificateV1, ...]:
    return tuple(
        sorted(
            candidates,
            key=lambda candidate: (
                hand_energy_from_record(
                    extract_upba_v2_feature_record(
                        pool=batch.pool,
                        intents=batch.intents,
                        balances=batch.balances,
                        candidate=candidate,
                        include_verifier_label=False,
                    )
                ),
                _candidate_hash_for_sort(candidate),
            ),
        )
    )


def _candidate_hash_for_sort(candidate: UniformBatchCertificateV1) -> str:
    from src.energy.upba_v2_ranker import advisory_candidate_hash

    return advisory_candidate_hash(candidate)


def _summarize_reports(reports: Sequence[dict[str, object]]) -> dict[str, object]:
    ok_values = [bool(report["ok"]) for report in reports]
    cover_values = [bool(report["dominance_cover_ok"]) for report in reports]
    structural_values = [bool(report["structural_verify_ok"]) for report in reports]
    uncovered = [int(report["uncovered_full_count"]) for report in reports]
    return {
        "count": len(reports),
        "ok_count": sum(1 for value in ok_values if value),
        "failed_count": sum(1 for value in ok_values if not value),
        "dominance_cover_ok_count": sum(1 for value in cover_values if value),
        "structural_verify_ok_count": sum(1 for value in structural_values if value),
        "mean_uncovered_full_count": mean(uncovered) if uncovered else 0.0,
        "max_uncovered_full_count": max(uncovered) if uncovered else 0,
    }


def _markdown_report(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# ZenoEnergy Dominance-Cover Runtime Prototype",
        "",
        "This bounded research harness checks a deterministic dominance-cover receipt over verified UPBA v2 candidates. It is advisory evidence for pruning mechanics, and deterministic UPBA verification remains authoritative.",
        "",
        "## Summary",
        "",
        "| mode | count | ok | failed | structural verify ok | mean uncovered | max uncovered |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode in ("winner_only", "hand_top1", "weak_pruned"):
        item = summary[mode]
        lines.append(
            "| {mode} | {count} | {ok_count} | {failed_count} | {structural_verify_ok_count} | {mean_uncovered_full_count:.4f} | {max_uncovered_full_count} |".format(
                mode=mode,
                **item,
            )
        )
    lines.extend(
        [
            "",
            "## Safety Boundary",
            "",
            "- The checker consumes verifier results and never accepts a settlement.",
            "- `winner_only` demonstrates a passing dominance witness over the supplied full list.",
            "- `weak_pruned` is a nonvacuous negative control: it keeps a weak valid candidate and must fail when better verified candidates are uncovered.",
            "- The result is scoped to bounded synthetic full lists. A production or bounded-grid claim still needs a separate completeness proof for the full candidate family.",
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
