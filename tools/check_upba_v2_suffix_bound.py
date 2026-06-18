#!/usr/bin/env python3
"""Benchmark deterministic UPBA v2 suffix-bound early stop certificates."""

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
from src.energy.upba_v2_energy_model import load_linear_model
from src.energy.upba_v2_features import extract_upba_v2_feature_record
from src.energy.upba_v2_hand_energy import (
    hand_energy_from_record,
    hard_barrier_energy_from_record,
)
from src.energy.upba_v2_ranker import (
    VerifiedCandidateResult,
    advisory_candidate_hash,
    calls_until_objective_equivalent_winner,
    deterministic_best_verified_candidate,
    objective_equivalent_verified_results,
    scorer_from_linear_model,
    verify_candidates_in_order,
)
from src.energy.upba_v2_suffix_bound import (
    SUFFIX_BOUND_SCHEMA,
    build_upba_v2_suffix_bound_certificate,
    verify_upba_v2_suffix_bound_certificate,
)
from tools.generate_upba_energy_dataset import SyntheticBatch, generate_synthetic_batch


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=120)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20260541)
    parser.add_argument(
        "--model",
        type=Path,
        default=Path("data/upba_energy/upba_v2_energy_linear_gap_weighted_seed20260517.json"),
    )
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = run_suffix_bound_benchmark(
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
    return 0 if report["ok"] else 1


def run_suffix_bound_benchmark(
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
        full_winner = deterministic_best_verified_candidate(full_results)
        if full_winner is None:
            skipped_without_winner += 1
            continue

        orders = _candidate_orders(
            batch=batch,
            candidates=candidates,
            model=model,
            seed=seed,
            batch_index=batch_index,
        )
        for mode, ordered_candidates in orders.items():
            mode_reports[mode].append(
                _simulate_suffix_bound_stop(
                    batch=batch,
                    full_candidates=candidates,
                    ordered_candidates=ordered_candidates,
                    full_winner=full_winner,
                )
            )

    elapsed_ms = (perf_counter() - started) * 1000.0
    summary = {mode: _summarize_reports(reports) for mode, reports in mode_reports.items()}
    required_modes = ("exhaustive", "hand", "learned", "hybrid")
    ok = (
        all(summary[mode]["count"] > 0 for mode in required_modes)
        and all(summary[mode]["invalid_accept_count"] == 0 for mode in required_modes)
        and all(summary[mode]["objective_equiv_accept_count"] == summary[mode]["count"] for mode in required_modes)
        and summary["learned"]["mean_verifier_calls"] <= summary["hand"]["mean_verifier_calls"]
        and summary["hybrid"]["mean_verifier_calls"] <= summary["hand"]["mean_verifier_calls"]
    )
    return {
        "schema": "zenodex/energy/upba_v2_suffix_bound_benchmark/v1",
        "ok": ok,
        "certificate_schema": SUFFIX_BOUND_SCHEMA,
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
            "deterministic_suffix_bound_required": True,
        },
        "limits": [
            "This benchmark uses bounded synthetic finite candidate lists.",
            "The suffix bound is deterministic, but a production bounded-grid claim still needs candidate-family coverage.",
            "Attractive invalid unchecked candidates can force more verifier calls because their declared outputs remain upper bounds until checked.",
        ],
    }


def _simulate_suffix_bound_stop(
    *,
    batch: SyntheticBatch,
    full_candidates: Sequence[UniformBatchCertificateV1],
    ordered_candidates: Sequence[UniformBatchCertificateV1],
    full_winner: VerifiedCandidateResult,
) -> dict[str, object]:
    checked_results: list[VerifiedCandidateResult] = []
    final_certificate: dict[str, object] | None = None
    stopped_by_suffix_bound = False

    for index, candidate in enumerate(ordered_candidates, start=1):
        result = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=(candidate,),
        )[0]
        checked_results.append(result)
        current_winner = deterministic_best_verified_candidate(checked_results)
        if current_winner is None:
            continue
        unchecked = tuple(ordered_candidates[index:])
        certificate = build_upba_v2_suffix_bound_certificate(
            checked_results=tuple(checked_results),
            unchecked_candidates=unchecked,
            full_candidates=tuple(full_candidates),
            intents=batch.intents,
            pool=batch.pool,
            balances=batch.balances,
            winner_hash=current_winner.certificate_hash,
            full_list_complete_for_claim=True,
            scope="synthetic-bounded-suffix-stop",
        )
        if verify_upba_v2_suffix_bound_certificate(certificate):
            final_certificate = certificate
            stopped_by_suffix_bound = index < len(ordered_candidates)
            break

    if final_certificate is None:
        current_winner = deterministic_best_verified_candidate(checked_results)
        if current_winner is not None:
            final_certificate = build_upba_v2_suffix_bound_certificate(
                checked_results=tuple(checked_results),
                unchecked_candidates=(),
                full_candidates=tuple(full_candidates),
                intents=batch.intents,
                pool=batch.pool,
                balances=batch.balances,
                winner_hash=current_winner.certificate_hash,
                full_list_complete_for_claim=True,
                scope="synthetic-bounded-full-fallback",
            )

    accepted = deterministic_best_verified_candidate(checked_results)
    accepted_equiv = bool(
        accepted is not None and objective_equivalent_verified_results(accepted, full_winner)
    )
    calls_to_objective_winner = (
        calls_until_objective_equivalent_winner(
            ordered_results=tuple(checked_results),
            winner=full_winner,
        )
        if accepted_equiv
        else len(checked_results)
    )
    return {
        "verifier_calls": len(checked_results),
        "full_candidate_count": len(full_candidates),
        "stopped_by_suffix_bound": stopped_by_suffix_bound,
        "full_fallback": len(checked_results) >= len(full_candidates),
        "accepted_objective_equiv": accepted_equiv,
        "accepted_hash": accepted.certificate_hash if accepted is not None else None,
        "full_winner_hash": full_winner.certificate_hash,
        "calls_to_objective_winner": calls_to_objective_winner,
        "certificate_ok": final_certificate is not None and final_certificate.get("ok") is True,
        "certificate_hash": final_certificate.get("certificate_hash") if final_certificate else None,
        "max_suffix_volume_upper": final_certificate.get("max_suffix_volume_upper") if final_certificate else None,
        "suffix_disqualified_count": final_certificate.get("suffix_disqualified_count") if final_certificate else 0,
        "invalid_accept_count": 0,
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
    return sha256(f"{seed}:{batch_index}:{advisory_candidate_hash(candidate)}".encode("utf-8")).hexdigest()


def _summarize_reports(reports: Sequence[dict[str, object]]) -> dict[str, object]:
    calls = [int(report["verifier_calls"]) for report in reports]
    full_counts = [int(report["full_candidate_count"]) for report in reports]
    disqualified = [int(report["suffix_disqualified_count"]) for report in reports]
    checked_ratios = [
        checked / max(1, full_count)
        for checked, full_count in zip(calls, full_counts, strict=True)
    ]
    return {
        "count": len(reports),
        "certificate_ok_count": sum(1 for report in reports if bool(report["certificate_ok"])),
        "objective_equiv_accept_count": sum(
            1 for report in reports if bool(report["accepted_objective_equiv"])
        ),
        "stopped_by_suffix_bound_count": sum(
            1 for report in reports if bool(report["stopped_by_suffix_bound"])
        ),
        "full_fallback_count": sum(1 for report in reports if bool(report["full_fallback"])),
        "mean_verifier_calls": mean(calls) if calls else 0.0,
        "p95_verifier_calls": _percentile(calls, 0.95),
        "p99_verifier_calls": _percentile(calls, 0.99),
        "max_verifier_calls": max(calls) if calls else 0,
        "mean_checked_ratio": mean(checked_ratios) if checked_ratios else 0.0,
        "mean_suffix_disqualified_count": mean(disqualified) if disqualified else 0.0,
        "invalid_accept_count": sum(int(report["invalid_accept_count"]) for report in reports),
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
        "# ZenoEnergy Suffix-Bound Early Stop",
        "",
        "This benchmark checks a deterministic early-stop certificate: a verifier-checked winner must dominate the checked prefix, and every unchecked candidate must have a declared objective upper bound no better than that winner.",
        "",
        "## Summary",
        "",
        "| mode | count | objective-equiv accepts | suffix stops | full fallback | mean calls | p95 | p99 | mean checked ratio | mean suffix disqualified |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for mode in ("exhaustive", "random", "hand", "learned", "hybrid"):
        item = summary[mode]
        lines.append(
            "| {mode} | {count} | {objective_equiv_accept_count} | {stopped_by_suffix_bound_count} | {full_fallback_count} | {mean_verifier_calls:.4f} | {p95_verifier_calls:.0f} | {p99_verifier_calls:.0f} | {mean_checked_ratio:.4f} | {mean_suffix_disqualified_count:.4f} |".format(
                mode=mode,
                **item,
            )
        )
    lines.extend(
        [
            "",
            "## Safety Boundary",
            "",
            "- The scorer only orders candidates.",
            "- The accepted candidate is verifier-checked.",
            "- The stop condition is a deterministic suffix-bound certificate.",
            "- Candidate-family coverage is still required for production bounded-grid claims.",
            "",
            "## Limits",
            "",
        ]
    )
    for item in report["limits"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
