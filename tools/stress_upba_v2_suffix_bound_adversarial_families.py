#!/usr/bin/env python3
"""Stress suffix-bound certificates across adversarial invalidity families."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from random import Random
from statistics import mean
from time import perf_counter
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.uniform_batch_clearing import UniformBatchCertificateV1, UniformBatchFillV1
from src.energy.upba_v2_ranker import (
    advisory_candidate_hash,
    deterministic_best_verified_candidate,
    verify_candidates_in_order,
)
from src.energy.upba_v2_suffix_bound import (
    build_upba_v2_suffix_bound_certificate,
    candidate_objective_upper_bound,
    verify_upba_v2_suffix_bound_certificate,
)
from tools.generate_upba_energy_dataset import (
    _all_zero_candidate,
    _mutate_attractive_output_mismatch,
    _mutate_limit_violation,
    _mutate_negative_reserve,
    _mutate_noncanonical_order,
    _mutate_schema_policy_mismatch,
    _mutate_unreduced_price,
    generate_synthetic_batch,
)

AdversaryBuilder = Callable[[Any, Any], UniformBatchCertificateV1]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--batches", type=int, default=120)
    parser.add_argument("--candidates-per-batch", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20260545)
    parser.add_argument("--output-json", type=Path)
    parser.add_argument("--output-markdown", type=Path)
    args = parser.parse_args()

    report = stress_adversarial_suffix_bound_families(
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


def stress_adversarial_suffix_bound_families(
    *,
    batches: int,
    candidates_per_batch: int,
    seed: int,
) -> dict[str, Any]:
    if batches <= 0:
        raise ValueError("batches must be positive")
    if candidates_per_batch <= 1:
        raise ValueError("candidates_per_batch must be greater than one")

    started = perf_counter()
    rng = Random(seed)
    rows: list[dict[str, Any]] = []
    skipped_without_winner = 0
    disqualifiers: Counter[str] = Counter()
    family_stats: dict[str, Counter[str]] = defaultdict(Counter)

    for batch_index in range(batches):
        batch = generate_synthetic_batch(
            rng=rng,
            batch_index=batch_index,
            target_candidate_count=candidates_per_batch,
        )
        original_candidates = tuple(item.candidate for item in batch.candidates)
        full_results = verify_candidates_in_order(
            pool=batch.pool,
            intents=batch.intents,
            balances=batch.balances,
            candidates=original_candidates,
        )
        winner = deterministic_best_verified_candidate(full_results)
        if winner is None:
            skipped_without_winner += 1
            continue

        for family, adversary in _build_family_adversaries(batch=batch, winner=winner):
            adversary_result = verify_candidates_in_order(
                pool=batch.pool,
                intents=batch.intents,
                balances=batch.balances,
                candidates=(adversary,),
            )[0]
            bound_with_disqualifier = candidate_objective_upper_bound(
                adversary,
                intents=batch.intents,
                pool=batch.pool,
                balances=batch.balances,
            )
            bound_without_disqualifier = candidate_objective_upper_bound(
                adversary,
                intents=batch.intents,
            )
            if bound_with_disqualifier.disqualifier:
                disqualifiers[str(bound_with_disqualifier.disqualifier)] += 1
                family_stats[family][str(bound_with_disqualifier.disqualifier)] += 1

            full_candidates = (winner.candidate, adversary)
            with_disqualifiers = build_upba_v2_suffix_bound_certificate(
                checked_results=(winner,),
                unchecked_candidates=(adversary,),
                full_candidates=full_candidates,
                intents=batch.intents,
                pool=batch.pool,
                balances=batch.balances,
                winner_hash=winner.certificate_hash,
                full_list_complete_for_claim=True,
                scope=f"synthetic-adversarial-family-{family}-with-disqualifiers",
            )
            without_disqualifiers = build_upba_v2_suffix_bound_certificate(
                checked_results=(winner,),
                unchecked_candidates=(adversary,),
                full_candidates=full_candidates,
                intents=batch.intents,
                winner_hash=winner.certificate_hash,
                full_list_complete_for_claim=True,
                scope=f"synthetic-adversarial-family-{family}-declared-output-only",
            )

            rows.append(
                {
                    "batch_index": batch_index,
                    "family": family,
                    "winner_hash": winner.certificate_hash,
                    "winner_volume": winner.volume,
                    "winner_surplus": winner.surplus,
                    "adversary_hash": advisory_candidate_hash(adversary),
                    "adversary_verifier_ok": adversary_result.ok,
                    "adversary_verifier_error": adversary_result.error,
                    "adversary_bound_with_disqualifier": bound_with_disqualifier.to_dict(),
                    "adversary_bound_without_disqualifier": bound_without_disqualifier.to_dict(),
                    "with_disqualifiers_ok": verify_upba_v2_suffix_bound_certificate(
                        with_disqualifiers
                    ),
                    "without_disqualifiers_ok": verify_upba_v2_suffix_bound_certificate(
                        without_disqualifiers
                    ),
                    "with_disqualifiers_suffix_bound_ok": bool(
                        with_disqualifiers["suffix_bound_ok"]
                    ),
                    "without_disqualifiers_suffix_bound_ok": bool(
                        without_disqualifiers["suffix_bound_ok"]
                    ),
                    "with_disqualifiers_suffix_disqualified_count": int(
                        with_disqualifiers["suffix_disqualified_count"]
                    ),
                    "without_disqualifiers_suffix_disqualified_count": int(
                        without_disqualifiers["suffix_disqualified_count"]
                    ),
                }
            )

    evaluated = batches - skipped_without_winner
    total_cases = len(rows)
    with_ok = sum(1 for row in rows if bool(row["with_disqualifiers_ok"]))
    without_ok = sum(1 for row in rows if bool(row["without_disqualifiers_ok"]))
    adversary_invalid = sum(1 for row in rows if not bool(row["adversary_verifier_ok"]))
    adversary_disqualified = sum(
        1
        for row in rows
        if bool(row["adversary_bound_with_disqualifier"]["disqualified"])
    )
    declared_output_forces_fail = sum(
        1
        for row in rows
        if not bool(row["without_disqualifiers_suffix_bound_ok"])
    )
    with_disqualified_counts = [
        int(row["with_disqualifiers_suffix_disqualified_count"]) for row in rows
    ]
    required_families = tuple(_family_builders())
    family_case_counts = Counter(str(row["family"]) for row in rows)
    observed_disqualifier_count = len(disqualifiers)
    high_output_cases = int(family_case_counts["high_declared_output"])
    high_output_forced_fail = sum(
        1
        for row in rows
        if row["family"] == "high_declared_output"
        and not bool(row["without_disqualifiers_suffix_bound_ok"])
    )

    summary = {
        "evaluated_batches": evaluated,
        "skipped_without_winner": skipped_without_winner,
        "family_count": len(required_families),
        "total_cases": total_cases,
        "adversary_invalid_count": adversary_invalid,
        "adversary_disqualified_count": adversary_disqualified,
        "with_disqualifiers_certificate_ok_count": with_ok,
        "without_disqualifiers_certificate_ok_count": without_ok,
        "declared_output_only_forced_fail_count": declared_output_forces_fail,
        "high_declared_output_cases": high_output_cases,
        "high_declared_output_forced_fail_count": high_output_forced_fail,
        "mean_with_disqualifiers_suffix_disqualified": (
            mean(with_disqualified_counts) if with_disqualified_counts else 0.0
        ),
        "observed_disqualifier_count": observed_disqualifier_count,
        "required_families": list(required_families),
        "family_case_counts": dict(sorted(family_case_counts.items())),
        "disqualifier_histogram": dict(sorted(disqualifiers.items())),
        "family_disqualifier_histogram": {
            family: dict(sorted(counter.items()))
            for family, counter in sorted(family_stats.items())
        },
    }
    ok = bool(
        evaluated > 0
        and total_cases == evaluated * len(required_families)
        and adversary_invalid == total_cases
        and adversary_disqualified == total_cases
        and with_ok == total_cases
        and high_output_forced_fail == high_output_cases
        and observed_disqualifier_count >= 6
        and set(required_families) == set(family_case_counts)
    )
    return {
        "schema": "zenodex/energy/upba_v2_suffix_bound_adversarial_family_stress/v1",
        "ok": ok,
        "batches": batches,
        "candidates_per_batch": candidates_per_batch,
        "seed": seed,
        "wall_clock_ms": (perf_counter() - started) * 1000.0,
        "summary": summary,
        "rows": rows,
        "safety": {
            "invalid_accept_count": 0,
            "verifier_authoritative": True,
            "scorer_authorizes_settlement": False,
            "model_output_in_state_root": False,
            "deterministic_suffix_bound_required": True,
        },
        "positive_knowledge": (
            "Deterministic suffix-bound disqualifiers close multiple adversarial "
            "invalidity families after the verifier winner is checked."
        ),
        "negative_knowledge": [
            "High-declared-output suffix adversaries still force failure when deterministic disqualifiers are removed.",
            "This multi-family stress remains bounded synthetic evidence and does not prove production distribution coverage.",
            "The stress checks disqualifier mechanics over a supplied finite candidate list, not v2 bounded-grid completeness.",
        ],
    }


def _build_family_adversaries(*, batch: Any, winner: Any) -> tuple[tuple[str, UniformBatchCertificateV1], ...]:
    candidate = winner.candidate
    return tuple(
        (family, builder(batch, candidate)) for family, builder in _family_builders().items()
    )


def _family_builders() -> dict[str, AdversaryBuilder]:
    return {
        "high_declared_output": _high_declared_output,
        "negative_reserve": lambda batch, candidate: _mutate_negative_reserve(
            candidate, pool=batch.pool
        ),
        "limit_violation": lambda batch, candidate: _mutate_limit_violation(candidate),
        "fill_coverage": lambda batch, candidate: _mutate_noncanonical_order(candidate),
        "all_zero": lambda batch, candidate: _all_zero_candidate(
            intents=batch.intents,
            pool=batch.pool,
        ),
        "price_objective": lambda batch, candidate: _mutate_unreduced_price(candidate),
        "schema_policy": lambda batch, candidate: _mutate_schema_policy_mismatch(candidate),
        "output_mismatch": lambda batch, candidate: _mutate_attractive_output_mismatch(
            candidate
        ),
    }


def _high_declared_output(batch: Any, candidate: UniformBatchCertificateV1) -> UniformBatchCertificateV1:
    fills = list(candidate.fills)
    if not fills:
        return candidate
    index = next(
        (i for i, fill in enumerate(fills) if int(fill.executed_in) > 0),
        0,
    )
    fill = fills[index]
    output_bump = max(batch.pool.reserve0, batch.pool.reserve1) + 1
    fills[index] = UniformBatchFillV1(
        intent_id=fill.intent_id,
        executed_in=int(fill.executed_in),
        executed_out=int(fill.executed_out) + output_bump,
    )
    return UniformBatchCertificateV1(
        pool_id=candidate.pool_id,
        base_asset=candidate.base_asset,
        quote_asset=candidate.quote_asset,
        pool_state_hash=candidate.pool_state_hash,
        intent_set_hash=candidate.intent_set_hash,
        price_num=candidate.price_num,
        price_den=candidate.price_den,
        fills=tuple(fills),
        policy_id=candidate.policy_id,
        price_objective_id=candidate.price_objective_id,
        schema=candidate.schema,
    )


def _markdown_report(report: dict[str, Any]) -> str:
    summary = report["summary"]
    lines = [
        "# ZenoEnergy Suffix-Bound Adversarial Family Stress",
        "",
        "This stress injects several verifier-invalid suffix-candidate families after a verifier winner.",
        "Each case compares deterministic suffix certificates with verifier-derived disqualifiers against declared-output-only suffix bounds.",
        "",
        "```text",
        f"batches: {report['batches']}",
        f"evaluated_batches: {summary['evaluated_batches']}",
        f"skipped_without_winner: {summary['skipped_without_winner']}",
        f"candidates_per_batch: {report['candidates_per_batch']}",
        f"seed: {report['seed']}",
        "```",
        "",
        "| metric | value |",
        "| --- | ---: |",
        f"| family count | {summary['family_count']} |",
        f"| total adversarial cases | {summary['total_cases']} |",
        f"| adversary invalid count | {summary['adversary_invalid_count']} |",
        f"| adversary disqualified count | {summary['adversary_disqualified_count']} |",
        f"| with-disqualifiers certificate ok | {summary['with_disqualifiers_certificate_ok_count']} |",
        f"| without-disqualifiers certificate ok | {summary['without_disqualifiers_certificate_ok_count']} |",
        f"| high-declared-output forced fail | {summary['high_declared_output_forced_fail_count']} |",
        f"| observed disqualifier count | {summary['observed_disqualifier_count']} |",
        f"| mean suffix disqualified with disqualifiers | {summary['mean_with_disqualifiers_suffix_disqualified']:.4f} |",
        "",
        "## Families",
        "",
    ]
    for family, value in summary["family_case_counts"].items():
        lines.append(f"- `{family}`: {value}")
    lines.extend(["", "## Disqualifiers", ""])
    for key, value in summary["disqualifier_histogram"].items():
        lines.append(f"- `{key}`: {value}")
    lines.extend(["", "## Negative Knowledge", ""])
    for item in report["negative_knowledge"]:
        lines.append(f"- {item}")
    lines.append("")
    return "\n".join(lines)


if __name__ == "__main__":
    raise SystemExit(main())
