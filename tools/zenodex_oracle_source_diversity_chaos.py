#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Oracle source diversity verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_source_diversity import (  # noqa: E402
    sample_source_diversity,
    source_set_content_hash,
    verify_source_diversity,
)


def base_receipt() -> dict[str, Any]:
    return sample_source_diversity()


def _refresh(receipt: dict[str, Any]) -> None:
    receipt["source_set_id"] = source_set_content_hash(receipt)


def _mutate(mutator: Callable[[dict[str, Any]], None], *, refresh: bool = True) -> dict[str, Any]:
    receipt = copy.deepcopy(base_receipt())
    mutator(receipt)
    if refresh:
        _refresh(receipt)
    return receipt


def source_diversity_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "source_set_hash_forgery_survives",
            _mutate(lambda r: r.__setitem__("min_sources", 2), refresh=False),
            ["source_set_content_hash_mismatch:"],
        ),
        (
            "duplicate_source_id_survives",
            _mutate(lambda r: r["sources"][1].__setitem__("source_id", r["sources"][0]["source_id"])),
            ["duplicate_source_id:"],
        ),
        (
            "too_few_sources_survives",
            _mutate(lambda r: r.__setitem__("sources", r["sources"][:2])),
            ["not_enough_sources"],
        ),
        (
            "operator_correlation_survives",
            _mutate(lambda r: r["sources"][1].__setitem__("operator_id", r["sources"][0]["operator_id"])),
            ["not_enough_distinct_operators", "operator_concentration_exceeds_policy"],
        ),
        (
            "venue_correlation_survives",
            _mutate(lambda r: r["sources"][1].__setitem__("venue_id", r["sources"][0]["venue_id"])),
            ["not_enough_distinct_venues", "venue_concentration_exceeds_policy"],
        ),
        (
            "data_family_correlation_survives",
            _mutate(lambda r: r["sources"][1].__setitem__("data_family_id", r["sources"][0]["data_family_id"])),
            ["not_enough_distinct_data_families", "data_family_concentration_exceeds_policy"],
        ),
        (
            "transport_correlation_survives",
            _mutate(lambda r: r["sources"][1].__setitem__("transport_id", r["sources"][0]["transport_id"])),
            ["not_enough_distinct_transports", "transport_concentration_exceeds_policy"],
        ),
        (
            "jurisdiction_correlation_survives",
            _mutate(lambda r: r["sources"][1].__setitem__("jurisdiction_id", r["sources"][0]["jurisdiction_id"])),
            ["not_enough_distinct_jurisdictions", "jurisdiction_concentration_exceeds_policy"],
        ),
        (
            "hidden_top_level_override_survives",
            _mutate(lambda r: r.__setitem__("trusted_override", True)),
            ["unknown_source_diversity_field:trusted_override"],
        ),
        (
            "hidden_source_weight_survives",
            _mutate(lambda r: r["sources"][0].__setitem__("weight_override", 99)),
            ["unknown_source_0_field:weight_override"],
        ),
        (
            "wrong_schema_survives",
            _mutate(lambda r: r.__setitem__("schema", "zenodex.oracle.source_diversity.v0")),
            ["source_diversity_schema_mismatch"],
        ),
        (
            "boolean_min_sources_survives",
            _mutate(lambda r: r.__setitem__("min_sources", True)),
            ["min_sources_must_be_int_between_1_and_64"],
        ),
        (
            "zero_max_same_operator_survives",
            _mutate(lambda r: r.__setitem__("max_same_operator", 0)),
            ["max_same_operator_must_be_int_between_1_and_64"],
        ),
        (
            "bad_operator_token_survives",
            _mutate(lambda r: r["sources"][0].__setitem__("operator_id", "Operator Alpha")),
            ["operator_id_must_be_token"],
        ),
        (
            "sources_as_object_survives",
            _mutate(lambda r: r.__setitem__("sources", {"source_id": "source.fake"})),
            ["sources_must_be_list"],
        ),
        (
            "min_jurisdictions_unmet_survives",
            _mutate(lambda r: r.__setitem__("min_jurisdictions", 4)),
            ["not_enough_distinct_jurisdictions"],
        ),
    ]


@dataclass(frozen=True)
class SourceDiversityChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_source_diversity_chaos() -> dict[str, Any]:
    baseline = verify_source_diversity(base_receipt())
    results: list[SourceDiversityChaosCaseResult] = []
    for name, receipt, expected_fragments in source_diversity_chaos_cases():
        result = verify_source_diversity(receipt)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            SourceDiversityChaosCaseResult(
                name=name,
                expected_reject=True,
                actual_status=result.status,
                expected_error_fragments=expected_fragments,
                actual_errors=actual_errors,
                passed=passed,
            )
        )

    failures = [case for case in results if not case.passed]
    return {
        "schema": "zenodex.oracle.source_diversity_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the source diversity chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_source_diversity_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
