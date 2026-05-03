#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Oracle consumer profile catalog."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_adapter import profile_content_hash  # noqa: E402
from zenodex_oracle_consumer_profiles import (  # noqa: E402
    sample_catalog,
    sample_hash,
    verify_consumer_profile_catalog,
)


def base_catalog() -> dict[str, Any]:
    return sample_catalog()


def _refresh_profile_id(catalog: dict[str, Any], index: int) -> None:
    profile = catalog["profiles"][index]
    profile["profile_id"] = profile_content_hash(profile)


def _mutate(mutator: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    catalog = copy.deepcopy(base_catalog())
    mutator(catalog)
    return catalog


def _profile_mutation(mutator: Callable[[dict[str, Any]], None]) -> Callable[[dict[str, Any]], None]:
    def inner(catalog: dict[str, Any]) -> None:
        mutator(catalog["profiles"][0])
        _refresh_profile_id(catalog, 0)

    return inner


def consumer_profile_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "missing_required_profile_survives",
            _mutate(lambda c: c.__setitem__("profiles", c["profiles"][1:])),
            ["missing_required_profile", "profile_count_mismatch"],
        ),
        (
            "duplicate_profile_key_survives",
            _mutate(lambda c: c["profiles"].__setitem__(1, dict(c["profiles"][0]))),
            ["duplicate_profile_key"],
        ),
        (
            "duplicate_profile_id_survives",
            _mutate(lambda c: c["profiles"][1].__setitem__("profile_id", c["profiles"][0]["profile_id"])),
            ["duplicate_profile_id"],
        ),
        (
            "profile_hash_forgery_survives",
            _mutate(lambda c: c["profiles"][0].__setitem__("max_freshness_window_epochs", c["profiles"][0]["max_freshness_window_epochs"] + 1)),
            ["profile_content_hash_mismatch"],
        ),
        (
            "unsupported_profile_key_survives",
            _mutate(_profile_mutation(lambda p: p.__setitem__("consumer_module", "zenodex.unknown"))),
            ["unsupported_profile_key"],
        ),
        (
            "wrong_query_survives",
            _mutate(_profile_mutation(lambda p: p.__setitem__("query_id", sample_hash("other-query")))),
            ["profile_query_id_mismatch"],
        ),
        (
            "weak_evidence_floor_survives",
            _mutate(_profile_mutation(lambda p: p.__setitem__("required_evidence_floor", "O2"))),
            ["required_evidence_floor_below_critical_minimum", "profile_evidence_floor_below_required"],
        ),
        (
            "loose_freshness_survives",
            _mutate(
                _profile_mutation(
                    lambda p: p.__setitem__("max_freshness_window_epochs", p["max_freshness_window_epochs"] + 1)
                )
            ),
            ["profile_freshness_window_exceeds_required"],
        ),
        (
            "noncritical_profile_survives",
            _mutate(_profile_mutation(lambda p: p.__setitem__("critical", False))),
            ["profile_must_be_critical"],
        ),
        (
            "hidden_profile_field_survives",
            _mutate(_profile_mutation(lambda p: p.__setitem__("admin_override", True))),
            ["unknown_profile_0_field:admin_override"],
        ),
        (
            "wrong_catalog_schema_survives",
            _mutate(lambda c: c.__setitem__("schema", "zenodex.oracle.consumer_profile_catalog.v0")),
            ["catalog_schema_mismatch"],
        ),
        (
            "wrong_profile_schema_survives",
            _mutate(_profile_mutation(lambda p: p.__setitem__("schema", "zenodex.oracle.consumer_profile.v0"))),
            ["profile_schema_mismatch"],
        ),
        (
            "boolean_freshness_survives",
            _mutate(_profile_mutation(lambda p: p.__setitem__("max_freshness_window_epochs", True))),
            ["max_freshness_window_epochs_must_be_int_ge_0"],
        ),
        (
            "hidden_catalog_field_survives",
            _mutate(lambda c: c.__setitem__("admin_override", True)),
            ["unknown_catalog_field:admin_override"],
        ),
    ]


@dataclass(frozen=True)
class ConsumerProfileChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_consumer_profile_chaos() -> dict[str, Any]:
    baseline = verify_consumer_profile_catalog(base_catalog())
    results: list[ConsumerProfileChaosCaseResult] = []
    for name, catalog, expected_fragments in consumer_profile_chaos_cases():
        result = verify_consumer_profile_catalog(catalog)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            ConsumerProfileChaosCaseResult(
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
        "schema": "zenodex.oracle.consumer_profile_catalog_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the consumer profile chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_consumer_profile_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
