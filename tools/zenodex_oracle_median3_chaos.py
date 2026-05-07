#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Zeno Oracle median_3 verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_median3 import (  # noqa: E402
    content_hash,
    sample_aggregate,
    sample_hash,
    verify_median3_aggregate,
)
from zenodex_oracle_source_diversity import source_set_content_hash  # noqa: E402


def base_aggregate() -> dict[str, Any]:
    return sample_aggregate()


def _refresh_report_id(aggregate: dict[str, Any], index: int) -> None:
    report = aggregate["reports"][index]
    report["report_id"] = content_hash(report, omit_key="report_id")


def _refresh_aggregate_id(aggregate: dict[str, Any]) -> None:
    aggregate["aggregate_id"] = content_hash(aggregate, omit_key="aggregate_id")


def _refresh_source_diversity_id(aggregate: dict[str, Any]) -> None:
    aggregate["source_diversity"]["source_set_id"] = source_set_content_hash(aggregate["source_diversity"])


def _mutate(mutator: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    aggregate = copy.deepcopy(base_aggregate())
    mutator(aggregate)
    return aggregate


def _refreshing(mutator: Callable[[dict[str, Any]], None]) -> Callable[[dict[str, Any]], None]:
    def inner(aggregate: dict[str, Any]) -> None:
        mutator(aggregate)
        _refresh_aggregate_id(aggregate)

    return inner


def _wrong_report_query(aggregate: dict[str, Any]) -> None:
    aggregate["reports"][1]["query_id"] = sample_hash("other-query")
    _refresh_report_id(aggregate, 1)
    _refresh_aggregate_id(aggregate)


def _future_report(aggregate: dict[str, Any]) -> None:
    aggregate["reports"][0]["observed_epoch"] = aggregate["current_epoch"] + 1
    _refresh_report_id(aggregate, 0)
    _refresh_aggregate_id(aggregate)


def _stale_report(aggregate: dict[str, Any]) -> None:
    aggregate["reports"][0]["observed_epoch"] = (
        aggregate["current_epoch"] - aggregate["max_staleness_epochs"] - 1
    )
    _refresh_report_id(aggregate, 0)
    _refresh_aggregate_id(aggregate)


def _duplicate_reporter(aggregate: dict[str, Any]) -> None:
    aggregate["reports"][1]["reporter_id"] = aggregate["reports"][0]["reporter_id"]
    _refresh_report_id(aggregate, 1)
    _refresh_aggregate_id(aggregate)


def _duplicate_source(aggregate: dict[str, Any]) -> None:
    aggregate["reports"][1]["source_id"] = aggregate["reports"][0]["source_id"]
    _refresh_report_id(aggregate, 1)
    _refresh_aggregate_id(aggregate)


def _nonpositive_value(aggregate: dict[str, Any]) -> None:
    aggregate["reports"][2]["value_e8"] = 0
    _refresh_report_id(aggregate, 2)
    _refresh_aggregate_id(aggregate)


def _forged_report_id(aggregate: dict[str, Any]) -> None:
    aggregate["reports"][0]["report_id"] = sample_hash("forged-report")
    _refresh_aggregate_id(aggregate)


def _forged_aggregate_id(aggregate: dict[str, Any]) -> None:
    aggregate["aggregate_id"] = sample_hash("forged-aggregate")


def _too_many_reports(aggregate: dict[str, Any]) -> None:
    aggregate["reports"].append(copy.deepcopy(aggregate["reports"][0]))
    _refresh_aggregate_id(aggregate)


def _source_diversity_source_mismatch(aggregate: dict[str, Any]) -> None:
    aggregate["source_diversity"]["sources"][0]["source_id"] = "source.unused.alt"
    _refresh_source_diversity_id(aggregate)
    _refresh_aggregate_id(aggregate)


def _source_diversity_operator_correlation(aggregate: dict[str, Any]) -> None:
    aggregate["source_diversity"]["sources"][1]["operator_id"] = (
        aggregate["source_diversity"]["sources"][0]["operator_id"]
    )
    _refresh_source_diversity_id(aggregate)
    _refresh_aggregate_id(aggregate)


def _source_diversity_query_mismatch(aggregate: dict[str, Any]) -> None:
    aggregate["source_diversity"]["query_id"] = sample_hash("other-source-diversity-query")
    _refresh_source_diversity_id(aggregate)
    _refresh_aggregate_id(aggregate)


def median3_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "aggregate_value_not_median",
            _mutate(_refreshing(lambda a: a["aggregate"].__setitem__("value_e8", a["aggregate"]["value_e8"] + 1))),
            ["aggregate_value_not_median"],
        ),
        (
            "aggregate_confidence_mismatch",
            _mutate(
                _refreshing(
                    lambda a: a["aggregate"].__setitem__(
                        "confidence_e8", a["aggregate"]["confidence_e8"] + 1
                    )
                )
            ),
            ["aggregate_confidence_mismatch"],
        ),
        (
            "aggregate_deviation_mismatch",
            _mutate(
                _refreshing(
                    lambda a: a["aggregate"].__setitem__(
                        "deviation_bps", a["aggregate"]["deviation_bps"] + 1
                    )
                )
            ),
            ["aggregate_deviation_mismatch"],
        ),
        (
            "aggregate_observed_epoch_mismatch",
            _mutate(
                _refreshing(
                    lambda a: a["aggregate"].__setitem__(
                        "observed_epoch", a["aggregate"]["observed_epoch"] - 1
                    )
                )
            ),
            ["aggregate_observed_epoch_mismatch"],
        ),
        (
            "report_query_id_mismatch",
            _mutate(_wrong_report_query),
            ["report_query_id_mismatch:1"],
        ),
        (
            "stale_report_survives",
            _mutate(_stale_report),
            ["report_stale:0"],
        ),
        (
            "future_report_survives",
            _mutate(_future_report),
            ["report_from_future:0"],
        ),
        (
            "duplicate_reporter_survives",
            _mutate(_duplicate_reporter),
            ["duplicate_reporter_id"],
        ),
        (
            "duplicate_source_survives",
            _mutate(_duplicate_source),
            ["duplicate_source_id", "not_enough_distinct_sources"],
        ),
        (
            "too_few_reports_survive",
            _mutate(_refreshing(lambda a: a.__setitem__("reports", a["reports"][:2]))),
            ["median3_requires_exactly_3_reports:2"],
        ),
        (
            "too_many_reports_survive",
            _mutate(_too_many_reports),
            ["median3_requires_exactly_3_reports:4"],
        ),
        (
            "forged_report_id_survives",
            _mutate(_forged_report_id),
            ["report_content_hash_mismatch"],
        ),
        (
            "forged_aggregate_id_survives",
            _mutate(_forged_aggregate_id),
            ["aggregate_content_hash_mismatch"],
        ),
        (
            "deviation_policy_exceeded",
            _mutate(_refreshing(lambda a: a.__setitem__("max_deviation_bps", 99))),
            ["aggregate_deviation_exceeds_policy"],
        ),
        (
            "source_diversity_report_source_mismatch_survives",
            _mutate(_source_diversity_source_mismatch),
            ["source_diversity_report_source_set_mismatch"],
        ),
        (
            "source_diversity_operator_correlation_survives",
            _mutate(_source_diversity_operator_correlation),
            ["source_diversity_rejected:not_enough_distinct_operators"],
        ),
        (
            "source_diversity_query_mismatch_survives",
            _mutate(_source_diversity_query_mismatch),
            ["source_diversity_query_id_mismatch"],
        ),
        (
            "nonpositive_report_value_survives",
            _mutate(_nonpositive_value),
            ["value_e8_must_be_int_between_1_and_1000000000000000000000000"],
        ),
        (
            "hidden_report_field_survives",
            _mutate(_refreshing(lambda a: a["reports"][0].__setitem__("debug_override", True))),
            ["unknown_report_0_field:debug_override"],
        ),
        (
            "hidden_aggregate_field_survives",
            _mutate(_refreshing(lambda a: a["aggregate"].__setitem__("debug_override", True))),
            ["unknown_aggregate_field:debug_override"],
        ),
        (
            "wrong_schema_survives",
            _mutate(_refreshing(lambda a: a.__setitem__("schema", "zenodex.oracle.median3_aggregate.v0"))),
            ["aggregate_schema_mismatch"],
        ),
    ]


@dataclass(frozen=True)
class Median3ChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_median3_chaos() -> dict[str, Any]:
    baseline = verify_median3_aggregate(base_aggregate())
    results: list[Median3ChaosCaseResult] = []
    for name, aggregate, expected_fragments in median3_chaos_cases():
        result = verify_median3_aggregate(aggregate)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            Median3ChaosCaseResult(
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
        "schema": "zenodex.oracle.median3_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the median_3 chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_median3_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
