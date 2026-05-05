#!/usr/bin/env python3
"""Replay deterministic chaos cases against the admitted median_3 verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_admitted_median3 import (  # noqa: E402
    _single_report_admission,
    aggregate_content_hash,
    sample_admitted_median3_aggregate,
    sample_hash,
    verify_admitted_median3_aggregate,
)
from zenodex_oracle_report_admission import admission_content_hash  # noqa: E402
from zenodex_oracle_signed_report import (  # noqa: E402
    payload_content_hash,
    report_content_hash,
    signing_payload,
    submission_content_hash,
)


def base_aggregate() -> dict[str, Any]:
    return sample_admitted_median3_aggregate()


def _refresh_admission_id(aggregate: dict[str, Any], index: int) -> None:
    admission = aggregate["report_admissions"][index]
    admission["admission_id"] = admission_content_hash(admission)


def _refresh_submission_id(aggregate: dict[str, Any], index: int) -> None:
    admission = aggregate["report_admissions"][index]
    submission = admission["signed_submission"]
    submission["submission_id"] = submission_content_hash(submission)


def _refresh_report_payload_hash(aggregate: dict[str, Any], index: int) -> None:
    admission = aggregate["report_admissions"][index]
    submission = admission["signed_submission"]
    report = submission["reports"][0]
    payload = signing_payload(
        chain_id=submission["chain_id"],
        reporter_id=submission["reporter_id"],
        reporter_pubkey=submission["reporter_pubkey"],
        report=report,
    )
    report["payload_hash"] = payload_content_hash(payload)


def _refresh_report_id(aggregate: dict[str, Any], index: int) -> None:
    report = aggregate["report_admissions"][index]["signed_submission"]["reports"][0]
    report["report_id"] = report_content_hash(report)


def _refresh_aggregate_id(aggregate: dict[str, Any]) -> None:
    aggregate["aggregate_id"] = aggregate_content_hash(aggregate)


def _mutate(mutator: Callable[[dict[str, Any]], None], *, refresh: bool = True) -> dict[str, Any]:
    aggregate = copy.deepcopy(base_aggregate())
    mutator(aggregate)
    if refresh:
        _refresh_aggregate_id(aggregate)
    return aggregate


def _admission_signed_value_mutation(aggregate: dict[str, Any]) -> None:
    report = aggregate["report_admissions"][1]["signed_submission"]["reports"][0]
    report["value_e8"] += 1
    _refresh_report_payload_hash(aggregate, 1)
    _refresh_report_id(aggregate, 1)
    _refresh_submission_id(aggregate, 1)
    _refresh_admission_id(aggregate, 1)


def _duplicate_admission(aggregate: dict[str, Any]) -> None:
    aggregate["report_admissions"][1] = copy.deepcopy(aggregate["report_admissions"][0])


def _duplicate_reporter(aggregate: dict[str, Any]) -> None:
    source_diversity = aggregate["report_admissions"][1]["source_diversity"]
    report = aggregate["report_admissions"][1]["signed_submission"]["reports"][0]
    aggregate["report_admissions"][1] = _single_report_admission(
        private_key=144,
        reporter_id=aggregate["report_admissions"][0]["signed_submission"]["reporter_id"],
        source_id=report["source_id"],
        query_id=aggregate["query_id"],
        value_e8=report["value_e8"],
        observed_epoch=report["observed_epoch"],
        source_diversity=source_diversity,
        current_epoch=aggregate["current_epoch"],
        max_staleness_epochs=aggregate["max_staleness_epochs"],
    )


def _duplicate_source(aggregate: dict[str, Any]) -> None:
    source_diversity = aggregate["report_admissions"][1]["source_diversity"]
    submission = aggregate["report_admissions"][1]["signed_submission"]
    report = submission["reports"][0]
    aggregate["report_admissions"][1] = _single_report_admission(
        private_key=144,
        reporter_id=submission["reporter_id"],
        source_id=aggregate["report_admissions"][0]["signed_submission"]["reports"][0]["source_id"],
        query_id=aggregate["query_id"],
        value_e8=report["value_e8"],
        observed_epoch=report["observed_epoch"],
        source_diversity=source_diversity,
        current_epoch=aggregate["current_epoch"],
        max_staleness_epochs=aggregate["max_staleness_epochs"],
    )


def _admission_query_mismatch(aggregate: dict[str, Any]) -> None:
    aggregate["report_admissions"][2]["source_diversity"]["query_id"] = sample_hash("wrong-admission-query")
    _refresh_admission_id(aggregate, 2)


def _admission_epoch_mismatch(aggregate: dict[str, Any]) -> None:
    aggregate["report_admissions"][0]["current_epoch"] = aggregate["current_epoch"] - 1
    _refresh_admission_id(aggregate, 0)


def _admission_staleness_mismatch(aggregate: dict[str, Any]) -> None:
    aggregate["report_admissions"][0]["max_staleness_epochs"] = aggregate["max_staleness_epochs"] - 1
    _refresh_admission_id(aggregate, 0)


def _extra_report_inside_admission(aggregate: dict[str, Any]) -> None:
    admission = aggregate["report_admissions"][0]
    admission["signed_submission"]["reports"].append(copy.deepcopy(admission["signed_submission"]["reports"][0]))
    _refresh_submission_id(aggregate, 0)
    _refresh_admission_id(aggregate, 0)


def admitted_median3_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "aggregate_hash_forgery_survives",
            _mutate(lambda a: a.__setitem__("current_epoch", a["current_epoch"] - 1), refresh=False),
            ["aggregate_content_hash_mismatch:"],
        ),
        (
            "wrong_median_value_survives",
            _mutate(lambda a: a["aggregate"].__setitem__("value_e8", a["aggregate"]["value_e8"] + 1)),
            ["aggregate_value_not_median"],
        ),
        (
            "wrong_confidence_survives",
            _mutate(lambda a: a["aggregate"].__setitem__("confidence_e8", a["aggregate"]["confidence_e8"] + 1)),
            ["aggregate_confidence_mismatch"],
        ),
        (
            "wrong_deviation_survives",
            _mutate(lambda a: a["aggregate"].__setitem__("deviation_bps", a["aggregate"]["deviation_bps"] + 1)),
            ["aggregate_deviation_mismatch"],
        ),
        (
            "wrong_observed_epoch_survives",
            _mutate(lambda a: a["aggregate"].__setitem__("observed_epoch", a["aggregate"]["observed_epoch"] - 1)),
            ["aggregate_observed_epoch_mismatch"],
        ),
        (
            "too_few_admissions_survive",
            _mutate(lambda a: a.__setitem__("report_admissions", a["report_admissions"][:2])),
            ["admitted_median3_requires_exactly_3_admissions:2"],
        ),
        (
            "admission_rejection_survives",
            _mutate(_admission_signed_value_mutation),
            ["report_admission_1_rejected:signed_submission_rejected:invalid_signature:0"],
        ),
        (
            "duplicate_admission_survives",
            _mutate(_duplicate_admission),
            ["duplicate_admission_id:"],
        ),
        (
            "duplicate_reporter_survives",
            _mutate(_duplicate_reporter),
            ["duplicate_reporter_id:"],
        ),
        (
            "duplicate_source_survives",
            _mutate(_duplicate_source),
            ["duplicate_source_id:", "not_enough_distinct_sources"],
        ),
        (
            "admission_query_mismatch_survives",
            _mutate(_admission_query_mismatch),
            ["report_admission_2_rejected:source_diversity_query_mismatch:0"],
        ),
        (
            "admission_epoch_mismatch_survives",
            _mutate(_admission_epoch_mismatch),
            ["admission_current_epoch_mismatch:0"],
        ),
        (
            "admission_staleness_mismatch_survives",
            _mutate(_admission_staleness_mismatch),
            ["admission_max_staleness_epochs_mismatch:0"],
        ),
        (
            "multi_report_admission_survives",
            _mutate(_extra_report_inside_admission),
            ["report_admission_0_rejected:signed_submission_rejected:sequence_not_contiguous:1"],
        ),
        (
            "deviation_policy_exceeded_survives",
            _mutate(lambda a: a.__setitem__("max_deviation_bps", 99)),
            ["aggregate_deviation_exceeds_policy"],
        ),
        (
            "admission_evidence_floor_bypass_survives",
            _mutate(lambda a: a["report_admissions"][1].__setitem__("evidence_class", "O2")),
            [
                "report_admission_1_rejected:evidence_class_below_critical_minimum",
                "admission_evidence_class_below_floor:1:O2<O3",
            ],
        ),
        (
            "aggregate_evidence_overclaim_survives",
            _mutate(lambda a: a.__setitem__("evidence_class", "O4")),
            ["aggregate_evidence_class_exceeds_admission_minimum"],
        ),
        (
            "hidden_top_level_field_survives",
            _mutate(lambda a: a.__setitem__("trusted_override", True)),
            ["unknown_admitted_median3_field:trusted_override"],
        ),
        (
            "hidden_aggregate_field_survives",
            _mutate(lambda a: a["aggregate"].__setitem__("trusted_override", True)),
            ["unknown_aggregate_field:trusted_override"],
        ),
        (
            "wrong_schema_survives",
            _mutate(lambda a: a.__setitem__("schema", "zenodex.oracle.admitted_median3_aggregate.v0")),
            ["admitted_median3_schema_mismatch"],
        ),
    ]


@dataclass(frozen=True)
class AdmittedMedian3ChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_admitted_median3_chaos() -> dict[str, Any]:
    baseline = verify_admitted_median3_aggregate(base_aggregate())
    results: list[AdmittedMedian3ChaosCaseResult] = []
    for name, aggregate, expected_fragments in admitted_median3_chaos_cases():
        result = verify_admitted_median3_aggregate(aggregate)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            AdmittedMedian3ChaosCaseResult(
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
        "schema": "zenodex.oracle.admitted_median3_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the admitted median3 chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_admitted_median3_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
