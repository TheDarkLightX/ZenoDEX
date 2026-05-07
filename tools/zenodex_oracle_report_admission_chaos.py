#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Oracle report admission verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_report_admission import (  # noqa: E402
    admission_content_hash,
    sample_report_admission,
    verify_report_admission,
)
from zenodex_oracle_signed_report import (  # noqa: E402
    payload_content_hash,
    report_content_hash,
    sample_hash,
    signing_payload,
    submission_content_hash,
)
from zenodex_oracle_source_diversity import source_set_content_hash  # noqa: E402


def base_admission() -> dict[str, Any]:
    return sample_report_admission()


def _refresh_payload_hash(admission: dict[str, Any], index: int) -> None:
    submission = admission["signed_submission"]
    report = submission["reports"][index]
    payload = signing_payload(
        chain_id=submission["chain_id"],
        reporter_id=submission["reporter_id"],
        reporter_pubkey=submission["reporter_pubkey"],
        report=report,
    )
    report["payload_hash"] = payload_content_hash(payload)


def _refresh_report_id(admission: dict[str, Any], index: int) -> None:
    report = admission["signed_submission"]["reports"][index]
    report["report_id"] = report_content_hash(report)


def _refresh_submission_id(admission: dict[str, Any]) -> None:
    admission["signed_submission"]["submission_id"] = submission_content_hash(admission["signed_submission"])


def _refresh_source_diversity_id(admission: dict[str, Any]) -> None:
    admission["source_diversity"]["source_set_id"] = source_set_content_hash(admission["source_diversity"])


def _refresh_admission_id(admission: dict[str, Any]) -> None:
    admission["admission_id"] = admission_content_hash(admission)


def _lifecycle_submit(admission: dict[str, Any], report_id: str) -> dict[str, Any]:
    for event in admission["reporter_lifecycle"]["events"]:
        if event.get("type") == "submit_report" and event.get("report_id") == report_id:
            return event
    raise AssertionError("submit event not found")


def _mutate(mutator: Callable[[dict[str, Any]], None], *, refresh: bool = True) -> dict[str, Any]:
    admission = copy.deepcopy(base_admission())
    mutator(admission)
    if refresh:
        _refresh_admission_id(admission)
    return admission


def _signed_payload_mutation(admission: dict[str, Any]) -> None:
    report = admission["signed_submission"]["reports"][1]
    submit_event = _lifecycle_submit(admission, report["report_id"])
    report["value_e8"] += 1
    _refresh_payload_hash(admission, 1)
    _refresh_report_id(admission, 1)
    submit_event["report_id"] = report["report_id"]
    submit_event["value_hash"] = report["payload_hash"]
    _refresh_submission_id(admission)


def _missing_lifecycle_submit(admission: dict[str, Any]) -> None:
    admission["reporter_lifecycle"]["events"] = admission["reporter_lifecycle"]["events"][:-1]


def _lifecycle_query_mismatch(admission: dict[str, Any]) -> None:
    report = admission["signed_submission"]["reports"][0]
    _lifecycle_submit(admission, report["report_id"])["query_id"] = sample_hash("wrong-query")


def _lifecycle_value_hash_mismatch(admission: dict[str, Any]) -> None:
    report = admission["signed_submission"]["reports"][0]
    _lifecycle_submit(admission, report["report_id"])["value_hash"] = sample_hash("wrong-value")


def _extra_lifecycle_submit(admission: dict[str, Any]) -> None:
    admission["reporter_lifecycle"]["events"].append(
        {
            "type": "submit_report",
            "epoch": 102,
            "report_id": sample_hash("extra-report"),
            "query_id": admission["signed_submission"]["reports"][0]["query_id"],
            "value_hash": sample_hash("extra-value"),
        }
    )


def _source_not_in_diversity(admission: dict[str, Any]) -> None:
    admission["source_diversity"]["sources"][0]["source_id"] = "source.unused.alt"
    _refresh_source_diversity_id(admission)


def _source_query_mismatch(admission: dict[str, Any]) -> None:
    admission["source_diversity"]["query_id"] = sample_hash("other-source-query")
    _refresh_source_diversity_id(admission)


def _source_operator_correlation(admission: dict[str, Any]) -> None:
    admission["source_diversity"]["sources"][1]["operator_id"] = admission["source_diversity"]["sources"][0]["operator_id"]
    _refresh_source_diversity_id(admission)


def _underbond_lifecycle(admission: dict[str, Any]) -> None:
    admission["reporter_lifecycle"]["events"][1]["amount"] = 0


def _hidden_signed_submission_field(admission: dict[str, Any]) -> None:
    admission["signed_submission"]["trusted_override"] = True
    _refresh_submission_id(admission)


def report_admission_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "admission_hash_forgery_survives",
            _mutate(lambda a: a.__setitem__("current_epoch", 103), refresh=False),
            ["admission_content_hash_mismatch:"],
        ),
        (
            "signed_payload_mutation_survives",
            _mutate(_signed_payload_mutation),
            ["signed_submission_rejected:invalid_signature:1"],
        ),
        (
            "reporter_id_mismatch_survives",
            _mutate(lambda a: a["reporter_lifecycle"].__setitem__("reporter_id", "reporter.other")),
            ["reporter_lifecycle_reporter_id_mismatch"],
        ),
        (
            "missing_lifecycle_submit_survives",
            _mutate(_missing_lifecycle_submit),
            ["lifecycle_missing_submit_report:1"],
        ),
        (
            "lifecycle_query_mismatch_survives",
            _mutate(_lifecycle_query_mismatch),
            ["lifecycle_submit_query_mismatch:0"],
        ),
        (
            "lifecycle_value_hash_mismatch_survives",
            _mutate(_lifecycle_value_hash_mismatch),
            ["lifecycle_submit_value_hash_mismatch:0"],
        ),
        (
            "extra_lifecycle_submit_survives",
            _mutate(_extra_lifecycle_submit),
            ["lifecycle_extra_submit_report:"],
        ),
        (
            "source_not_in_diversity_survives",
            _mutate(_source_not_in_diversity),
            ["report_source_not_in_source_diversity:0"],
        ),
        (
            "source_diversity_query_mismatch_survives",
            _mutate(_source_query_mismatch),
            ["source_diversity_query_mismatch:0"],
        ),
        (
            "future_admitted_report_survives",
            _mutate(lambda a: a.__setitem__("current_epoch", 100)),
            ["admitted_report_from_future:1"],
        ),
        (
            "stale_admitted_report_survives",
            _mutate(lambda a: a.__setitem__("max_staleness_epochs", 2)),
            ["admitted_report_stale:0"],
        ),
        (
            "underbonded_lifecycle_survives",
            _mutate(_underbond_lifecycle),
            ["reporter_lifecycle_rejected:report_submitted_under_required_bond"],
        ),
        (
            "source_operator_correlation_survives",
            _mutate(_source_operator_correlation),
            ["source_diversity_rejected:not_enough_distinct_operators"],
        ),
        (
            "hidden_admission_field_survives",
            _mutate(lambda a: a.__setitem__("trusted_override", True)),
            ["unknown_admission_field:trusted_override"],
        ),
        (
            "hidden_signed_submission_field_survives",
            _mutate(_hidden_signed_submission_field),
            ["signed_submission_rejected:unknown_submission_field:trusted_override"],
        ),
        (
            "wrong_admission_schema_survives",
            _mutate(lambda a: a.__setitem__("schema", "zenodex.oracle.report_admission.v0")),
            ["admission_schema_mismatch"],
        ),
        (
            "boolean_current_epoch_survives",
            _mutate(lambda a: a.__setitem__("current_epoch", True)),
            ["current_epoch_must_be_int_between_0_and_9223372036854775807"],
        ),
        (
            "source_diversity_as_null_survives",
            _mutate(lambda a: a.__setitem__("source_diversity", None)),
            ["source_diversity_must_be_object"],
        ),
    ]


@dataclass(frozen=True)
class ReportAdmissionChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_report_admission_chaos() -> dict[str, Any]:
    baseline = verify_report_admission(base_admission())
    results: list[ReportAdmissionChaosCaseResult] = []
    for name, admission, expected_fragments in report_admission_chaos_cases():
        result = verify_report_admission(admission)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            ReportAdmissionChaosCaseResult(
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
        "schema": "zenodex.oracle.report_admission_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the report admission chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_report_admission_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
