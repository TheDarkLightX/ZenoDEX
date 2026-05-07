#!/usr/bin/env python3
"""Replay deterministic chaos cases against the Oracle signed report verifier."""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_signed_report import (  # noqa: E402
    payload_content_hash,
    report_content_hash,
    sample_hash,
    sample_submission,
    signing_payload,
    submission_content_hash,
    verify_signed_report_submission,
)


def base_submission() -> dict[str, Any]:
    return sample_submission()


def _refresh_payload_hash(submission: dict[str, Any], index: int) -> None:
    report = submission["reports"][index]
    payload = signing_payload(
        chain_id=submission["chain_id"],
        reporter_id=submission["reporter_id"],
        reporter_pubkey=submission["reporter_pubkey"],
        report=report,
    )
    report["payload_hash"] = payload_content_hash(payload)


def _refresh_report_id(submission: dict[str, Any], index: int) -> None:
    submission["reports"][index]["report_id"] = report_content_hash(submission["reports"][index])


def _refresh_submission_id(submission: dict[str, Any]) -> None:
    submission["submission_id"] = submission_content_hash(submission)


def _mutate(mutator: Callable[[dict[str, Any]], None], *, refresh_submission: bool = True) -> dict[str, Any]:
    submission = copy.deepcopy(base_submission())
    mutator(submission)
    if refresh_submission:
        _refresh_submission_id(submission)
    return submission


def _payload_mutation(submission: dict[str, Any]) -> None:
    submission["reports"][1]["value_e8"] += 1
    _refresh_payload_hash(submission, 1)
    _refresh_report_id(submission, 1)


def _payload_hash_forgery(submission: dict[str, Any]) -> None:
    submission["reports"][0]["payload_hash"] = sample_hash("forged-payload")
    _refresh_report_id(submission, 0)


def _signature_mutation(submission: dict[str, Any]) -> None:
    signature = submission["reports"][1]["signature"]
    replacement = "0" if signature[-1] != "0" else "1"
    submission["reports"][1]["signature"] = signature[:-1] + replacement
    _refresh_report_id(submission, 1)


def _report_id_forgery(submission: dict[str, Any]) -> None:
    submission["reports"][0]["report_id"] = sample_hash("forged-report")


def _sequence_gap(submission: dict[str, Any]) -> None:
    submission["reports"][1]["sequence"] = 2
    _refresh_payload_hash(submission, 1)
    _refresh_report_id(submission, 1)


def _previous_chain_mismatch(submission: dict[str, Any]) -> None:
    submission["reports"][1]["previous_report_id"] = sample_hash("wrong-previous")
    _refresh_payload_hash(submission, 1)
    _refresh_report_id(submission, 1)


def _first_previous_set(submission: dict[str, Any]) -> None:
    submission["reports"][0]["previous_report_id"] = sample_hash("unexpected-previous")
    _refresh_payload_hash(submission, 0)
    _refresh_report_id(submission, 0)


def _duplicate_report_id(submission: dict[str, Any]) -> None:
    submission["reports"][1] = copy.deepcopy(submission["reports"][0])


def _hidden_report_field(submission: dict[str, Any]) -> None:
    submission["reports"][0]["debug_override"] = True
    _refresh_report_id(submission, 0)


def _bad_signature_length(submission: dict[str, Any]) -> None:
    submission["reports"][0]["signature"] = "0x1234"
    _refresh_report_id(submission, 0)


def _boolean_value(submission: dict[str, Any]) -> None:
    submission["reports"][0]["value_e8"] = True
    _refresh_payload_hash(submission, 0)
    _refresh_report_id(submission, 0)


def signed_report_chaos_cases() -> list[tuple[str, dict[str, Any], list[str]]]:
    return [
        (
            "submission_hash_forgery_survives",
            _mutate(lambda s: s.__setitem__("chain_id", "zenodex.oracle.other"), refresh_submission=False),
            ["submission_content_hash_mismatch:"],
        ),
        (
            "payload_mutation_survives_signature_check",
            _mutate(_payload_mutation),
            ["invalid_signature:1"],
        ),
        (
            "payload_hash_forgery_survives",
            _mutate(_payload_hash_forgery),
            ["payload_hash_mismatch:0"],
        ),
        (
            "signature_mutation_survives",
            _mutate(_signature_mutation),
            ["invalid_signature:1"],
        ),
        (
            "report_id_forgery_survives",
            _mutate(_report_id_forgery),
            ["report_content_hash_mismatch:0"],
        ),
        (
            "sequence_gap_survives",
            _mutate(_sequence_gap),
            ["sequence_not_contiguous:1"],
        ),
        (
            "previous_report_chain_mismatch_survives",
            _mutate(_previous_chain_mismatch),
            ["previous_report_id_chain_mismatch:1"],
        ),
        (
            "first_previous_report_id_survives",
            _mutate(_first_previous_set),
            ["first_report_previous_report_id_must_be_null", "first_report_chain_mismatch"],
        ),
        (
            "duplicate_report_id_survives",
            _mutate(_duplicate_report_id),
            ["duplicate_report_id:", "duplicate_sequence:0"],
        ),
        (
            "hidden_submission_field_survives",
            _mutate(lambda s: s.__setitem__("trusted_override", True)),
            ["unknown_submission_field:trusted_override"],
        ),
        (
            "hidden_report_field_survives",
            _mutate(_hidden_report_field),
            ["unknown_report_0_field:debug_override"],
        ),
        (
            "wrong_submission_schema_survives",
            _mutate(lambda s: s.__setitem__("schema", "zenodex.oracle.signed_report_submission.v0")),
            ["submission_schema_mismatch"],
        ),
        (
            "wrong_report_schema_survives",
            _mutate(lambda s: s["reports"][0].__setitem__("schema", "zenodex.oracle.signed_report.v0")),
            ["report_0_schema_mismatch"],
        ),
        (
            "bad_reporter_pubkey_survives",
            _mutate(lambda s: s.__setitem__("reporter_pubkey", "0x1234")),
            ["reporter_pubkey_must_be_48_bytes"],
        ),
        (
            "bad_signature_length_survives",
            _mutate(_bad_signature_length),
            ["signature_must_be_96_bytes"],
        ),
        (
            "boolean_value_survives",
            _mutate(_boolean_value),
            ["value_e8_must_be_int_between_1_and_1000000000000000000000000"],
        ),
        (
            "reports_as_object_survives",
            _mutate(lambda s: s.__setitem__("reports", {"report_id": sample_hash("fake")})),
            ["reports_must_be_list"],
        ),
        (
            "bad_source_token_survives",
            _mutate(lambda s: s["reports"][0].__setitem__("source_id", "Source Alpha")),
            ["source_id_must_be_token"],
        ),
    ]


@dataclass(frozen=True)
class SignedReportChaosCaseResult:
    name: str
    expected_reject: bool
    actual_status: str
    expected_error_fragments: list[str]
    actual_errors: list[str]
    passed: bool


def run_signed_report_chaos() -> dict[str, Any]:
    baseline = verify_signed_report_submission(base_submission())
    results: list[SignedReportChaosCaseResult] = []
    for name, submission, expected_fragments in signed_report_chaos_cases():
        result = verify_signed_report_submission(submission)
        actual_errors = list(result.errors)
        passed = result.status == "rejected" and all(
            any(fragment in error for error in actual_errors)
            for fragment in expected_fragments
        )
        results.append(
            SignedReportChaosCaseResult(
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
        "schema": "zenodex.oracle.signed_report_chaos_replay.v1",
        "ok": baseline.status == "accepted" and not failures,
        "baseline_status": baseline.status,
        "case_count": len(results),
        "rejected_case_count": sum(1 for case in results if case.actual_status == "rejected"),
        "failed_case_count": len(failures),
        "cases": [asdict(case) for case in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="optional path for the signed report chaos replay receipt JSON")
    args = parser.parse_args(argv)
    receipt = run_signed_report_chaos()
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if receipt["ok"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
