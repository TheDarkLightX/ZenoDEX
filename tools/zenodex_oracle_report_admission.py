#!/usr/bin/env python3
"""Verify first-shell Zeno Oracle report admission bundles."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_reporter_lifecycle import (  # noqa: E402
    LIFECYCLE_SCHEMA,
    verify_lifecycle_trace,
)
from zenodex_oracle_signed_report import (  # noqa: E402
    sample_submission,
    verify_signed_report_submission,
)
from zenodex_oracle_source_diversity import (  # noqa: E402
    sample_source_diversity,
    verify_source_diversity,
)

from src.state.canonical import canonical_json_bytes

ADMISSION_SCHEMA = "zenodex.oracle.report_admission.v1"
RESULT_SCHEMA = "zenodex.oracle.report_admission_verify_result.v1"
MAX_ADMISSION_BYTES = 1_000_000
MAX_EPOCH = 2**63 - 1
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
EVIDENCE_RANK = {"O0": 0, "O1": 1, "O2": 2, "O3": 3, "O4": 4, "O5": 5}
MIN_CRITICAL_EVIDENCE = "O3"
TOP_LEVEL_KEYS = {
    "schema",
    "admission_id",
    "current_epoch",
    "max_staleness_epochs",
    "evidence_class",
    "signed_submission",
    "reporter_lifecycle",
    "source_diversity",
}
NOT_CLAIMED = [
    "does_not_claim_report_value_true",
    "does_not_claim_reporter_honesty",
    "does_not_claim_source_honesty",
    "does_not_claim_production_oracle_network_live",
]


@dataclass(frozen=True)
class ReportAdmissionResult:
    status: str
    errors: list[str]
    admission_id: str | None = None
    reporter_id: str | None = None
    query_id: str | None = None
    admitted_report_count: int | None = None
    current_epoch: int | None = None
    max_staleness_epochs: int | None = None
    evidence_class: str | None = None
    admitted_reports: list[dict[str, Any]] | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "admission_id": self.admission_id,
            "reporter_id": self.reporter_id,
            "query_id": self.query_id,
            "admitted_report_count": self.admitted_report_count,
            "current_epoch": self.current_epoch,
            "max_staleness_epochs": self.max_staleness_epochs,
            "evidence_class": self.evidence_class,
            "admitted_reports": list(self.admitted_reports or []),
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def _content_hash(obj: Mapping[str, Any], *, omit_key: str) -> str:
    body = {key: value for key, value in obj.items() if key != omit_key}
    return "sha256:" + hashlib.sha256(canonical_json_bytes(body)).hexdigest()


def admission_content_hash(obj: Mapping[str, Any]) -> str:
    return _content_hash(obj, omit_key="admission_id")


def sample_lifecycle_for_signed_submission(
    signed_submission: Mapping[str, Any],
    *,
    register_epoch: int = 1,
    bond_epoch: int = 2,
) -> dict[str, Any]:
    for name, epoch in (("register_epoch", register_epoch), ("bond_epoch", bond_epoch)):
        if not isinstance(epoch, int) or isinstance(epoch, bool) or epoch < 0:
            raise ValueError(f"{name} must be a nonnegative int")
    if register_epoch > bond_epoch:
        raise ValueError("register_epoch must not exceed bond_epoch")
    reporter_id = str(signed_submission["reporter_id"])
    reports = list(signed_submission["reports"])
    events: list[dict[str, Any]] = [
        {"type": "register", "epoch": register_epoch},
        {"type": "deposit_bond", "epoch": bond_epoch, "amount": 100},
    ]
    for report in reports:
        events.append(
            {
                "type": "submit_report",
                "epoch": int(report["observed_epoch"]),
                "report_id": str(report["report_id"]),
                "query_id": str(report["query_id"]),
                "value_hash": str(report["payload_hash"]),
            }
        )
    return {
        "schema": LIFECYCLE_SCHEMA,
        "reporter_id": reporter_id,
        "required_bond": 100,
        "events": events,
    }


def sample_report_admission() -> dict[str, Any]:
    signed_submission = sample_submission()
    source_diversity = sample_source_diversity()
    lifecycle = sample_lifecycle_for_signed_submission(signed_submission)
    admission = {
        "schema": ADMISSION_SCHEMA,
        "current_epoch": 104,
        "max_staleness_epochs": 10,
        "evidence_class": MIN_CRITICAL_EVIDENCE,
        "signed_submission": signed_submission,
        "reporter_lifecycle": lifecycle,
        "source_diversity": source_diversity,
    }
    admission["admission_id"] = admission_content_hash(admission)
    return admission


def _unknown_fields(
    obj: Mapping[str, Any],
    *,
    allowed: set[str],
    label: str,
    errors: list[str],
) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not SHA256_RE.match(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _int_between(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int,
    maximum: int,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum or value > maximum:
        errors.append(f"{key}_must_be_int_between_{minimum}_and_{maximum}")
        return None
    return int(value)


def _mapping(obj: Mapping[str, Any], key: str, errors: list[str]) -> Mapping[str, Any] | None:
    value = obj.get(key)
    if not isinstance(value, Mapping):
        errors.append(f"{key}_must_be_object")
        return None
    return value


def _evidence_class(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or value not in EVIDENCE_RANK:
        errors.append(f"{key}_invalid")
        return None
    if EVIDENCE_RANK[value] < EVIDENCE_RANK[MIN_CRITICAL_EVIDENCE]:
        errors.append(f"{key}_below_critical_minimum")
    return value


def _source_ids(source_diversity: Mapping[str, Any]) -> set[str]:
    raw_sources = source_diversity.get("sources")
    if not isinstance(raw_sources, list):
        return set()
    return {
        str(source["source_id"])
        for source in raw_sources
        if isinstance(source, Mapping) and isinstance(source.get("source_id"), str)
    }


def _submit_events_by_report_id(lifecycle: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    raw_events = lifecycle.get("events")
    if not isinstance(raw_events, list):
        return {}
    submits: dict[str, Mapping[str, Any]] = {}
    for event in raw_events:
        if not isinstance(event, Mapping) or event.get("type") != "submit_report":
            continue
        report_id = event.get("report_id")
        if isinstance(report_id, str):
            submits[report_id] = event
    return submits


def verify_report_admission(obj: Mapping[str, Any]) -> ReportAdmissionResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="admission", errors=errors)
    if obj.get("schema") != ADMISSION_SCHEMA:
        errors.append("admission_schema_mismatch")

    admission_id = _hash(obj, "admission_id", errors)
    if admission_id is not None:
        try:
            expected_admission_id = admission_content_hash(obj)
        except (TypeError, ValueError):
            expected_admission_id = None
            errors.append(f"admission_content_hash_unencodable:{admission_id}")
        if expected_admission_id is not None and admission_id != expected_admission_id:
            errors.append(f"admission_content_hash_mismatch:{admission_id}")

    current_epoch = _int_between(obj, "current_epoch", errors, minimum=0, maximum=MAX_EPOCH)
    max_staleness_epochs = _int_between(obj, "max_staleness_epochs", errors, minimum=0, maximum=MAX_EPOCH)
    evidence_class = _evidence_class(obj, "evidence_class", errors)
    signed_submission = _mapping(obj, "signed_submission", errors)
    reporter_lifecycle = _mapping(obj, "reporter_lifecycle", errors)
    source_diversity = _mapping(obj, "source_diversity", errors)

    signed_result = None
    lifecycle_result = None
    diversity_result = None
    if signed_submission is not None:
        signed_result = verify_signed_report_submission(signed_submission)
        if signed_result.status != "accepted":
            for error in signed_result.errors:
                errors.append(f"signed_submission_rejected:{error}")
    if reporter_lifecycle is not None:
        lifecycle_result = verify_lifecycle_trace(reporter_lifecycle)
        if lifecycle_result.status != "accepted":
            for error in lifecycle_result.errors:
                errors.append(f"reporter_lifecycle_rejected:{error}")
    if source_diversity is not None:
        diversity_result = verify_source_diversity(source_diversity)
        if diversity_result.status != "accepted":
            for error in diversity_result.errors:
                errors.append(f"source_diversity_rejected:{error}")

    reporter_id: str | None = None
    query_id: str | None = None
    admitted_reports: list[dict[str, Any]] = []
    if signed_submission is not None and isinstance(signed_submission.get("reporter_id"), str):
        reporter_id = str(signed_submission["reporter_id"])
    if (
        reporter_id is not None
        and lifecycle_result is not None
        and lifecycle_result.reporter_id is not None
        and reporter_id != lifecycle_result.reporter_id
    ):
        errors.append("reporter_lifecycle_reporter_id_mismatch")

    source_ids = _source_ids(source_diversity) if source_diversity is not None else set()
    submit_events = _submit_events_by_report_id(reporter_lifecycle) if reporter_lifecycle is not None else {}
    signed_report_ids: set[str] = set()
    if signed_submission is not None and isinstance(signed_submission.get("reports"), list):
        for pos, report in enumerate(signed_submission["reports"]):
            if not isinstance(report, Mapping):
                continue
            report_id = report.get("report_id")
            report_query_id = report.get("query_id")
            source_id = report.get("source_id")
            payload_hash = report.get("payload_hash")
            observed_epoch = report.get("observed_epoch")
            value_e8 = report.get("value_e8")
            if isinstance(report_id, str):
                signed_report_ids.add(report_id)
            if isinstance(report_query_id, str):
                if query_id is None:
                    query_id = report_query_id
                elif query_id != report_query_id:
                    errors.append(f"admitted_report_query_mismatch:{pos}")
            if (
                diversity_result is not None
                and diversity_result.query_id is not None
                and isinstance(report_query_id, str)
                and report_query_id != diversity_result.query_id
            ):
                errors.append(f"source_diversity_query_mismatch:{pos}")
            if isinstance(source_id, str) and source_ids and source_id not in source_ids:
                errors.append(f"report_source_not_in_source_diversity:{pos}")
            if isinstance(observed_epoch, int) and not isinstance(observed_epoch, bool):
                if current_epoch is not None and observed_epoch > current_epoch:
                    errors.append(f"admitted_report_from_future:{pos}")
                if (
                    current_epoch is not None
                    and max_staleness_epochs is not None
                    and current_epoch - observed_epoch > max_staleness_epochs
                ):
                    errors.append(f"admitted_report_stale:{pos}")
            if isinstance(report_id, str):
                event = submit_events.get(report_id)
                if event is None:
                    errors.append(f"lifecycle_missing_submit_report:{pos}")
                else:
                    if isinstance(report_query_id, str) and event.get("query_id") != report_query_id:
                        errors.append(f"lifecycle_submit_query_mismatch:{pos}")
                    if isinstance(payload_hash, str) and event.get("value_hash") != payload_hash:
                        errors.append(f"lifecycle_submit_value_hash_mismatch:{pos}")
            if all(
                [
                    isinstance(report_id, str),
                    isinstance(report_query_id, str),
                    isinstance(source_id, str),
                    isinstance(payload_hash, str),
                    isinstance(value_e8, int) and not isinstance(value_e8, bool),
                    isinstance(observed_epoch, int) and not isinstance(observed_epoch, bool),
                ]
            ):
                admitted_reports.append(
                    {
                        "report_id": report_id,
                        "reporter_id": reporter_id,
                        "query_id": report_query_id,
                        "source_id": source_id,
                        "payload_hash": payload_hash,
                        "value_e8": value_e8,
                        "observed_epoch": observed_epoch,
                    }
                )
    extra_submit_ids = sorted(set(submit_events.keys()) - signed_report_ids)
    for report_id in extra_submit_ids:
        errors.append(f"lifecycle_extra_submit_report:{report_id}")

    return ReportAdmissionResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        admission_id=admission_id,
        reporter_id=reporter_id,
        query_id=query_id,
        admitted_report_count=len(admitted_reports),
        current_epoch=current_epoch,
        max_staleness_epochs=max_staleness_epochs,
        evidence_class=evidence_class,
        admitted_reports=admitted_reports,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_ADMISSION_BYTES:
        raise ValueError(f"report_admission_file_too_large:{size}>{MAX_ADMISSION_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("report admission root must be a JSON object")
    return obj


def _write_result(result: ReportAdmissionResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        admission = _load_json(Path(args.admission))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = ReportAdmissionResult(status="inconclusive", errors=[f"report_admission_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_report_admission(admission)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_report_admission(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an Oracle report admission JSON file")
    verify.add_argument("admission", help="path to a report admission JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted report admission")
    sample.add_argument("--output", help="optional output path for the sample admission JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
