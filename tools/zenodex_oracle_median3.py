#!/usr/bin/env python3
"""Verify first-shell Zeno Oracle median_3 aggregate receipts."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from zenodex_oracle_source_diversity import (  # noqa: E402
    verify_source_diversity,
    sample_source_diversity,
)


AGGREGATE_SCHEMA = "zenodex.oracle.median3_aggregate.v1"
RESULT_SCHEMA = "zenodex.oracle.median3_verify_result.v1"
MAX_AGGREGATE_BYTES = 500_000
MAX_AMOUNT = 10**24
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,95}$")
TOP_LEVEL_KEYS = {
    "schema",
    "aggregate_id",
    "query_id",
    "current_epoch",
    "max_staleness_epochs",
    "max_deviation_bps",
    "min_distinct_sources",
    "source_diversity",
    "reports",
    "aggregate",
}
REPORT_KEYS = {
    "report_id",
    "reporter_id",
    "source_id",
    "query_id",
    "value_e8",
    "observed_epoch",
}
AGGREGATE_KEYS = {
    "value_e8",
    "confidence_e8",
    "deviation_bps",
    "observed_epoch",
    "report_count",
}
NOT_CLAIMED = [
    "does_not_claim_true_market_price",
    "does_not_claim_reporter_honesty",
    "does_not_claim_real_world_source_independence_beyond_declared_source_classification",
    "does_not_claim_production_oracle_network_live",
]


@dataclass(frozen=True)
class Median3VerifyResult:
    status: str
    errors: list[str]
    aggregate_id: str | None = None
    query_id: str | None = None
    value_e8: int | None = None
    confidence_e8: int | None = None
    deviation_bps: int | None = None
    observed_epoch: int | None = None
    report_count: int | None = None
    distinct_reporter_count: int | None = None
    distinct_source_count: int | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "aggregate_id": self.aggregate_id,
            "query_id": self.query_id,
            "value_e8": self.value_e8,
            "confidence_e8": self.confidence_e8,
            "deviation_bps": self.deviation_bps,
            "observed_epoch": self.observed_epoch,
            "report_count": self.report_count,
            "distinct_reporter_count": self.distinct_reporter_count,
            "distinct_source_count": self.distinct_source_count,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def _canonical_json_bytes(obj: Mapping[str, Any]) -> bytes:
    return json.dumps(
        obj,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def content_hash(obj: Mapping[str, Any], *, omit_key: str) -> str:
    body = {key: value for key, value in obj.items() if key != omit_key}
    return "sha256:" + hashlib.sha256(_canonical_json_bytes(body)).hexdigest()


def _ceil_div(numer: int, denom: int) -> int:
    return (numer + denom - 1) // denom


def _median3(values: list[int]) -> int:
    return sorted(values)[1]


def _confidence(values: list[int], median: int) -> int:
    return max(abs(value - median) for value in values)


def _deviation_bps(confidence_e8: int, median_e8: int) -> int:
    return _ceil_div(confidence_e8 * 10_000, median_e8)


def _build_report(
    *,
    reporter_id: str,
    source_id: str,
    query_id: str,
    value_e8: int,
    observed_epoch: int,
) -> dict[str, Any]:
    report = {
        "reporter_id": reporter_id,
        "source_id": source_id,
        "query_id": query_id,
        "value_e8": value_e8,
        "observed_epoch": observed_epoch,
    }
    report["report_id"] = content_hash(report, omit_key="report_id")
    return report


def sample_aggregate() -> dict[str, Any]:
    source_diversity = sample_source_diversity()
    query_id = str(source_diversity["query_id"])
    source_ids = [str(source["source_id"]) for source in source_diversity["sources"]]
    reports = [
        _build_report(
            reporter_id="reporter.alpha",
            source_id=source_ids[0],
            query_id=query_id,
            value_e8=100_000_000,
            observed_epoch=100,
        ),
        _build_report(
            reporter_id="reporter.beta",
            source_id=source_ids[1],
            query_id=query_id,
            value_e8=101_000_000,
            observed_epoch=101,
        ),
        _build_report(
            reporter_id="reporter.gamma",
            source_id=source_ids[2],
            query_id=query_id,
            value_e8=99_500_000,
            observed_epoch=102,
        ),
    ]
    values = [int(report["value_e8"]) for report in reports]
    median = _median3(values)
    confidence = _confidence(values, median)
    deviation = _deviation_bps(confidence, median)
    receipt = {
        "schema": AGGREGATE_SCHEMA,
        "query_id": query_id,
        "current_epoch": 104,
        "max_staleness_epochs": 10,
        "max_deviation_bps": 200,
        "min_distinct_sources": 3,
        "source_diversity": source_diversity,
        "reports": reports,
        "aggregate": {
            "value_e8": median,
            "confidence_e8": confidence,
            "deviation_bps": deviation,
            "observed_epoch": max(int(report["observed_epoch"]) for report in reports),
            "report_count": 3,
        },
    }
    receipt["aggregate_id"] = content_hash(receipt, omit_key="aggregate_id")
    return receipt


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and bool(SHA256_RE.match(value))


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
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _token(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{key}_must_be_token")
        return None
    return str(value)


def _int_between(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int = 0,
    maximum: int = MAX_AMOUNT,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum or value > maximum:
        errors.append(f"{key}_must_be_int_between_{minimum}_and_{maximum}")
        return None
    return int(value)


def _reports(obj: Mapping[str, Any], errors: list[str]) -> list[Mapping[str, Any]]:
    raw = obj.get("reports")
    if not isinstance(raw, list):
        errors.append("reports_must_be_list")
        return []
    if len(raw) != 3:
        errors.append(f"median3_requires_exactly_3_reports:{len(raw)}")
        return []
    reports: list[Mapping[str, Any]] = []
    for pos, report in enumerate(raw):
        if not isinstance(report, Mapping):
            errors.append(f"report_{pos}_must_be_object")
            continue
        reports.append(report)
    return reports


def _aggregate(obj: Mapping[str, Any], errors: list[str]) -> Mapping[str, Any] | None:
    raw = obj.get("aggregate")
    if not isinstance(raw, Mapping):
        errors.append("aggregate_must_be_object")
        return None
    _unknown_fields(raw, allowed=AGGREGATE_KEYS, label="aggregate", errors=errors)
    return raw


def _source_diversity(obj: Mapping[str, Any], errors: list[str]) -> Mapping[str, Any] | None:
    raw = obj.get("source_diversity")
    if not isinstance(raw, Mapping):
        errors.append("source_diversity_must_be_object")
        return None
    return raw


def verify_median3_aggregate(obj: Mapping[str, Any]) -> Median3VerifyResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="median3", errors=errors)
    if obj.get("schema") != AGGREGATE_SCHEMA:
        errors.append("aggregate_schema_mismatch")

    aggregate_id = _hash(obj, "aggregate_id", errors)
    if aggregate_id is not None:
        try:
            expected_aggregate_id = content_hash(obj, omit_key="aggregate_id")
        except (TypeError, ValueError):
            expected_aggregate_id = None
            errors.append(f"aggregate_content_hash_unencodable:{aggregate_id}")
        if expected_aggregate_id is not None and aggregate_id != expected_aggregate_id:
            errors.append(f"aggregate_content_hash_mismatch:{aggregate_id}")

    query_id = _hash(obj, "query_id", errors)
    current_epoch = _int_between(obj, "current_epoch", errors)
    max_staleness_epochs = _int_between(obj, "max_staleness_epochs", errors)
    max_deviation_bps = _int_between(obj, "max_deviation_bps", errors, maximum=10_000)
    min_distinct_sources = _int_between(obj, "min_distinct_sources", errors, minimum=1, maximum=3)
    source_diversity = _source_diversity(obj, errors)
    reports = _reports(obj, errors)
    aggregate = _aggregate(obj, errors)

    source_diversity_source_ids: set[str] = set()
    if source_diversity is not None:
        diversity_result = verify_source_diversity(source_diversity)
        if diversity_result.status != "accepted":
            for error in diversity_result.errors:
                errors.append(f"source_diversity_rejected:{error}")
        if (
            query_id is not None
            and diversity_result.query_id is not None
            and diversity_result.query_id != query_id
        ):
            errors.append("source_diversity_query_id_mismatch")
        raw_sources = source_diversity.get("sources")
        if isinstance(raw_sources, list):
            for source in raw_sources:
                if isinstance(source, Mapping) and isinstance(source.get("source_id"), str):
                    source_diversity_source_ids.add(str(source["source_id"]))

    values: list[int] = []
    observed_epochs: list[int] = []
    reporter_ids: list[str] = []
    source_ids: list[str] = []
    report_ids: list[str] = []
    for pos, report in enumerate(reports):
        _unknown_fields(report, allowed=REPORT_KEYS, label=f"report_{pos}", errors=errors)
        report_id = _hash(report, "report_id", errors)
        if report_id is not None:
            try:
                expected_report_id = content_hash(report, omit_key="report_id")
            except (TypeError, ValueError):
                expected_report_id = None
                errors.append(f"report_content_hash_unencodable:{report_id}")
            if expected_report_id is not None and report_id != expected_report_id:
                errors.append(f"report_content_hash_mismatch:{report_id}")
            report_ids.append(report_id)
        reporter_id = _token(report, "reporter_id", errors)
        source_id = _token(report, "source_id", errors)
        report_query_id = _hash(report, "query_id", errors)
        value_e8 = _int_between(report, "value_e8", errors, minimum=1)
        observed_epoch = _int_between(report, "observed_epoch", errors)
        if reporter_id is not None:
            reporter_ids.append(reporter_id)
        if source_id is not None:
            source_ids.append(source_id)
        if query_id is not None and report_query_id is not None and report_query_id != query_id:
            errors.append(f"report_query_id_mismatch:{pos}")
        if value_e8 is not None:
            values.append(value_e8)
        if observed_epoch is not None:
            observed_epochs.append(observed_epoch)
            if current_epoch is not None and observed_epoch > current_epoch:
                errors.append(f"report_from_future:{pos}")
            if (
                current_epoch is not None
                and max_staleness_epochs is not None
                and current_epoch - observed_epoch > max_staleness_epochs
            ):
                errors.append(f"report_stale:{pos}")

    duplicate_reporters = sorted({reporter_id for reporter_id in reporter_ids if reporter_ids.count(reporter_id) > 1})
    for reporter_id in duplicate_reporters:
        errors.append(f"duplicate_reporter_id:{reporter_id}")
    duplicate_sources = sorted({source_id for source_id in source_ids if source_ids.count(source_id) > 1})
    for source_id in duplicate_sources:
        errors.append(f"duplicate_source_id:{source_id}")
    duplicate_reports = sorted({report_id for report_id in report_ids if report_ids.count(report_id) > 1})
    for report_id in duplicate_reports:
        errors.append(f"duplicate_report_id:{report_id}")
    if min_distinct_sources is not None and len(set(source_ids)) < min_distinct_sources:
        errors.append("not_enough_distinct_sources")
    if (
        len(source_ids) == 3
        and source_diversity_source_ids
        and set(source_ids) != source_diversity_source_ids
    ):
        errors.append("source_diversity_report_source_set_mismatch")

    median: int | None = None
    confidence: int | None = None
    deviation: int | None = None
    aggregate_observed_epoch: int | None = None
    if len(values) == 3:
        median = _median3(values)
        confidence = _confidence(values, median)
        deviation = _deviation_bps(confidence, median)
    if len(observed_epochs) == 3:
        aggregate_observed_epoch = max(observed_epochs)

    aggregate_value: int | None = None
    aggregate_confidence: int | None = None
    aggregate_deviation: int | None = None
    aggregate_report_count: int | None = None
    if aggregate is not None:
        aggregate_value = _int_between(aggregate, "value_e8", errors, minimum=1)
        aggregate_confidence = _int_between(aggregate, "confidence_e8", errors)
        aggregate_deviation = _int_between(aggregate, "deviation_bps", errors, maximum=10_000)
        aggregate_observed = _int_between(aggregate, "observed_epoch", errors)
        aggregate_report_count = _int_between(aggregate, "report_count", errors, maximum=3)
        if median is not None and aggregate_value is not None and aggregate_value != median:
            errors.append("aggregate_value_not_median")
        if confidence is not None and aggregate_confidence is not None and aggregate_confidence != confidence:
            errors.append("aggregate_confidence_mismatch")
        if deviation is not None and aggregate_deviation is not None and aggregate_deviation != deviation:
            errors.append("aggregate_deviation_mismatch")
        if (
            aggregate_observed_epoch is not None
            and aggregate_observed is not None
            and aggregate_observed != aggregate_observed_epoch
        ):
            errors.append("aggregate_observed_epoch_mismatch")
        if aggregate_report_count is not None and aggregate_report_count != 3:
            errors.append("aggregate_report_count_mismatch")

    if max_deviation_bps is not None and aggregate_deviation is not None and aggregate_deviation > max_deviation_bps:
        errors.append("aggregate_deviation_exceeds_policy")

    return Median3VerifyResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        aggregate_id=aggregate_id,
        query_id=query_id,
        value_e8=aggregate_value,
        confidence_e8=aggregate_confidence,
        deviation_bps=aggregate_deviation,
        observed_epoch=aggregate_observed_epoch,
        report_count=aggregate_report_count,
        distinct_reporter_count=len(set(reporter_ids)),
        distinct_source_count=len(set(source_ids)),
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_AGGREGATE_BYTES:
        raise ValueError(f"aggregate_file_too_large:{size}>{MAX_AGGREGATE_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("aggregate root must be a JSON object")
    return obj


def _write_result(result: Median3VerifyResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        aggregate = _load_json(Path(args.aggregate))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = Median3VerifyResult(status="inconclusive", errors=[f"aggregate_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_median3_aggregate(aggregate)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_aggregate(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an Oracle median_3 aggregate JSON file")
    verify.add_argument("aggregate", help="path to a median_3 aggregate JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted median_3 aggregate")
    sample.add_argument("--output", help="optional output path for the sample aggregate JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
