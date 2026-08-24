#!/usr/bin/env python3
"""Verify median_3 aggregates built only from admitted Oracle reports."""

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

from zenodex_oracle_report_admission import (  # noqa: E402
    admission_content_hash,
    sample_lifecycle_for_signed_submission,
    verify_report_admission,
)
from zenodex_oracle_signed_report import (  # noqa: E402
    _BLS_AVAILABLE,
    SUBMISSION_SCHEMA,
    G2Basic,
    _build_report,
    submission_content_hash,
)
from zenodex_oracle_source_diversity import sample_source_diversity  # noqa: E402

from src.state.canonical import canonical_json_bytes

ADMITTED_MEDIAN3_SCHEMA = "zenodex.oracle.admitted_median3_aggregate.v1"
RESULT_SCHEMA = "zenodex.oracle.admitted_median3_verify_result.v1"
MAX_ADMITTED_MEDIAN3_BYTES = 2_000_000
MAX_AMOUNT = 10**24
MAX_EPOCH = 2**63 - 1
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
EVIDENCE_RANK = {"O0": 0, "O1": 1, "O2": 2, "O3": 3, "O4": 4, "O5": 5}
MIN_CRITICAL_EVIDENCE = "O3"
TOP_LEVEL_KEYS = {
    "schema",
    "aggregate_id",
    "query_id",
    "current_epoch",
    "max_staleness_epochs",
    "evidence_floor",
    "evidence_class",
    "max_deviation_bps",
    "min_distinct_sources",
    "report_admissions",
    "aggregate",
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
    "does_not_claim_source_honesty",
    "does_not_claim_production_oracle_network_live",
]


@dataclass(frozen=True)
class AdmittedMedian3Result:
    status: str
    errors: list[str]
    aggregate_id: str | None = None
    query_id: str | None = None
    value_e8: int | None = None
    confidence_e8: int | None = None
    deviation_bps: int | None = None
    observed_epoch: int | None = None
    report_count: int | None = None
    admission_count: int | None = None
    evidence_floor: str | None = None
    evidence_class: str | None = None
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
            "admission_count": self.admission_count,
            "evidence_floor": self.evidence_floor,
            "evidence_class": self.evidence_class,
            "distinct_reporter_count": self.distinct_reporter_count,
            "distinct_source_count": self.distinct_source_count,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def content_hash(obj: Mapping[str, Any], *, omit_key: str) -> str:
    body = {key: value for key, value in obj.items() if key != omit_key}
    return "sha256:" + hashlib.sha256(canonical_json_bytes(body)).hexdigest()


def aggregate_content_hash(obj: Mapping[str, Any]) -> str:
    return content_hash(obj, omit_key="aggregate_id")


def _ceil_div(numer: int, denom: int) -> int:
    return (numer + denom - 1) // denom


def _median3(values: list[int]) -> int:
    return sorted(values)[1]


def _confidence(values: list[int], median: int) -> int:
    return max(abs(value - median) for value in values)


def _deviation_bps(confidence_e8: int, median_e8: int) -> int:
    return _ceil_div(confidence_e8 * 10_000, median_e8)


def _single_report_admission(
    *,
    private_key: int,
    reporter_id: str,
    source_id: str,
    query_id: str,
    value_e8: int,
    observed_epoch: int,
    source_diversity: Mapping[str, Any],
    current_epoch: int,
    max_staleness_epochs: int,
    evidence_class: str = MIN_CRITICAL_EVIDENCE,
) -> dict[str, Any]:
    if not _BLS_AVAILABLE or G2Basic is None:
        raise RuntimeError("py_ecc.bls.G2Basic unavailable")
    reporter_pubkey = "0x" + G2Basic.SkToPk(private_key).hex()
    chain_id = "zenodex.oracle.local"
    report = _build_report(
        private_key=private_key,
        chain_id=chain_id,
        reporter_id=reporter_id,
        reporter_pubkey=reporter_pubkey,
        query_id=query_id,
        source_id=source_id,
        value_e8=value_e8,
        observed_epoch=observed_epoch,
        sequence=0,
        previous_report_id=None,
    )
    signed_submission = {
        "schema": SUBMISSION_SCHEMA,
        "chain_id": chain_id,
        "reporter_id": reporter_id,
        "reporter_pubkey": reporter_pubkey,
        "reports": [report],
    }
    signed_submission["submission_id"] = submission_content_hash(signed_submission)
    admission = {
        "schema": "zenodex.oracle.report_admission.v1",
        "current_epoch": current_epoch,
        "max_staleness_epochs": max_staleness_epochs,
        "evidence_class": evidence_class,
        "signed_submission": signed_submission,
        "reporter_lifecycle": sample_lifecycle_for_signed_submission(
            signed_submission,
            register_epoch=min(1, observed_epoch),
            bond_epoch=min(2, observed_epoch),
        ),
        "source_diversity": dict(source_diversity),
    }
    admission["admission_id"] = admission_content_hash(admission)
    return admission


def sample_admitted_median3_aggregate(
    *,
    current_epoch: int = 104,
    latest_observed_epoch: int | None = None,
    center_value_e8: int = 100_000_000,
) -> dict[str, Any]:
    if not isinstance(current_epoch, int) or isinstance(current_epoch, bool) or current_epoch < 0:
        raise ValueError("current_epoch must be a nonnegative int")
    if latest_observed_epoch is None:
        latest_observed_epoch = max(0, current_epoch - 2)
    if (
        not isinstance(latest_observed_epoch, int)
        or isinstance(latest_observed_epoch, bool)
        or latest_observed_epoch < 0
        or latest_observed_epoch > current_epoch
    ):
        raise ValueError(
            "latest_observed_epoch must be a nonnegative int not exceeding current_epoch"
        )
    if (
        not isinstance(center_value_e8, int)
        or isinstance(center_value_e8, bool)
        or center_value_e8 < 2
        or center_value_e8 > MAX_AMOUNT
    ):
        raise ValueError("center_value_e8 must be an int between 2 and MAX_AMOUNT")
    upper_spread_e8 = max(1, center_value_e8 // 100)
    lower_spread_e8 = max(1, center_value_e8 // 200)
    if center_value_e8 + upper_spread_e8 > MAX_AMOUNT:
        raise ValueError("center_value_e8 leaves no room for the sample upper report")
    source_diversity = sample_source_diversity()
    query_id = str(source_diversity["query_id"])
    source_ids = [str(source["source_id"]) for source in source_diversity["sources"]]
    observed_epochs = (
        max(0, latest_observed_epoch - 2),
        max(0, latest_observed_epoch - 1),
        latest_observed_epoch,
    )
    max_staleness_epochs = 10
    admissions = [
        _single_report_admission(
            private_key=43,
            reporter_id="reporter.alpha",
            source_id=source_ids[0],
            query_id=query_id,
            value_e8=center_value_e8,
            observed_epoch=observed_epochs[0],
            source_diversity=source_diversity,
            current_epoch=current_epoch,
            max_staleness_epochs=max_staleness_epochs,
        ),
        _single_report_admission(
            private_key=44,
            reporter_id="reporter.beta",
            source_id=source_ids[1],
            query_id=query_id,
            value_e8=center_value_e8 + upper_spread_e8,
            observed_epoch=observed_epochs[1],
            source_diversity=source_diversity,
            current_epoch=current_epoch,
            max_staleness_epochs=max_staleness_epochs,
        ),
        _single_report_admission(
            private_key=45,
            reporter_id="reporter.gamma",
            source_id=source_ids[2],
            query_id=query_id,
            value_e8=center_value_e8 - lower_spread_e8,
            observed_epoch=observed_epochs[2],
            source_diversity=source_diversity,
            current_epoch=current_epoch,
            max_staleness_epochs=max_staleness_epochs,
        ),
    ]
    values = [
        int(verify_report_admission(admission).admitted_reports[0]["value_e8"])
        for admission in admissions
    ]
    epochs = [
        int(verify_report_admission(admission).admitted_reports[0]["observed_epoch"])
        for admission in admissions
    ]
    median = _median3(values)
    confidence = _confidence(values, median)
    deviation = _deviation_bps(confidence, median)
    aggregate = {
        "schema": ADMITTED_MEDIAN3_SCHEMA,
        "query_id": query_id,
        "current_epoch": current_epoch,
        "max_staleness_epochs": max_staleness_epochs,
        "evidence_floor": MIN_CRITICAL_EVIDENCE,
        "evidence_class": MIN_CRITICAL_EVIDENCE,
        "max_deviation_bps": 200,
        "min_distinct_sources": 3,
        "report_admissions": admissions,
        "aggregate": {
            "value_e8": median,
            "confidence_e8": confidence,
            "deviation_bps": deviation,
            "observed_epoch": max(epochs),
            "report_count": 3,
        },
    }
    aggregate["aggregate_id"] = aggregate_content_hash(aggregate)
    return aggregate


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


def _evidence_class(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or value not in EVIDENCE_RANK:
        errors.append(f"{key}_invalid")
        return None
    if EVIDENCE_RANK[value] < EVIDENCE_RANK[MIN_CRITICAL_EVIDENCE]:
        errors.append(f"{key}_below_critical_minimum")
    return value


def _report_admissions(obj: Mapping[str, Any], errors: list[str]) -> list[Mapping[str, Any]]:
    raw = obj.get("report_admissions")
    if not isinstance(raw, list):
        errors.append("report_admissions_must_be_list")
        return []
    if len(raw) != 3:
        errors.append(f"admitted_median3_requires_exactly_3_admissions:{len(raw)}")
        return []
    admissions: list[Mapping[str, Any]] = []
    for pos, admission in enumerate(raw):
        if not isinstance(admission, Mapping):
            errors.append(f"admission_{pos}_must_be_object")
            continue
        admissions.append(admission)
    return admissions


def _aggregate(obj: Mapping[str, Any], errors: list[str]) -> Mapping[str, Any] | None:
    raw = obj.get("aggregate")
    if not isinstance(raw, Mapping):
        errors.append("aggregate_must_be_object")
        return None
    _unknown_fields(raw, allowed=AGGREGATE_KEYS, label="aggregate", errors=errors)
    return raw


def verify_admitted_median3_aggregate(obj: Mapping[str, Any]) -> AdmittedMedian3Result:
    errors: list[str] = []
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="admitted_median3", errors=errors)
    if obj.get("schema") != ADMITTED_MEDIAN3_SCHEMA:
        errors.append("admitted_median3_schema_mismatch")

    aggregate_id = _hash(obj, "aggregate_id", errors)
    if aggregate_id is not None:
        try:
            expected_aggregate_id = aggregate_content_hash(obj)
        except (TypeError, ValueError):
            expected_aggregate_id = None
            errors.append(f"aggregate_content_hash_unencodable:{aggregate_id}")
        if expected_aggregate_id is not None and aggregate_id != expected_aggregate_id:
            errors.append(f"aggregate_content_hash_mismatch:{aggregate_id}")

    query_id = _hash(obj, "query_id", errors)
    current_epoch = _int_between(obj, "current_epoch", errors, maximum=MAX_EPOCH)
    max_staleness_epochs = _int_between(obj, "max_staleness_epochs", errors, maximum=MAX_EPOCH)
    evidence_floor = _evidence_class(obj, "evidence_floor", errors)
    evidence_class = _evidence_class(obj, "evidence_class", errors)
    max_deviation_bps = _int_between(obj, "max_deviation_bps", errors, maximum=10_000)
    min_distinct_sources = _int_between(obj, "min_distinct_sources", errors, minimum=1, maximum=3)
    admissions = _report_admissions(obj, errors)
    aggregate = _aggregate(obj, errors)
    if (
        evidence_floor is not None
        and evidence_class is not None
        and EVIDENCE_RANK[evidence_class] < EVIDENCE_RANK[evidence_floor]
    ):
        errors.append("aggregate_evidence_class_below_floor")

    admitted_reports: list[Mapping[str, Any]] = []
    admission_ids: list[str] = []
    admission_evidence_classes: list[str] = []
    for pos, admission in enumerate(admissions):
        result = verify_report_admission(admission)
        if result.status != "accepted":
            for error in result.errors:
                errors.append(f"report_admission_{pos}_rejected:{error}")
        if result.admission_id is not None:
            admission_ids.append(result.admission_id)
        if current_epoch is not None and result.current_epoch is not None and current_epoch != result.current_epoch:
            errors.append(f"admission_current_epoch_mismatch:{pos}")
        if (
            max_staleness_epochs is not None
            and result.max_staleness_epochs is not None
            and max_staleness_epochs != result.max_staleness_epochs
        ):
            errors.append(f"admission_max_staleness_epochs_mismatch:{pos}")
        if result.evidence_class is not None:
            admission_evidence_classes.append(result.evidence_class)
            if (
                evidence_floor is not None
                and EVIDENCE_RANK[result.evidence_class] < EVIDENCE_RANK[evidence_floor]
            ):
                errors.append(f"admission_evidence_class_below_floor:{pos}:{result.evidence_class}<{evidence_floor}")
        reports = list(result.admitted_reports or [])
        if len(reports) != 1:
            errors.append(f"admission_must_contain_exactly_one_report:{pos}:{len(reports)}")
        elif query_id is not None and reports[0].get("query_id") != query_id:
            errors.append(f"admitted_report_query_mismatch:{pos}")
        if reports:
            admitted_reports.extend(reports[:1])

    duplicate_admissions = sorted(
        {admission_id for admission_id in admission_ids if admission_ids.count(admission_id) > 1}
    )
    for admission_id in duplicate_admissions:
        errors.append(f"duplicate_admission_id:{admission_id}")

    values: list[int] = []
    observed_epochs: list[int] = []
    reporter_ids: list[str] = []
    source_ids: list[str] = []
    report_ids: list[str] = []
    for pos, report in enumerate(admitted_reports):
        report_id = report.get("report_id")
        reporter_id = report.get("reporter_id")
        source_id = report.get("source_id")
        value_e8 = report.get("value_e8")
        observed_epoch = report.get("observed_epoch")
        if isinstance(report_id, str):
            report_ids.append(report_id)
        if isinstance(reporter_id, str):
            reporter_ids.append(reporter_id)
        if isinstance(source_id, str):
            source_ids.append(source_id)
        if isinstance(value_e8, int) and not isinstance(value_e8, bool):
            values.append(value_e8)
        else:
            errors.append(f"admitted_report_value_malformed:{pos}")
        if isinstance(observed_epoch, int) and not isinstance(observed_epoch, bool):
            observed_epochs.append(observed_epoch)
        else:
            errors.append(f"admitted_report_epoch_malformed:{pos}")

    duplicate_reports = sorted({report_id for report_id in report_ids if report_ids.count(report_id) > 1})
    for report_id in duplicate_reports:
        errors.append(f"duplicate_report_id:{report_id}")
    duplicate_reporters = sorted(
        {reporter_id for reporter_id in reporter_ids if reporter_ids.count(reporter_id) > 1}
    )
    for reporter_id in duplicate_reporters:
        errors.append(f"duplicate_reporter_id:{reporter_id}")
    duplicate_sources = sorted({source_id for source_id in source_ids if source_ids.count(source_id) > 1})
    for source_id in duplicate_sources:
        errors.append(f"duplicate_source_id:{source_id}")
    if min_distinct_sources is not None and len(set(source_ids)) < min_distinct_sources:
        errors.append("not_enough_distinct_sources")

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
    if evidence_class is not None and admission_evidence_classes:
        min_admission_rank = min(EVIDENCE_RANK[value] for value in admission_evidence_classes)
        if EVIDENCE_RANK[evidence_class] > min_admission_rank:
            errors.append("aggregate_evidence_class_exceeds_admission_minimum")

    return AdmittedMedian3Result(
        status="rejected" if errors else "accepted",
        errors=errors,
        aggregate_id=aggregate_id,
        query_id=query_id,
        value_e8=aggregate_value,
        confidence_e8=aggregate_confidence,
        deviation_bps=aggregate_deviation,
        observed_epoch=aggregate_observed_epoch,
        report_count=aggregate_report_count,
        admission_count=len(admissions),
        evidence_floor=evidence_floor,
        evidence_class=evidence_class,
        distinct_reporter_count=len(set(reporter_ids)),
        distinct_source_count=len(set(source_ids)),
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_ADMITTED_MEDIAN3_BYTES:
        raise ValueError(f"admitted_median3_file_too_large:{size}>{MAX_ADMITTED_MEDIAN3_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("admitted median3 root must be a JSON object")
    return obj


def _write_result(result: AdmittedMedian3Result, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        aggregate = _load_json(Path(args.aggregate))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = AdmittedMedian3Result(status="inconclusive", errors=[f"admitted_median3_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_admitted_median3_aggregate(aggregate)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_admitted_median3_aggregate(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an admitted median_3 aggregate JSON file")
    verify.add_argument("aggregate", help="path to an admitted median_3 aggregate JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted admitted median_3 aggregate")
    sample.add_argument("--output", help="optional output path for the sample aggregate JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
