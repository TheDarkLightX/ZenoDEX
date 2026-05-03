#!/usr/bin/env python3
"""Verify that an Oracle read bundle is derived from an admitted aggregate."""

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

from src.state.canonical import canonical_json_bytes
from zenodex_oracle import (  # noqa: E402
    ACTION_TYPE,
    BUNDLE_SCHEMA,
    READ_TYPE,
    receipt_content_hash,
    verify_bundle,
)
from zenodex_oracle_admitted_median3 import (  # noqa: E402
    sample_admitted_median3_aggregate,
    verify_admitted_median3_aggregate,
)


AGGREGATE_READ_SCHEMA = "zenodex.oracle.aggregate_read_bridge.v1"
RESULT_SCHEMA = "zenodex.oracle.aggregate_read_verify_result.v1"
READ_VALUE_SCHEMA = "zenodex.oracle.aggregate_read_value.v1"
MAX_AGGREGATE_READ_BYTES = 3_000_000
MAX_EPOCH = 2**63 - 1
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOP_LEVEL_KEYS = {
    "schema",
    "bridge_id",
    "freshness_window_epochs",
    "aggregate",
    "receipt_bundle",
}
NOT_CLAIMED = [
    "does_not_claim_true_market_price",
    "does_not_claim_reporter_honesty",
    "does_not_claim_source_honesty",
    "does_not_claim_production_oracle_network_live",
]


@dataclass(frozen=True)
class AggregateReadResult:
    status: str
    errors: list[str]
    bridge_id: str | None = None
    aggregate_id: str | None = None
    query_id: str | None = None
    value_hash: str | None = None
    read_receipt_id: str | None = None
    consumer_action_receipt_id: str | None = None
    value_e8: int | None = None
    confidence_e8: int | None = None
    deviation_bps: int | None = None
    observed_epoch: int | None = None
    expires_at_epoch: int | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "bridge_id": self.bridge_id,
            "aggregate_id": self.aggregate_id,
            "query_id": self.query_id,
            "value_hash": self.value_hash,
            "read_receipt_id": self.read_receipt_id,
            "consumer_action_receipt_id": self.consumer_action_receipt_id,
            "value_e8": self.value_e8,
            "confidence_e8": self.confidence_e8,
            "deviation_bps": self.deviation_bps,
            "observed_epoch": self.observed_epoch,
            "expires_at_epoch": self.expires_at_epoch,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def _content_hash(obj: Mapping[str, Any], *, omit_key: str) -> str:
    body = {key: value for key, value in obj.items() if key != omit_key}
    return "sha256:" + hashlib.sha256(canonical_json_bytes(body)).hexdigest()


def bridge_content_hash(obj: Mapping[str, Any]) -> str:
    return _content_hash(obj, omit_key="bridge_id")


def aggregate_read_value_hash(
    *,
    aggregate_id: str,
    query_id: str,
    value_e8: int,
    confidence_e8: int,
    deviation_bps: int,
    observed_epoch: int,
    report_count: int,
    admission_count: int,
) -> str:
    value = {
        "schema": READ_VALUE_SCHEMA,
        "aggregate_id": aggregate_id,
        "query_id": query_id,
        "value_e8": value_e8,
        "confidence_e8": confidence_e8,
        "deviation_bps": deviation_bps,
        "observed_epoch": observed_epoch,
        "report_count": report_count,
        "admission_count": admission_count,
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def _bundle_for_aggregate(
    *,
    aggregate_id: str,
    query_id: str,
    value_hash: str,
    observed_epoch: int,
    freshness_window_epochs: int,
) -> dict[str, Any]:
    read = {
        "type": READ_TYPE,
        "status": "accepted",
        "query_id": query_id,
        "value_hash": value_hash,
        "evidence_class": "O3",
        "fresh": True,
        "observed_epoch": observed_epoch,
        "expires_at_epoch": observed_epoch + freshness_window_epochs,
        "dispute_clear": True,
        "uncertainty_accepted": True,
        "depends_on": [],
    }
    read["id"] = receipt_content_hash(read)
    action = {
        "type": ACTION_TYPE,
        "status": "accepted",
        "consumer_module": "zenodex.oracle.sample",
        "action_kind": "sample_aggregate_read",
        "action_id": sample_hash(f"sample-aggregate-action:{aggregate_id}"),
        "action_epoch": observed_epoch + 1,
        "freshness_window_epochs": freshness_window_epochs,
        "query_id": query_id,
        "value_hash": value_hash,
        "read_receipt_id": read["id"],
        "critical": True,
        "emergency_oracle_bypass": False,
        "depends_on": [read["id"]],
    }
    action["id"] = receipt_content_hash(action)
    return {
        "schema": BUNDLE_SCHEMA,
        "terminal": {
            "read_receipt_id": read["id"],
            "consumer_action_receipt_id": action["id"],
        },
        "receipts": [read, action],
    }


def sample_aggregate_read_bridge() -> dict[str, Any]:
    aggregate = sample_admitted_median3_aggregate()
    result = verify_admitted_median3_aggregate(aggregate)
    if result.status != "accepted":  # pragma: no cover - protects sample helper contract
        raise RuntimeError("sample admitted median3 aggregate did not verify")
    value_hash = aggregate_read_value_hash(
        aggregate_id=str(result.aggregate_id),
        query_id=str(result.query_id),
        value_e8=int(result.value_e8),
        confidence_e8=int(result.confidence_e8),
        deviation_bps=int(result.deviation_bps),
        observed_epoch=int(result.observed_epoch),
        report_count=int(result.report_count),
        admission_count=int(result.admission_count),
    )
    bridge = {
        "schema": AGGREGATE_READ_SCHEMA,
        "freshness_window_epochs": 4,
        "aggregate": aggregate,
        "receipt_bundle": _bundle_for_aggregate(
            aggregate_id=str(result.aggregate_id),
            query_id=str(result.query_id),
            value_hash=value_hash,
            observed_epoch=int(result.observed_epoch),
            freshness_window_epochs=4,
        ),
    }
    bridge["bridge_id"] = bridge_content_hash(bridge)
    return bridge


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
    maximum: int = MAX_EPOCH,
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


def verify_aggregate_read_bridge(obj: Mapping[str, Any]) -> AggregateReadResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="aggregate_read", errors=errors)
    if obj.get("schema") != AGGREGATE_READ_SCHEMA:
        errors.append("aggregate_read_schema_mismatch")

    bridge_id = _hash(obj, "bridge_id", errors)
    if bridge_id is not None:
        try:
            expected_bridge_id = bridge_content_hash(obj)
        except (TypeError, ValueError):
            expected_bridge_id = None
            errors.append(f"bridge_content_hash_unencodable:{bridge_id}")
        if expected_bridge_id is not None and bridge_id != expected_bridge_id:
            errors.append(f"bridge_content_hash_mismatch:{bridge_id}")

    freshness_window_epochs = _int_between(obj, "freshness_window_epochs", errors, minimum=1)
    aggregate = _mapping(obj, "aggregate", errors)
    bundle = _mapping(obj, "receipt_bundle", errors)

    aggregate_result = None
    if aggregate is not None:
        aggregate_result = verify_admitted_median3_aggregate(aggregate)
        if aggregate_result.status != "accepted":
            errors.append("admitted_aggregate_not_accepted")
            errors.extend(f"aggregate:{error}" for error in aggregate_result.errors)

    bundle_result = None
    if bundle is not None:
        bundle_result = verify_bundle(bundle)
        if bundle_result.status != "accepted":
            errors.append("receipt_bundle_not_accepted")
            errors.extend(f"bundle:{error}" for error in bundle_result.errors)

    expected_value_hash: str | None = None
    expires_at_epoch: int | None = None
    if aggregate_result is not None and aggregate_result.status == "accepted":
        expected_value_hash = aggregate_read_value_hash(
            aggregate_id=str(aggregate_result.aggregate_id),
            query_id=str(aggregate_result.query_id),
            value_e8=int(aggregate_result.value_e8),
            confidence_e8=int(aggregate_result.confidence_e8),
            deviation_bps=int(aggregate_result.deviation_bps),
            observed_epoch=int(aggregate_result.observed_epoch),
            report_count=int(aggregate_result.report_count),
            admission_count=int(aggregate_result.admission_count),
        )
        if freshness_window_epochs is not None:
            expires_at_epoch = int(aggregate_result.observed_epoch) + freshness_window_epochs

    if bundle_result is not None and aggregate_result is not None and aggregate_result.status == "accepted":
        if bundle_result.query_id != aggregate_result.query_id:
            errors.append("bundle_query_id_mismatch")
        if expected_value_hash is not None and bundle_result.value_hash != expected_value_hash:
            errors.append("bundle_value_hash_mismatch")
        if bundle_result.observed_epoch != aggregate_result.observed_epoch:
            errors.append("bundle_observed_epoch_mismatch")
        if expires_at_epoch is not None and bundle_result.expires_at_epoch != expires_at_epoch:
            errors.append("bundle_expiry_mismatch")
        if bundle_result.freshness_window_epochs != freshness_window_epochs:
            errors.append("bundle_freshness_window_mismatch")

    return AggregateReadResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        bridge_id=bridge_id,
        aggregate_id=None if aggregate_result is None else aggregate_result.aggregate_id,
        query_id=None if aggregate_result is None else aggregate_result.query_id,
        value_hash=expected_value_hash,
        read_receipt_id=None if bundle_result is None else bundle_result.read_receipt_id,
        consumer_action_receipt_id=None if bundle_result is None else bundle_result.consumer_action_receipt_id,
        value_e8=None if aggregate_result is None else aggregate_result.value_e8,
        confidence_e8=None if aggregate_result is None else aggregate_result.confidence_e8,
        deviation_bps=None if aggregate_result is None else aggregate_result.deviation_bps,
        observed_epoch=None if aggregate_result is None else aggregate_result.observed_epoch,
        expires_at_epoch=expires_at_epoch,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_AGGREGATE_READ_BYTES:
        raise ValueError(f"aggregate_read_file_too_large:{size}>{MAX_AGGREGATE_READ_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("aggregate read bridge root must be a JSON object")
    return obj


def _write_result(result: AggregateReadResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        bridge = _load_json(Path(args.bridge))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = AggregateReadResult(status="inconclusive", errors=[f"aggregate_read_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_aggregate_read_bridge(bridge)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_aggregate_read_bridge(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an aggregate-read bridge JSON file")
    verify.add_argument("bridge", help="path to an aggregate-read bridge JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted aggregate-read bridge")
    sample.add_argument("--output", help="optional output path for the sample aggregate-read bridge JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
