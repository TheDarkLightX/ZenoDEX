#!/usr/bin/env python3
"""Verify an aggregate-derived Oracle read against a concrete action/profile."""

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

from zenodex_oracle import verify_bundle  # noqa: E402
from zenodex_oracle_adapter import (  # noqa: E402
    ACTION_SCHEMA,
    PROFILE_SCHEMA,
    profile_content_hash,
    verify_oracle_use,
)
from zenodex_oracle_aggregate_read import (  # noqa: E402
    sample_aggregate_read_bridge,
    verify_aggregate_read_bridge,
)

from src.state.canonical import canonical_json_bytes

AGGREGATE_ADAPTER_SCHEMA = "zenodex.oracle.aggregate_adapter_bridge.v1"
RESULT_SCHEMA = "zenodex.oracle.aggregate_adapter_verify_result.v1"
MAX_AGGREGATE_ADAPTER_BYTES = 3_500_000
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOP_LEVEL_KEYS = {
    "schema",
    "bridge_id",
    "aggregate_read",
    "action",
    "profile",
}
NOT_CLAIMED = [
    "does_not_claim_true_market_price",
    "does_not_claim_reporter_honesty",
    "does_not_claim_source_honesty",
    "does_not_claim_downstream_module_integrated",
    "does_not_claim_production_oracle_network_live",
]


@dataclass(frozen=True)
class AggregateAdapterResult:
    status: str
    errors: list[str]
    bridge_id: str | None = None
    aggregate_read_bridge_id: str | None = None
    aggregate_id: str | None = None
    query_id: str | None = None
    value_hash: str | None = None
    value_e8: int | None = None
    consumer_module: str | None = None
    action_kind: str | None = None
    action_id: str | None = None
    action_epoch: int | None = None
    read_receipt_id: str | None = None
    consumer_action_receipt_id: str | None = None
    profile_id: str | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "bridge_id": self.bridge_id,
            "aggregate_read_bridge_id": self.aggregate_read_bridge_id,
            "aggregate_id": self.aggregate_id,
            "query_id": self.query_id,
            "value_hash": self.value_hash,
            "value_e8": self.value_e8,
            "consumer_module": self.consumer_module,
            "action_kind": self.action_kind,
            "action_id": self.action_id,
            "action_epoch": self.action_epoch,
            "read_receipt_id": self.read_receipt_id,
            "consumer_action_receipt_id": self.consumer_action_receipt_id,
            "profile_id": self.profile_id,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def _content_hash(obj: Mapping[str, Any], *, omit_key: str) -> str:
    body = {key: value for key, value in obj.items() if key != omit_key}
    return "sha256:" + hashlib.sha256(canonical_json_bytes(body)).hexdigest()


def aggregate_adapter_content_hash(obj: Mapping[str, Any]) -> str:
    return _content_hash(obj, omit_key="bridge_id")


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def sample_aggregate_adapter_bridge() -> dict[str, Any]:
    aggregate_read = sample_aggregate_read_bridge()
    bundle_result = verify_bundle(aggregate_read["receipt_bundle"])
    if bundle_result.status != "accepted":  # pragma: no cover - protects sample helper contract
        raise RuntimeError("sample aggregate-read receipt bundle did not verify")
    action = {
        "schema": ACTION_SCHEMA,
        "consumer_module": bundle_result.consumer_module,
        "action_kind": bundle_result.action_kind,
        "action_id": bundle_result.action_id,
        "action_epoch": bundle_result.action_epoch,
        "query_id": bundle_result.query_id,
        "value_hash": bundle_result.value_hash,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": bundle_result.freshness_window_epochs,
        "read_receipt_id": bundle_result.read_receipt_id,
        "consumer_action_receipt_id": bundle_result.consumer_action_receipt_id,
        "critical": True,
    }
    profile = {
        "schema": PROFILE_SCHEMA,
        "consumer_module": bundle_result.consumer_module,
        "action_kind": bundle_result.action_kind,
        "query_id": bundle_result.query_id,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": bundle_result.freshness_window_epochs,
        "critical": True,
    }
    profile["profile_id"] = profile_content_hash(profile)
    bridge = {
        "schema": AGGREGATE_ADAPTER_SCHEMA,
        "aggregate_read": aggregate_read,
        "action": action,
        "profile": profile,
    }
    bridge["bridge_id"] = aggregate_adapter_content_hash(bridge)
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


def _mapping(obj: Mapping[str, Any], key: str, errors: list[str]) -> Mapping[str, Any] | None:
    value = obj.get(key)
    if not isinstance(value, Mapping):
        errors.append(f"{key}_must_be_object")
        return None
    return value


def verify_aggregate_adapter_bridge(obj: Mapping[str, Any]) -> AggregateAdapterResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="aggregate_adapter", errors=errors)
    if obj.get("schema") != AGGREGATE_ADAPTER_SCHEMA:
        errors.append("aggregate_adapter_schema_mismatch")

    bridge_id = _hash(obj, "bridge_id", errors)
    if bridge_id is not None:
        try:
            expected_bridge_id = aggregate_adapter_content_hash(obj)
        except (TypeError, ValueError):
            expected_bridge_id = None
            errors.append(f"aggregate_adapter_content_hash_unencodable:{bridge_id}")
        if expected_bridge_id is not None and bridge_id != expected_bridge_id:
            errors.append(f"aggregate_adapter_content_hash_mismatch:{bridge_id}")

    aggregate_read = _mapping(obj, "aggregate_read", errors)
    action = _mapping(obj, "action", errors)
    profile = _mapping(obj, "profile", errors)

    aggregate_read_result = None
    if aggregate_read is not None:
        aggregate_read_result = verify_aggregate_read_bridge(aggregate_read)
        if aggregate_read_result.status != "accepted":
            errors.append("aggregate_read_not_accepted")
            errors.extend(f"aggregate_read:{error}" for error in aggregate_read_result.errors)

    adapter_result = None
    if aggregate_read is not None and action is not None and profile is not None:
        bundle = aggregate_read.get("receipt_bundle")
        if not isinstance(bundle, Mapping):
            errors.append("aggregate_read_receipt_bundle_must_be_object")
        else:
            adapter_result = verify_oracle_use(action, bundle, profile)
            if adapter_result.status != "accepted":
                errors.append("adapter_not_accepted")
                errors.extend(f"adapter:{error}" for error in adapter_result.errors)

    return AggregateAdapterResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        bridge_id=bridge_id,
        aggregate_read_bridge_id=None if aggregate_read_result is None else aggregate_read_result.bridge_id,
        aggregate_id=None if aggregate_read_result is None else aggregate_read_result.aggregate_id,
        query_id=None if aggregate_read_result is None else aggregate_read_result.query_id,
        value_hash=None if aggregate_read_result is None else aggregate_read_result.value_hash,
        value_e8=None if aggregate_read_result is None else aggregate_read_result.value_e8,
        consumer_module=None if adapter_result is None else adapter_result.consumer_module,
        action_kind=None if adapter_result is None else adapter_result.action_kind,
        action_id=None if adapter_result is None else adapter_result.action_id,
        action_epoch=None if adapter_result is None else adapter_result.action_epoch,
        read_receipt_id=None if adapter_result is None else adapter_result.read_receipt_id,
        consumer_action_receipt_id=None if adapter_result is None else adapter_result.consumer_action_receipt_id,
        profile_id=None if adapter_result is None else adapter_result.profile_id,
    )


def _reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for key, value in pairs:
        if key in obj:
            raise ValueError(f"duplicate JSON key: {key}")
        obj[key] = value
    return obj


def _reject_json_constant(value: str) -> None:
    raise ValueError(f"non-standard JSON constant: {value}")


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_AGGREGATE_ADAPTER_BYTES:
        raise ValueError(f"aggregate_adapter_file_too_large:{size}>{MAX_AGGREGATE_ADAPTER_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(
            handle,
            object_pairs_hook=_reject_duplicate_json_keys,
            parse_constant=_reject_json_constant,
        )
    if type(obj) is not dict:
        raise ValueError("aggregate adapter bridge root must be a JSON object")
    return obj


def _write_result(result: AggregateAdapterResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        bridge = _load_json(Path(args.bridge))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = AggregateAdapterResult(status="inconclusive", errors=[f"aggregate_adapter_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_aggregate_adapter_bridge(bridge)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_aggregate_adapter_bridge(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an aggregate-adapter bridge JSON file")
    verify.add_argument("bridge", help="path to an aggregate-adapter bridge JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted aggregate-adapter bridge")
    sample.add_argument("--output", help="optional output path for the sample aggregate-adapter bridge JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
