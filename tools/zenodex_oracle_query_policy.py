#!/usr/bin/env python3
"""Verify first-shell Zeno Oracle query-policy lifecycle traces."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


TRACE_SCHEMA = "zenodex.oracle.query_policy_trace.v1"
RESULT_SCHEMA = "zenodex.oracle.query_policy_verify_result.v1"
MAX_TRACE_BYTES = 250_000
MAX_EVENTS = 64
MAX_INT = 10**9
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
TOP_LEVEL_KEYS = {"schema", "query_id", "events"}
EVENT_KEYS_BY_TYPE = {
    "publish_policy": {"type", "epoch", "policy"},
    "bind_consumer": {
        "type",
        "epoch",
        "consumer_module",
        "action_kind",
        "action_id",
        "action_epoch",
        "critical",
        "policy_id",
    },
}
POLICY_KEYS = {
    "policy_id",
    "query_id",
    "version",
    "supersedes_policy_id",
    "evidence_floor",
    "max_staleness_epochs",
    "max_deviation_bps",
    "min_distinct_sources",
    "min_distinct_reporters",
    "aggregation_schema",
    "read_schema",
}
EVIDENCE_RANK = {"O0": 0, "O1": 1, "O2": 2, "O3": 3, "O4": 4, "O5": 5}
MIN_CRITICAL_EVIDENCE = EVIDENCE_RANK["O3"]
NOT_CLAIMED = [
    "does_not_claim_reporter_honesty",
    "does_not_claim_true_market_price",
    "does_not_claim_query_policy_governance_live",
    "does_not_claim_consumer_adapter_wired",
]


@dataclass(frozen=True)
class QueryPolicyResult:
    status: str
    errors: list[str]
    query_id: str | None = None
    active_policy_id: str | None = None
    active_policy_version: int | None = None
    published_policy_count: int | None = None
    bound_consumer_count: int | None = None
    last_epoch: int | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "query_id": self.query_id,
            "active_policy_id": self.active_policy_id,
            "active_policy_version": self.active_policy_version,
            "published_policy_count": self.published_policy_count,
            "bound_consumer_count": self.bound_consumer_count,
            "last_epoch": self.last_epoch,
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


def _build_policy(
    *,
    query_id: str,
    version: int,
    supersedes_policy_id: str | None,
    evidence_floor: str = "O3",
    max_staleness_epochs: int = 4,
    max_deviation_bps: int = 200,
    min_distinct_sources: int = 3,
    min_distinct_reporters: int = 3,
) -> dict[str, Any]:
    policy = {
        "query_id": query_id,
        "version": version,
        "supersedes_policy_id": supersedes_policy_id,
        "evidence_floor": evidence_floor,
        "max_staleness_epochs": max_staleness_epochs,
        "max_deviation_bps": max_deviation_bps,
        "min_distinct_sources": min_distinct_sources,
        "min_distinct_reporters": min_distinct_reporters,
        "aggregation_schema": "zenodex.oracle.median3_aggregate.v1",
        "read_schema": "zenodex.oracle.receipt_bundle.v1",
    }
    policy["policy_id"] = content_hash(policy, omit_key="policy_id")
    return policy


def sample_policy_trace() -> dict[str, Any]:
    query_id = sample_hash("zenodex-oracle-query-policy-query")
    policy_v1 = _build_policy(query_id=query_id, version=1, supersedes_policy_id=None)
    policy_v2 = _build_policy(
        query_id=query_id,
        version=2,
        supersedes_policy_id=str(policy_v1["policy_id"]),
        max_staleness_epochs=3,
        max_deviation_bps=150,
    )
    return {
        "schema": TRACE_SCHEMA,
        "query_id": query_id,
        "events": [
            {"type": "publish_policy", "epoch": 1, "policy": policy_v1},
            {
                "type": "bind_consumer",
                "epoch": 2,
                "consumer_module": "zenodex.perps",
                "action_kind": "settle_epoch",
                "action_id": sample_hash("zenodex-oracle-query-policy-action"),
                "action_epoch": 2,
                "critical": True,
                "policy_id": policy_v1["policy_id"],
            },
            {"type": "publish_policy", "epoch": 3, "policy": policy_v2},
        ],
    }


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


def _optional_hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if value is None:
        return None
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256_or_null")
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
    maximum: int = MAX_INT,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum or value > maximum:
        errors.append(f"{key}_must_be_int_between_{minimum}_and_{maximum}")
        return None
    return int(value)


def _epoch(obj: Mapping[str, Any], errors: list[str]) -> int | None:
    return _int_between(obj, "epoch", errors, minimum=0, maximum=MAX_INT)


def _events(obj: Mapping[str, Any], errors: list[str]) -> list[Mapping[str, Any]]:
    raw = obj.get("events")
    if not isinstance(raw, list):
        errors.append("events_must_be_list")
        return []
    if len(raw) > MAX_EVENTS:
        errors.append(f"events_exceed_max:{len(raw)}>{MAX_EVENTS}")
    events: list[Mapping[str, Any]] = []
    for pos, event in enumerate(raw[:MAX_EVENTS]):
        if not isinstance(event, Mapping):
            errors.append(f"event_{pos}_must_be_object")
            continue
        events.append(event)
    return events


def _evidence_floor(policy: Mapping[str, Any], errors: list[str]) -> str | None:
    value = policy.get("evidence_floor")
    if not isinstance(value, str) or value not in EVIDENCE_RANK:
        errors.append("evidence_floor_invalid")
        return None
    if EVIDENCE_RANK[value] < MIN_CRITICAL_EVIDENCE:
        errors.append("evidence_floor_below_critical_minimum")
    return value


def _validate_policy(
    policy: Mapping[str, Any],
    *,
    trace_query_id: str | None,
    errors: list[str],
) -> dict[str, Any]:
    _unknown_fields(policy, allowed=POLICY_KEYS, label="policy", errors=errors)
    policy_id = _hash(policy, "policy_id", errors)
    if policy_id is not None:
        try:
            expected_policy_id = content_hash(policy, omit_key="policy_id")
        except (TypeError, ValueError):
            expected_policy_id = None
            errors.append(f"policy_content_hash_unencodable:{policy_id}")
        if expected_policy_id is not None and policy_id != expected_policy_id:
            errors.append(f"policy_content_hash_mismatch:{policy_id}")
    query_id = _hash(policy, "query_id", errors)
    if trace_query_id is not None and query_id is not None and query_id != trace_query_id:
        errors.append("policy_query_id_mismatch")
    version = _int_between(policy, "version", errors, minimum=1)
    supersedes_policy_id = _optional_hash(policy, "supersedes_policy_id", errors)
    evidence_floor = _evidence_floor(policy, errors)
    max_staleness_epochs = _int_between(policy, "max_staleness_epochs", errors)
    max_deviation_bps = _int_between(policy, "max_deviation_bps", errors, maximum=10_000)
    min_distinct_sources = _int_between(policy, "min_distinct_sources", errors, minimum=1, maximum=64)
    min_distinct_reporters = _int_between(policy, "min_distinct_reporters", errors, minimum=1, maximum=64)
    aggregation_schema = _token(policy, "aggregation_schema", errors)
    read_schema = _token(policy, "read_schema", errors)
    return {
        "policy_id": policy_id,
        "query_id": query_id,
        "version": version,
        "supersedes_policy_id": supersedes_policy_id,
        "evidence_floor": evidence_floor,
        "max_staleness_epochs": max_staleness_epochs,
        "max_deviation_bps": max_deviation_bps,
        "min_distinct_sources": min_distinct_sources,
        "min_distinct_reporters": min_distinct_reporters,
        "aggregation_schema": aggregation_schema,
        "read_schema": read_schema,
    }


def _check_policy_revision(
    *,
    previous: dict[str, Any] | None,
    current: dict[str, Any],
    errors: list[str],
) -> None:
    if previous is None:
        if current["version"] is not None and current["version"] != 1:
            errors.append("first_policy_version_must_be_1")
        if current["supersedes_policy_id"] is not None:
            errors.append("first_policy_must_not_supersede")
        return

    if current["supersedes_policy_id"] != previous["policy_id"]:
        errors.append("policy_supersedes_must_equal_active_policy")
    if (
        current["version"] is not None
        and previous["version"] is not None
        and current["version"] != previous["version"] + 1
    ):
        errors.append("policy_version_must_increment_by_1")
    if (
        current["evidence_floor"] is not None
        and previous["evidence_floor"] is not None
        and EVIDENCE_RANK[current["evidence_floor"]] < EVIDENCE_RANK[previous["evidence_floor"]]
    ):
        errors.append("policy_evidence_floor_downgrade")
    if (
        current["max_staleness_epochs"] is not None
        and previous["max_staleness_epochs"] is not None
        and current["max_staleness_epochs"] > previous["max_staleness_epochs"]
    ):
        errors.append("policy_staleness_downgrade")
    if (
        current["max_deviation_bps"] is not None
        and previous["max_deviation_bps"] is not None
        and current["max_deviation_bps"] > previous["max_deviation_bps"]
    ):
        errors.append("policy_deviation_downgrade")
    if (
        current["min_distinct_sources"] is not None
        and previous["min_distinct_sources"] is not None
        and current["min_distinct_sources"] < previous["min_distinct_sources"]
    ):
        errors.append("policy_source_quorum_downgrade")
    if (
        current["min_distinct_reporters"] is not None
        and previous["min_distinct_reporters"] is not None
        and current["min_distinct_reporters"] < previous["min_distinct_reporters"]
    ):
        errors.append("policy_reporter_quorum_downgrade")
    if (
        current["aggregation_schema"] is not None
        and previous["aggregation_schema"] is not None
        and current["aggregation_schema"] != previous["aggregation_schema"]
    ):
        errors.append("policy_aggregation_schema_change")
    if (
        current["read_schema"] is not None
        and previous["read_schema"] is not None
        and current["read_schema"] != previous["read_schema"]
    ):
        errors.append("policy_read_schema_change")


def verify_policy_trace(obj: Mapping[str, Any]) -> QueryPolicyResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="query_policy", errors=errors)
    if obj.get("schema") != TRACE_SCHEMA:
        errors.append("query_policy_schema_mismatch")
    trace_query_id = _hash(obj, "query_id", errors)
    events = _events(obj, errors)

    policies: dict[str, dict[str, Any]] = {}
    latest_policy: dict[str, Any] | None = None
    bound_consumer_count = 0
    last_epoch: int | None = None

    for pos, event in enumerate(events):
        event_type = event.get("type")
        if not isinstance(event_type, str):
            errors.append(f"event_{pos}_type_must_be_string")
            continue
        allowed_keys = EVENT_KEYS_BY_TYPE.get(event_type)
        if allowed_keys is None:
            errors.append(f"unsupported_event_type:{event_type}")
            continue
        _unknown_fields(event, allowed=allowed_keys, label=f"event_{event_type}", errors=errors)
        epoch = _epoch(event, errors)
        if epoch is not None:
            if last_epoch is not None and epoch < last_epoch:
                errors.append(f"event_epoch_regression:{pos}")
            last_epoch = epoch if last_epoch is None else max(last_epoch, epoch)

        if event_type == "publish_policy":
            policy_obj = event.get("policy")
            if not isinstance(policy_obj, Mapping):
                errors.append("policy_must_be_object")
                continue
            before_count = len(errors)
            policy = _validate_policy(policy_obj, trace_query_id=trace_query_id, errors=errors)
            _check_policy_revision(previous=latest_policy, current=policy, errors=errors)
            policy_id = policy["policy_id"]
            if policy_id is not None and policy_id in policies:
                errors.append(f"duplicate_policy_id:{policy_id}")
            if policy_id is not None and len(errors) == before_count:
                policies[policy_id] = policy
                latest_policy = policy
        elif event_type == "bind_consumer":
            _token(event, "consumer_module", errors)
            _token(event, "action_kind", errors)
            _hash(event, "action_id", errors)
            action_epoch = _int_between(event, "action_epoch", errors)
            critical = event.get("critical")
            if critical is not True:
                errors.append("consumer_binding_must_be_critical")
            policy_id = _hash(event, "policy_id", errors)
            if epoch is not None and action_epoch is not None and action_epoch < epoch:
                errors.append("consumer_action_before_policy_binding")
            if policy_id is not None:
                if policy_id not in policies:
                    errors.append("consumer_binds_unknown_policy")
                elif latest_policy is not None and policy_id != latest_policy["policy_id"]:
                    errors.append("consumer_binds_nonlatest_policy")
                else:
                    bound_consumer_count += 1

    return QueryPolicyResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        query_id=trace_query_id,
        active_policy_id=None if latest_policy is None else latest_policy["policy_id"],
        active_policy_version=None if latest_policy is None else latest_policy["version"],
        published_policy_count=len(policies),
        bound_consumer_count=bound_consumer_count,
        last_epoch=last_epoch,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_TRACE_BYTES:
        raise ValueError(f"query_policy_file_too_large:{size}>{MAX_TRACE_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("query policy root must be a JSON object")
    return obj


def _write_result(result: QueryPolicyResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        trace = _load_json(Path(args.trace))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = QueryPolicyResult(status="inconclusive", errors=[f"query_policy_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_policy_trace(trace)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_policy_trace(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an Oracle query-policy trace JSON file")
    verify.add_argument("trace", help="path to a query-policy trace JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted query-policy trace")
    sample.add_argument("--output", help="optional output path for the sample trace JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
