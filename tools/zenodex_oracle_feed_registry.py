#!/usr/bin/env python3
"""Verify first-shell Zeno Oracle feed registry objects."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parent))

from zenodex_oracle_source_diversity import (  # noqa: E402
    sample_source_diversity,
    source_set_content_hash,
    verify_source_diversity,
)


REGISTRY_SCHEMA = "zenodex.oracle.feed_registry.v1"
FEED_SCHEMA = "zenodex.oracle.feed.v1"
QUERY_SPEC_SCHEMA = "zenodex.oracle.query_spec.v1"
AGGREGATE_POLICY_SCHEMA = "zenodex.oracle.aggregate_policy.v1"
RESULT_SCHEMA = "zenodex.oracle.feed_registry_verify_result.v1"
MAX_REGISTRY_BYTES = 1_000_000
MAX_FEEDS = 64
MAX_INT = 10**12
VALUE_SCALE_E8 = 100_000_000
MIN_CRITICAL_EVIDENCE = "O3"
ADMITTED_MEDIAN3_SCHEMA = "zenodex.oracle.admitted_median3_aggregate.v1"
SIGNED_REPORT_SCHEMA = "zenodex.oracle.signed_report.v1"
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
REGISTRY_KEYS = {"schema", "registry_id", "current_epoch", "feeds"}
FEED_KEYS = {
    "schema",
    "feed_id",
    "status",
    "created_epoch",
    "query_spec",
    "source_diversity",
    "aggregate_policy",
}
QUERY_SPEC_KEYS = {
    "schema",
    "query_id",
    "query_kind",
    "base_asset",
    "quote_asset",
    "unit",
    "value_scale",
}
AGGREGATE_POLICY_KEYS = {
    "schema",
    "policy_id",
    "aggregation_schema",
    "report_schema",
    "evidence_floor",
    "min_reporters",
    "min_sources",
    "freshness_window_epochs",
    "max_deviation_bps",
}
EVIDENCE_RANK = {"O0": 0, "O1": 1, "O2": 2, "O3": 3, "O4": 4, "O5": 5}
NOT_CLAIMED = [
    "does_not_claim_feed_governance_live",
    "does_not_claim_source_honesty",
    "does_not_claim_true_market_price",
    "does_not_claim_reporter_network_live",
    "does_not_claim_production_token_live",
]


@dataclass(frozen=True)
class FeedRegistryResult:
    status: str
    errors: list[str]
    registry_id: str | None = None
    feed_count: int | None = None
    active_feed_count: int | None = None
    query_ids: list[str] | None = None
    feed_ids: list[str] | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "registry_id": self.registry_id,
            "feed_count": self.feed_count,
            "active_feed_count": self.active_feed_count,
            "query_ids": [] if self.query_ids is None else list(self.query_ids),
            "feed_ids": [] if self.feed_ids is None else list(self.feed_ids),
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


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


def _build_query_spec(
    *,
    base_asset: str = "agrs",
    quote_asset: str = "zdex",
    query_kind: str = "price_e8",
    unit: str = "quote_per_base",
) -> dict[str, Any]:
    spec = {
        "schema": QUERY_SPEC_SCHEMA,
        "query_kind": query_kind,
        "base_asset": base_asset,
        "quote_asset": quote_asset,
        "unit": unit,
        "value_scale": VALUE_SCALE_E8,
    }
    spec["query_id"] = content_hash(spec, omit_key="query_id")
    return spec


def _build_source_diversity(query_id: str) -> dict[str, Any]:
    source_diversity = sample_source_diversity()
    source_diversity["query_id"] = query_id
    source_diversity["source_set_id"] = source_set_content_hash(source_diversity)
    return source_diversity


def _build_aggregate_policy(
    *,
    min_reporters: int = 3,
    min_sources: int = 3,
    freshness_window_epochs: int = 4,
    max_deviation_bps: int = 200,
) -> dict[str, Any]:
    policy = {
        "schema": AGGREGATE_POLICY_SCHEMA,
        "aggregation_schema": ADMITTED_MEDIAN3_SCHEMA,
        "report_schema": SIGNED_REPORT_SCHEMA,
        "evidence_floor": MIN_CRITICAL_EVIDENCE,
        "min_reporters": min_reporters,
        "min_sources": min_sources,
        "freshness_window_epochs": freshness_window_epochs,
        "max_deviation_bps": max_deviation_bps,
    }
    policy["policy_id"] = content_hash(policy, omit_key="policy_id")
    return policy


def _build_feed(*, created_epoch: int = 10) -> dict[str, Any]:
    query_spec = _build_query_spec()
    source_diversity = _build_source_diversity(str(query_spec["query_id"]))
    aggregate_policy = _build_aggregate_policy()
    feed = {
        "schema": FEED_SCHEMA,
        "status": "active",
        "created_epoch": created_epoch,
        "query_spec": query_spec,
        "source_diversity": source_diversity,
        "aggregate_policy": aggregate_policy,
    }
    feed["feed_id"] = content_hash(feed, omit_key="feed_id")
    return feed


def sample_feed_registry() -> dict[str, Any]:
    registry = {
        "schema": REGISTRY_SCHEMA,
        "current_epoch": 10,
        "feeds": [_build_feed(created_epoch=10)],
    }
    registry["registry_id"] = content_hash(registry, omit_key="registry_id")
    return registry


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
    maximum: int = MAX_INT,
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


def _feeds(obj: Mapping[str, Any], errors: list[str]) -> list[Mapping[str, Any]]:
    raw = obj.get("feeds")
    if not isinstance(raw, list):
        errors.append("feeds_must_be_list")
        return []
    if not raw:
        errors.append("feeds_must_be_nonempty")
    if len(raw) > MAX_FEEDS:
        errors.append(f"feeds_exceed_max:{len(raw)}>{MAX_FEEDS}")
    feeds: list[Mapping[str, Any]] = []
    for pos, feed in enumerate(raw[:MAX_FEEDS]):
        if not isinstance(feed, Mapping):
            errors.append(f"feed_{pos}_must_be_object")
            continue
        feeds.append(feed)
    return feeds


def _validate_query_spec(spec: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    _unknown_fields(spec, allowed=QUERY_SPEC_KEYS, label="query_spec", errors=errors)
    if spec.get("schema") != QUERY_SPEC_SCHEMA:
        errors.append("query_spec_schema_mismatch")
    query_id = _hash(spec, "query_id", errors)
    if query_id is not None:
        try:
            expected_query_id = content_hash(spec, omit_key="query_id")
        except (TypeError, ValueError):
            expected_query_id = None
            errors.append(f"query_spec_content_hash_unencodable:{query_id}")
        if expected_query_id is not None and query_id != expected_query_id:
            errors.append(f"query_spec_content_hash_mismatch:{query_id}")
    query_kind = _token(spec, "query_kind", errors)
    if query_kind != "price_e8":
        errors.append("query_kind_must_be_price_e8")
    base_asset = _token(spec, "base_asset", errors)
    quote_asset = _token(spec, "quote_asset", errors)
    if base_asset is not None and quote_asset is not None and base_asset == quote_asset:
        errors.append("base_quote_assets_must_differ")
    unit = _token(spec, "unit", errors)
    if unit != "quote_per_base":
        errors.append("unit_must_be_quote_per_base")
    value_scale = _int_between(spec, "value_scale", errors, minimum=1, maximum=10**18)
    if value_scale is not None and value_scale != VALUE_SCALE_E8:
        errors.append("value_scale_must_be_e8")
    return {
        "query_id": query_id,
        "base_asset": base_asset,
        "quote_asset": quote_asset,
    }


def _validate_aggregate_policy(policy: Mapping[str, Any], errors: list[str]) -> dict[str, Any]:
    _unknown_fields(policy, allowed=AGGREGATE_POLICY_KEYS, label="aggregate_policy", errors=errors)
    if policy.get("schema") != AGGREGATE_POLICY_SCHEMA:
        errors.append("aggregate_policy_schema_mismatch")
    policy_id = _hash(policy, "policy_id", errors)
    if policy_id is not None:
        try:
            expected_policy_id = content_hash(policy, omit_key="policy_id")
        except (TypeError, ValueError):
            expected_policy_id = None
            errors.append(f"aggregate_policy_content_hash_unencodable:{policy_id}")
        if expected_policy_id is not None and policy_id != expected_policy_id:
            errors.append(f"aggregate_policy_content_hash_mismatch:{policy_id}")
    aggregation_schema = _token(policy, "aggregation_schema", errors)
    if aggregation_schema != ADMITTED_MEDIAN3_SCHEMA:
        errors.append("aggregation_schema_must_be_admitted_median3")
    report_schema = _token(policy, "report_schema", errors)
    if report_schema != SIGNED_REPORT_SCHEMA:
        errors.append("report_schema_must_be_signed_report_v1")
    evidence_floor = policy.get("evidence_floor")
    if not isinstance(evidence_floor, str) or evidence_floor not in EVIDENCE_RANK:
        errors.append("evidence_floor_invalid")
        evidence_floor = None
    elif EVIDENCE_RANK[evidence_floor] < EVIDENCE_RANK[MIN_CRITICAL_EVIDENCE]:
        errors.append("evidence_floor_below_critical_minimum")
    min_reporters = _int_between(policy, "min_reporters", errors, minimum=3, maximum=MAX_FEEDS)
    min_sources = _int_between(policy, "min_sources", errors, minimum=3, maximum=MAX_FEEDS)
    freshness_window_epochs = _int_between(
        policy,
        "freshness_window_epochs",
        errors,
        minimum=1,
        maximum=MAX_INT,
    )
    max_deviation_bps = _int_between(policy, "max_deviation_bps", errors, minimum=0, maximum=10_000)
    return {
        "policy_id": policy_id,
        "min_reporters": min_reporters,
        "min_sources": min_sources,
        "freshness_window_epochs": freshness_window_epochs,
        "max_deviation_bps": max_deviation_bps,
    }


def _validate_feed(
    feed: Mapping[str, Any],
    *,
    current_epoch: int | None,
    errors: list[str],
) -> dict[str, Any]:
    _unknown_fields(feed, allowed=FEED_KEYS, label="feed", errors=errors)
    if feed.get("schema") != FEED_SCHEMA:
        errors.append("feed_schema_mismatch")
    feed_id = _hash(feed, "feed_id", errors)
    if feed_id is not None:
        try:
            expected_feed_id = content_hash(feed, omit_key="feed_id")
        except (TypeError, ValueError):
            expected_feed_id = None
            errors.append(f"feed_content_hash_unencodable:{feed_id}")
        if expected_feed_id is not None and feed_id != expected_feed_id:
            errors.append(f"feed_content_hash_mismatch:{feed_id}")

    status = feed.get("status")
    if status != "active":
        errors.append("feed_status_must_be_active")
    created_epoch = _int_between(feed, "created_epoch", errors, minimum=0, maximum=MAX_INT)
    if current_epoch is not None and created_epoch is not None and created_epoch > current_epoch:
        errors.append("feed_created_epoch_in_future")

    query_spec = _mapping(feed, "query_spec", errors)
    source_diversity = _mapping(feed, "source_diversity", errors)
    aggregate_policy = _mapping(feed, "aggregate_policy", errors)

    query = {"query_id": None, "base_asset": None, "quote_asset": None}
    if query_spec is not None:
        query = _validate_query_spec(query_spec, errors)

    policy = {
        "policy_id": None,
        "min_reporters": None,
        "min_sources": None,
        "freshness_window_epochs": None,
        "max_deviation_bps": None,
    }
    if aggregate_policy is not None:
        policy = _validate_aggregate_policy(aggregate_policy, errors)

    source_set_id: str | None = None
    if source_diversity is not None:
        source_result = verify_source_diversity(source_diversity)
        if source_result.status != "accepted":
            errors.append("source_diversity_rejected")
            errors.extend(f"source_diversity:{error}" for error in source_result.errors)
        source_set_id = source_result.source_set_id
        if query["query_id"] is not None and source_result.query_id != query["query_id"]:
            errors.append("source_diversity_query_mismatch")
        if (
            policy["min_sources"] is not None
            and source_result.source_count is not None
            and source_result.source_count < policy["min_sources"]
        ):
            errors.append("source_diversity_below_feed_min_sources")

    return {
        "feed_id": feed_id,
        "query_id": query["query_id"],
        "source_set_id": source_set_id,
        "policy_id": policy["policy_id"],
        "status": status,
    }


def verify_feed_registry(obj: Mapping[str, Any]) -> FeedRegistryResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=REGISTRY_KEYS, label="feed_registry", errors=errors)
    if obj.get("schema") != REGISTRY_SCHEMA:
        errors.append("feed_registry_schema_mismatch")

    registry_id = _hash(obj, "registry_id", errors)
    if registry_id is not None:
        try:
            expected_registry_id = content_hash(obj, omit_key="registry_id")
        except (TypeError, ValueError):
            expected_registry_id = None
            errors.append(f"registry_content_hash_unencodable:{registry_id}")
        if expected_registry_id is not None and registry_id != expected_registry_id:
            errors.append(f"registry_content_hash_mismatch:{registry_id}")

    current_epoch = _int_between(obj, "current_epoch", errors, minimum=0, maximum=MAX_INT)
    feeds = _feeds(obj, errors)

    feed_ids: list[str] = []
    query_ids: list[str] = []
    source_set_ids: list[str] = []
    active_count = 0

    for feed in feeds:
        result = _validate_feed(feed, current_epoch=current_epoch, errors=errors)
        if result["feed_id"] is not None:
            feed_ids.append(str(result["feed_id"]))
        if result["query_id"] is not None:
            query_ids.append(str(result["query_id"]))
        if result["source_set_id"] is not None:
            source_set_ids.append(str(result["source_set_id"]))
        if result["status"] == "active":
            active_count += 1

    for label, values in (
        ("feed_id", feed_ids),
        ("query_id", query_ids),
        ("source_set_id", source_set_ids),
    ):
        duplicates = sorted({value for value in values if values.count(value) > 1})
        for duplicate in duplicates:
            errors.append(f"duplicate_{label}:{duplicate}")

    return FeedRegistryResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        registry_id=registry_id,
        feed_count=len(feeds),
        active_feed_count=active_count,
        query_ids=query_ids,
        feed_ids=feed_ids,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_REGISTRY_BYTES:
        raise ValueError(f"feed_registry_file_too_large:{size}>{MAX_REGISTRY_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("feed registry root must be a JSON object")
    return obj


def _write_result(result: FeedRegistryResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        registry = _load_json(Path(args.registry))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = FeedRegistryResult(status="inconclusive", errors=[f"feed_registry_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_feed_registry(registry)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_feed_registry(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an Oracle feed registry JSON file")
    verify.add_argument("registry", help="path to a feed registry JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted feed registry")
    sample.add_argument("--output", help="optional output path for the sample registry JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
