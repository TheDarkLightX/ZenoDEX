#!/usr/bin/env python3
"""Verify first-shell Zeno Oracle source diversity receipts."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


SOURCE_DIVERSITY_SCHEMA = "zenodex.oracle.source_diversity.v1"
RESULT_SCHEMA = "zenodex.oracle.source_diversity_verify_result.v1"
MAX_SOURCE_DIVERSITY_BYTES = 500_000
MAX_SOURCES = 64
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
TOP_LEVEL_KEYS = {
    "schema",
    "source_set_id",
    "query_id",
    "min_sources",
    "min_operators",
    "min_venues",
    "min_data_families",
    "min_transports",
    "min_jurisdictions",
    "max_same_operator",
    "max_same_venue",
    "max_same_data_family",
    "max_same_transport",
    "max_same_jurisdiction",
    "sources",
}
SOURCE_KEYS = {
    "source_id",
    "operator_id",
    "venue_id",
    "data_family_id",
    "transport_id",
    "jurisdiction_id",
}
NOT_CLAIMED = [
    "does_not_claim_real_world_source_independence",
    "does_not_claim_source_honesty",
    "does_not_claim_query_semantics_final",
    "does_not_claim_production_oracle_network_live",
]


@dataclass(frozen=True)
class SourceDiversityResult:
    status: str
    errors: list[str]
    source_set_id: str | None = None
    query_id: str | None = None
    source_count: int | None = None
    distinct_operator_count: int | None = None
    distinct_venue_count: int | None = None
    distinct_data_family_count: int | None = None
    distinct_transport_count: int | None = None
    distinct_jurisdiction_count: int | None = None
    max_operator_concentration: int | None = None
    max_venue_concentration: int | None = None
    max_data_family_concentration: int | None = None
    max_transport_concentration: int | None = None
    max_jurisdiction_concentration: int | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "source_set_id": self.source_set_id,
            "query_id": self.query_id,
            "source_count": self.source_count,
            "distinct_operator_count": self.distinct_operator_count,
            "distinct_venue_count": self.distinct_venue_count,
            "distinct_data_family_count": self.distinct_data_family_count,
            "distinct_transport_count": self.distinct_transport_count,
            "distinct_jurisdiction_count": self.distinct_jurisdiction_count,
            "max_operator_concentration": self.max_operator_concentration,
            "max_venue_concentration": self.max_venue_concentration,
            "max_data_family_concentration": self.max_data_family_concentration,
            "max_transport_concentration": self.max_transport_concentration,
            "max_jurisdiction_concentration": self.max_jurisdiction_concentration,
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


def source_set_content_hash(obj: Mapping[str, Any]) -> str:
    body = {key: value for key, value in obj.items() if key != "source_set_id"}
    return "sha256:" + hashlib.sha256(_canonical_json_bytes(body)).hexdigest()


def sample_source_diversity() -> dict[str, Any]:
    receipt = {
        "schema": SOURCE_DIVERSITY_SCHEMA,
        "query_id": sample_hash("zenodex.oracle.query.perps.index_price_e8"),
        "min_sources": 3,
        "min_operators": 3,
        "min_venues": 3,
        "min_data_families": 3,
        "min_transports": 3,
        "min_jurisdictions": 3,
        "max_same_operator": 1,
        "max_same_venue": 1,
        "max_same_data_family": 1,
        "max_same_transport": 1,
        "max_same_jurisdiction": 1,
        "sources": [
            {
                "source_id": "source.dex.pool.local",
                "operator_id": "operator.dex",
                "venue_id": "venue.zenodex",
                "data_family_id": "family.onchain.dex",
                "transport_id": "transport.local.node",
                "jurisdiction_id": "jurisdiction.us",
            },
            {
                "source_id": "source.cex.book.a",
                "operator_id": "operator.cex.a",
                "venue_id": "venue.cex.a",
                "data_family_id": "family.centralized.orderbook",
                "transport_id": "transport.rest.a",
                "jurisdiction_id": "jurisdiction.eu",
            },
            {
                "source_id": "source.index.b",
                "operator_id": "operator.index.b",
                "venue_id": "venue.index.b",
                "data_family_id": "family.index.composite",
                "transport_id": "transport.websocket.b",
                "jurisdiction_id": "jurisdiction.apac",
            },
        ],
    }
    receipt["source_set_id"] = source_set_content_hash(receipt)
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
    minimum: int = 1,
    maximum: int = MAX_SOURCES,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum or value > maximum:
        errors.append(f"{key}_must_be_int_between_{minimum}_and_{maximum}")
        return None
    return int(value)


def _sources(obj: Mapping[str, Any], errors: list[str]) -> list[Mapping[str, Any]]:
    raw = obj.get("sources")
    if not isinstance(raw, list):
        errors.append("sources_must_be_list")
        return []
    if not raw:
        errors.append("sources_must_be_nonempty")
    if len(raw) > MAX_SOURCES:
        errors.append(f"sources_exceed_max:{len(raw)}>{MAX_SOURCES}")
    sources: list[Mapping[str, Any]] = []
    for pos, source in enumerate(raw[:MAX_SOURCES]):
        if not isinstance(source, Mapping):
            errors.append(f"source_{pos}_must_be_object")
            continue
        sources.append(source)
    return sources


def _max_concentration(values: list[str]) -> int:
    if not values:
        return 0
    return max(values.count(value) for value in set(values))


def verify_source_diversity(obj: Mapping[str, Any]) -> SourceDiversityResult:
    errors: list[str] = []
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="source_diversity", errors=errors)
    if obj.get("schema") != SOURCE_DIVERSITY_SCHEMA:
        errors.append("source_diversity_schema_mismatch")

    source_set_id = _hash(obj, "source_set_id", errors)
    if source_set_id is not None:
        try:
            expected_source_set_id = source_set_content_hash(obj)
        except (TypeError, ValueError):
            expected_source_set_id = None
            errors.append(f"source_set_content_hash_unencodable:{source_set_id}")
        if expected_source_set_id is not None and source_set_id != expected_source_set_id:
            errors.append(f"source_set_content_hash_mismatch:{source_set_id}")

    query_id = _hash(obj, "query_id", errors)
    min_sources = _int_between(obj, "min_sources", errors)
    min_operators = _int_between(obj, "min_operators", errors)
    min_venues = _int_between(obj, "min_venues", errors)
    min_data_families = _int_between(obj, "min_data_families", errors)
    min_transports = _int_between(obj, "min_transports", errors)
    min_jurisdictions = _int_between(obj, "min_jurisdictions", errors)
    max_same_operator = _int_between(obj, "max_same_operator", errors)
    max_same_venue = _int_between(obj, "max_same_venue", errors)
    max_same_data_family = _int_between(obj, "max_same_data_family", errors)
    max_same_transport = _int_between(obj, "max_same_transport", errors)
    max_same_jurisdiction = _int_between(obj, "max_same_jurisdiction", errors)
    sources = _sources(obj, errors)

    source_ids: list[str] = []
    operator_ids: list[str] = []
    venue_ids: list[str] = []
    data_family_ids: list[str] = []
    transport_ids: list[str] = []
    jurisdiction_ids: list[str] = []
    for pos, source in enumerate(sources):
        _unknown_fields(source, allowed=SOURCE_KEYS, label=f"source_{pos}", errors=errors)
        source_id = _token(source, "source_id", errors)
        operator_id = _token(source, "operator_id", errors)
        venue_id = _token(source, "venue_id", errors)
        data_family_id = _token(source, "data_family_id", errors)
        transport_id = _token(source, "transport_id", errors)
        jurisdiction_id = _token(source, "jurisdiction_id", errors)
        if source_id is not None:
            source_ids.append(source_id)
        if operator_id is not None:
            operator_ids.append(operator_id)
        if venue_id is not None:
            venue_ids.append(venue_id)
        if data_family_id is not None:
            data_family_ids.append(data_family_id)
        if transport_id is not None:
            transport_ids.append(transport_id)
        if jurisdiction_id is not None:
            jurisdiction_ids.append(jurisdiction_id)

    duplicate_sources = sorted({source_id for source_id in source_ids if source_ids.count(source_id) > 1})
    for source_id in duplicate_sources:
        errors.append(f"duplicate_source_id:{source_id}")

    source_count = len(sources)
    distinct_operator_count = len(set(operator_ids))
    distinct_venue_count = len(set(venue_ids))
    distinct_data_family_count = len(set(data_family_ids))
    distinct_transport_count = len(set(transport_ids))
    distinct_jurisdiction_count = len(set(jurisdiction_ids))
    max_operator_concentration = _max_concentration(operator_ids)
    max_venue_concentration = _max_concentration(venue_ids)
    max_data_family_concentration = _max_concentration(data_family_ids)
    max_transport_concentration = _max_concentration(transport_ids)
    max_jurisdiction_concentration = _max_concentration(jurisdiction_ids)

    if min_sources is not None and source_count < min_sources:
        errors.append("not_enough_sources")
    if min_operators is not None and distinct_operator_count < min_operators:
        errors.append("not_enough_distinct_operators")
    if min_venues is not None and distinct_venue_count < min_venues:
        errors.append("not_enough_distinct_venues")
    if min_data_families is not None and distinct_data_family_count < min_data_families:
        errors.append("not_enough_distinct_data_families")
    if min_transports is not None and distinct_transport_count < min_transports:
        errors.append("not_enough_distinct_transports")
    if min_jurisdictions is not None and distinct_jurisdiction_count < min_jurisdictions:
        errors.append("not_enough_distinct_jurisdictions")
    if max_same_operator is not None and max_operator_concentration > max_same_operator:
        errors.append("operator_concentration_exceeds_policy")
    if max_same_venue is not None and max_venue_concentration > max_same_venue:
        errors.append("venue_concentration_exceeds_policy")
    if max_same_data_family is not None and max_data_family_concentration > max_same_data_family:
        errors.append("data_family_concentration_exceeds_policy")
    if max_same_transport is not None and max_transport_concentration > max_same_transport:
        errors.append("transport_concentration_exceeds_policy")
    if max_same_jurisdiction is not None and max_jurisdiction_concentration > max_same_jurisdiction:
        errors.append("jurisdiction_concentration_exceeds_policy")

    return SourceDiversityResult(
        status="rejected" if errors else "accepted",
        errors=errors,
        source_set_id=source_set_id,
        query_id=query_id,
        source_count=source_count,
        distinct_operator_count=distinct_operator_count,
        distinct_venue_count=distinct_venue_count,
        distinct_data_family_count=distinct_data_family_count,
        distinct_transport_count=distinct_transport_count,
        distinct_jurisdiction_count=distinct_jurisdiction_count,
        max_operator_concentration=max_operator_concentration,
        max_venue_concentration=max_venue_concentration,
        max_data_family_concentration=max_data_family_concentration,
        max_transport_concentration=max_transport_concentration,
        max_jurisdiction_concentration=max_jurisdiction_concentration,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_SOURCE_DIVERSITY_BYTES:
        raise ValueError(f"source_diversity_file_too_large:{size}>{MAX_SOURCE_DIVERSITY_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("source diversity root must be a JSON object")
    return obj


def _write_result(result: SourceDiversityResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        receipt = _load_json(Path(args.receipt))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = SourceDiversityResult(status="inconclusive", errors=[f"source_diversity_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_source_diversity(receipt)
    _write_result(result, Path(args.output) if args.output else None)
    return 0 if result.status == "accepted" else 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_source_diversity(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an Oracle source diversity receipt")
    verify.add_argument("receipt", help="path to a source diversity JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted source diversity receipt")
    sample.add_argument("--output", help="optional output path for the sample receipt JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
