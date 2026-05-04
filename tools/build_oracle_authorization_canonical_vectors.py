#!/usr/bin/env python3
"""Emit deterministic ZenoOracle authorization canonicalization vectors."""

from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.integration.zeno_oracle_authorization import oracle_value_hash, semantic_hash  # noqa: E402
from src.state.canonical import CANONICAL_ENCODING_VERSION, canonical_json_bytes  # noqa: E402


RESULT_SCHEMA = "zenodex.oracle.authorization_canonical_vectors.v1"

AUTHORIZATION_VECTOR: dict[str, Any] = {
    "action_facts_hash": "sha256:2222222222222222222222222222222222222222222222222222222222222222",
    "action_id": "sha256:1111111111111111111111111111111111111111111111111111111111111111",
    "action_kind": "mint",
    "confidence_e8": 10_000,
    "consumer_module": "zenodex.zusd",
    "deviation_bps": 32,
    "economic_envelope_id": "econ:small-notional-v1",
    "evidence_class": "O3",
    "expires_at_epoch": 44,
    "feed_id": "feed:agrs-zdex:v1",
    "feed_registry_root": "sha256:5555555555555555555555555555555555555555555555555555555555555555",
    "observed_epoch": 42,
    "pre_state_hash": "sha256:3333333333333333333333333333333333333333333333333333333333333333",
    "profile_id": "critical-zusd-v1",
    "query_id": "query:AGRS/ZDEX",
    "query_policy_root": "sha256:6666666666666666666666666666666666666666666666666666666666666666",
    "receipt_graph_root": "sha256:9999999999999999999999999999999999999999999999999999999999999999",
    "reporter_registry_root": "sha256:8888888888888888888888888888888888888888888888888888888888888888",
    "source_registry_root": "sha256:7777777777777777777777777777777777777777777777777777777777777777",
    "value_e8": 123_456_789,
    "value_hash": "sha256:4444444444444444444444444444444444444444444444444444444444444444",
}

UNICODE_VECTOR: dict[str, Any] = {
    "description": "UTF-8 canonicalization vector for non-ASCII feed labels",
    "feed_label": "AGRS/ZDEX μ-market",
    "symbols": ["ZΞNO", "Δ", "価格"],
}


def _object_vector(*, name: str, domain: str, payload: dict[str, Any]) -> dict[str, Any]:
    canonical = canonical_json_bytes(payload)
    return {
        "name": name,
        "domain": domain,
        "object": payload,
        "canonical_json_utf8_hex": canonical.hex(),
        "semantic_hash": semantic_hash(domain, payload),
    }


def build_vectors() -> dict[str, Any]:
    return {
        "schema": RESULT_SCHEMA,
        "canonical_encoding_version": CANONICAL_ENCODING_VERSION,
        "vectors": [
            _object_vector(
                name="oracle_authorization_ascii_v1",
                domain="zenodex.oracle.authorization.vector.v1",
                payload=AUTHORIZATION_VECTOR,
            ),
            _object_vector(
                name="oracle_authorization_unicode_utf8_v1",
                domain="zenodex.oracle.authorization.unicode.vector.v1",
                payload=UNICODE_VECTOR,
            ),
        ],
        "value_hash_vector": {
            "query_id": AUTHORIZATION_VECTOR["query_id"],
            "value_e8": AUTHORIZATION_VECTOR["value_e8"],
            "observed_epoch": AUTHORIZATION_VECTOR["observed_epoch"],
            "value_hash": oracle_value_hash(
                query_id=str(AUTHORIZATION_VECTOR["query_id"]),
                value_e8=int(AUTHORIZATION_VECTOR["value_e8"]),
                observed_epoch=int(AUTHORIZATION_VECTOR["observed_epoch"]),
            ),
        },
        "negative_vectors": [
            {
                "name": "float_value_rejected",
                "object": {"value_e8": 1.25},
                "expected_error_contains": "floats are not allowed",
            },
            {
                "name": "non_string_key_rejected",
                "object_repr": "{1: 'not-a-string-key'}",
                "expected_error_contains": "dict keys must be str",
            },
        ],
        "cross_language_rule": (
            "Encode UTF-8 JSON with sorted string keys and compact separators; "
            "reject floats, non-string object keys, NaN/Infinity, and surrogate code points."
        ),
    }


def main() -> int:
    sys.stdout.write(json.dumps(build_vectors(), indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
