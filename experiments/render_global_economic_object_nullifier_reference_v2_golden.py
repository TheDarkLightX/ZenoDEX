#!/usr/bin/env python3
"""Render quarantined fixed vectors for the V2 nullifier reference oracle.

This renderer deliberately does not import the implementation under test. It
prints deterministic JSON by default and fails closed when ``--check`` differs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Sequence

SCHEMA = "zenodex/global-economic-object-nullifier-reference/v2"
GOLDEN_SCHEMA = "zenodex/global-economic-object-nullifier-reference-golden/v1"
DIGEST_PREFIX = b"global-economic-object-nullifier-reference\x002\x00"
MAX_ENTRIES = 4_096
MAX_CLAIMS = 64
MAX_BYTES = 1_048_576


def _identifier(number: int) -> str:
    if number <= 0 or number >= 2**256:
        raise ValueError("fixture identifier must be in 1..2^256-1")
    return f"0x{number:064x}"


def _entry(object_number: int, occurrence_number: int) -> dict[str, str]:
    return {
        "object_id": _identifier(object_number),
        "first_consumed_by_occurrence_id": _identifier(occurrence_number),
    }


def _claim(object_number: int, occurrence_number: int) -> dict[str, str]:
    return {
        "object_id": _identifier(object_number),
        "consumed_by_occurrence_id": _identifier(occurrence_number),
    }


def _canonical_bytes(entries: list[dict[str, str]]) -> bytes:
    ordered = sorted(entries, key=lambda row: bytes.fromhex(row["object_id"][2:]))
    value = {"schema": SCHEMA, "entries": ordered}
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    ).encode("utf-8")


def _digest(entries: list[dict[str, str]]) -> str:
    return "0x" + hashlib.sha256(DIGEST_PREFIX + _canonical_bytes(entries)).hexdigest()


def _accepted(
    pre_entries: list[dict[str, str]], claims: list[dict[str, str]]
) -> dict[str, object]:
    post = list(pre_entries)
    post.extend(
        _entry(
            int(claim["object_id"], 16),
            int(claim["consumed_by_occurrence_id"], 16),
        )
        for claim in claims
    )
    canonical = _canonical_bytes(post)
    return {
        "kind": "accepted",
        "post_canonical_json": canonical.decode("utf-8"),
        "post_entries": sorted(post, key=lambda row: row["object_id"]),
        "post_reference_archive_digest": "0x"
        + hashlib.sha256(DIGEST_PREFIX + canonical).hexdigest(),
    }


def _vector(
    name: str,
    pre_entries: list[dict[str, str]],
    claims: list[dict[str, str]],
    *,
    reject_code: str | None = None,
) -> dict[str, object]:
    canonical = _canonical_bytes(pre_entries)
    expected: dict[str, object]
    if reject_code is None:
        expected = _accepted(pre_entries, claims)
    else:
        expected = {"code": reject_code, "kind": "rejected"}
    return {
        "name": name,
        "pre_entries": sorted(pre_entries, key=lambda row: row["object_id"]),
        "pre_canonical_json": canonical.decode("utf-8"),
        "pre_reference_archive_digest": _digest(pre_entries),
        "claims": claims,
        "expected": expected,
    }


def render() -> bytes:
    vectors = [
        _vector("empty_identity", [], []),
        _vector("insert_one", [], [_claim(1, 101)]),
        _vector("insert_two_reverse", [], [_claim(2, 102), _claim(1, 101)]),
        _vector(
            "duplicate_in_batch",
            [],
            [_claim(1, 101), _claim(1, 102)],
            reject_code="REFERENCE_DUPLICATE_IN_BATCH",
        ),
        _vector(
            "already_consumed",
            [_entry(1, 101)],
            [_claim(1, 102)],
            reject_code="REFERENCE_ALREADY_CONSUMED",
        ),
    ]
    payload = {
        "schema": GOLDEN_SCHEMA,
        "reference_schema": SCHEMA,
        "digest_prefix_hex": DIGEST_PREFIX.hex(),
        "limits": {
            "max_archive_bytes": MAX_BYTES,
            "max_claims_per_step": MAX_CLAIMS,
            "max_nullifiers": MAX_ENTRIES,
        },
        "vectors": vectors,
    }
    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    rendered = render()
    if args.check is None:
        sys.stdout.buffer.write(rendered)
        return 0
    try:
        observed = args.check.read_bytes()
    except OSError as exc:
        print(f"golden check failed: {exc}", file=sys.stderr)
        return 1
    if observed != rendered:
        print(f"golden drift: {args.check}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
