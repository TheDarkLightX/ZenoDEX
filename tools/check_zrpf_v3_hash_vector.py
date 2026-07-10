#!/usr/bin/env python3
"""Independently replay the normative ZRPF V3 leaf hash fixture."""

from __future__ import annotations

import hashlib
import json
from typing import Any


EXPECTED_JOURNAL_HASH = "319ccd083fa38a331c55c3a6239eaaf20ed39efe8025436c2564547d095f77e7"
EXPECTED_POSTCARD_LENGTH = 1547
EXPECTED_POSTCARD_SHA256 = "5c34571084faecc3f0f89258c8127663f9509c199cfeb58feb2babc2a03215fd"
EXPECTED_COMMITMENTS_HASH = "e09e2adba2a02941c0154bf6cb4dc759fc3fd7cd5192756c2c49ec400ca19d5d"

EMPTY_CHILD_DOMAINS = (
    b"zenodex.zrpf.child_tasks_root.v3",
    b"zenodex.zrpf.child_claims_root.v3",
    b"zenodex.zrpf.child_journals_root.v3",
    b"zenodex.zrpf.child_programs_root.v3",
    b"zenodex.zrpf.child_profiles_root.v3",
    b"zenodex.zrpf.child_verifiers_root.v3",
    b"zenodex.zrpf.immediate_verifier_set_root.v3",
    b"zenodex.zrpf.child_statements_root.v3",
    b"zenodex.zrpf.child_manifests_root.v3",
    b"zenodex.zrpf.child_effects_root.v3",
    b"zenodex.zrpf.child_provenance_roots.v3",
    b"zenodex.zrpf.child_data_availability_roots.v3",
)


def _fill(value: int) -> bytes:
    return bytes([value]) * 32


def _indexed_root(seed: int, index: int) -> bytes:
    value = bytearray(_fill(seed))
    value[0] = index
    return bytes(value)


def _write_domain(hasher: Any, domain: bytes) -> None:
    if len(domain) > 0xFFFF:
        raise ValueError("hash domain exceeds u16")
    hasher.update(len(domain).to_bytes(2, "big"))
    hasher.update(domain)


def _empty_list_root(domain: bytes) -> bytes:
    hasher = hashlib.sha256()
    _write_domain(hasher, domain)
    hasher.update((0).to_bytes(4, "big"))
    return hasher.digest()


def _verifier_id() -> bytes:
    hasher = hashlib.sha256()
    _write_domain(hasher, b"zenodex.zrpf.verifier_id.v3")
    hasher.update(_fill(2))
    hasher.update(_fill(240))
    hasher.update((3).to_bytes(2, "big"))
    return hasher.digest()


def _unsigned_varint(value: int) -> bytes:
    encoded = bytearray()
    while value >= 0x80:
        encoded.append((value & 0x7F) | 0x80)
        value >>= 7
    encoded.append(value)
    return bytes(encoded)


def _fixed_field_sequence() -> tuple[bytes, ...]:
    return (
        *(_indexed_root(31, index) for index in range(1, 24)),
        *(_empty_list_root(domain) for domain in EMPTY_CHILD_DOMAINS),
    )


def reference_commitments_hash() -> str:
    hasher = hashlib.sha256()
    _write_domain(hasher, b"zenodex.zrpf.node_commitments_hash.v3")
    for index in range(1, 24):
        hasher.update(_indexed_root(31, index))
    return hasher.hexdigest()


def reference_journal_hash() -> str:
    fields = iter(_fixed_field_sequence())
    hasher = hashlib.sha256()
    _write_domain(hasher, b"zenodex.zrpf.node_journal_hash.v3")
    hasher.update((3).to_bytes(2, "big"))
    hasher.update(_fill(1))  # task_id
    hasher.update(bytes((0, 0)))  # leaf kind, level zero
    hasher.update((10).to_bytes(8, "big"))
    hasher.update((11).to_bytes(8, "big"))
    hasher.update(bytes((0,)))  # immediate child count
    hasher.update((1).to_bytes(8, "big"))
    hasher.update((7).to_bytes(8, "big"))
    hasher.update(_fill(231))  # operation count unit ID
    hasher.update((1).to_bytes(8, "big"))
    hasher.update(_fill(225))  # application_id
    hasher.update(_fill(226))  # domain_id
    hasher.update((10).to_bytes(8, "big"))
    hasher.update((10).to_bytes(8, "big"))
    for value in range(227, 231):
        hasher.update(_fill(value))
    hasher.update(_fill(240))
    hasher.update(_fill(2))
    hasher.update(_verifier_id())
    hasher.update(_fill(4))  # node statement hash
    hasher.update(_fill(5))  # program manifest root
    for field in fields:
        hasher.update(field)
    return hasher.hexdigest()


def reference_postcard_bytes() -> bytes:
    fields = iter(_fixed_field_sequence())
    encoded = bytearray()
    encoded.extend(_unsigned_varint(3))
    encoded.extend(_fill(1))  # task_id
    encoded.extend(_unsigned_varint(0))  # leaf enum variant
    encoded.append(0)  # level
    encoded.extend(_unsigned_varint(10))
    encoded.extend(_unsigned_varint(11))
    encoded.append(0)  # immediate child count
    encoded.extend(_unsigned_varint(1))
    encoded.extend(_unsigned_varint(7))
    encoded.extend(_fill(231))  # operation count unit ID
    encoded.extend(_unsigned_varint(1))
    encoded.extend(_fill(225))  # application_id
    encoded.extend(_fill(226))  # domain_id
    encoded.extend(_unsigned_varint(10))
    encoded.extend(_unsigned_varint(10))
    for value in range(227, 231):
        encoded.extend(_fill(value))
    encoded.extend(_fill(240))
    encoded.extend(_fill(2))
    encoded.extend(_verifier_id())
    encoded.extend(_fill(4))  # node statement hash
    encoded.extend(_fill(5))  # program manifest root
    for field in fields:
        encoded.extend(field)
    return bytes(encoded)


def check() -> dict[str, object]:
    postcard = reference_postcard_bytes()
    commitments_hash = reference_commitments_hash()
    journal_hash = reference_journal_hash()
    postcard_sha256 = hashlib.sha256(postcard).hexdigest()
    checks = {
        "commitments_hash": commitments_hash == EXPECTED_COMMITMENTS_HASH,
        "journal_hash": journal_hash == EXPECTED_JOURNAL_HASH,
        "postcard_length": len(postcard) == EXPECTED_POSTCARD_LENGTH,
        "postcard_sha256": postcard_sha256 == EXPECTED_POSTCARD_SHA256,
    }
    return {
        "ok": all(checks.values()),
        "checks": checks,
        "commitments_hash": commitments_hash,
        "journal_hash": journal_hash,
        "postcard_length": len(postcard),
        "postcard_sha256": postcard_sha256,
    }


def main() -> int:
    report = check()
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
