#!/usr/bin/env python3
"""Replay the exact research-only O-003B retired Tau bridge inventory."""

from __future__ import annotations

import argparse
import json
import os
import stat
import sys
from pathlib import Path
from typing import Final, Mapping

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.build_retired_tau_bridge_inventory_v1 import build_inventory_object_v1  # noqa: E402
from tools.retired_tau_bridge_inventory_v1 import (  # noqa: E402
    CHECK_SCHEMA_V1,
    CLASSIFICATIONS_V1,
    EXPECTED_ARTIFACT_SHA256_V1,
    INVENTORY_PATH_V1,
    MAX_ARTIFACT_BYTES_V1,
    SCHEMA_V1,
    InventoryRejectV1,
    canonical_json_bytes_v1,
    reject_v1,
    sha256_prefixed_v1,
)

_TOP_LEVEL_KEYS_V1: Final = frozenset(
    {
        "authority",
        "candidate_fingerprint",
        "dependencies",
        "inventory_subject",
        "mutation_cases",
        "nonclaims",
        "route_static_guard_evidence",
        "schema",
        "scope_contract",
        "scope_summary",
        "source_scope_root",
        "startup_refusal_evidence",
        "status",
        "vm_gates_closed",
    }
)


def _duplicate_keys_rejector_v1(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            reject_v1("DUPLICATE_JSON_KEY", key)
        result[key] = value
    return result


def _decode_artifact_v1(raw: bytes) -> dict[str, object]:
    if len(raw) > MAX_ARTIFACT_BYTES_V1:
        reject_v1("ARTIFACT_TOO_LARGE", INVENTORY_PATH_V1.as_posix())
    try:
        value = json.loads(
            raw.decode(),
            object_pairs_hook=_duplicate_keys_rejector_v1,
            parse_constant=lambda token: reject_v1("INVALID_JSON_CONSTANT", token),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        reject_v1("INVALID_JSON", type(exc).__name__)
    if type(value) is not dict:
        reject_v1("ARTIFACT_NOT_OBJECT", type(value).__name__)
    return value


def validate_inventory_object_v1(
    value: Mapping[str, object],
    *,
    expected: Mapping[str, object],
) -> dict[str, object]:
    if type(value) is not dict or set(value) != _TOP_LEVEL_KEYS_V1:
        reject_v1("ARTIFACT_SCHEMA_MISMATCH", "top-level")
    if value.get("schema") != SCHEMA_V1:
        reject_v1("ARTIFACT_SCHEMA_MISMATCH", "schema")
    if value.get("status") != "RESEARCH_ONLY_NO_PROMOTION":
        reject_v1("STATUS_PROMOTION_FORBIDDEN", repr(value.get("status")))
    if value.get("authority") != {
        "production": "NONE",
        "release": "NONE",
        "settlement": "NONE",
        "value_movement": "NONE",
    }:
        reject_v1("AUTHORITY_PROMOTION_FORBIDDEN", repr(value.get("authority")))
    if value.get("vm_gates_closed") != []:
        reject_v1("VM_GATE_PROMOTION_FORBIDDEN", repr(value.get("vm_gates_closed")))
    raw_dependencies = value.get("dependencies")
    if type(raw_dependencies) is not list:
        reject_v1("DEPENDENCIES_NOT_LIST", type(raw_dependencies).__name__)
    dependencies: list[object] = raw_dependencies
    identifiers: list[str] = []
    for index, raw_row in enumerate(dependencies):
        if type(raw_row) is not dict:
            reject_v1("DEPENDENCY_NOT_OBJECT", str(index))
        row: dict[str, object] = raw_row
        classification, identifier = row.get("classification"), row.get("dependency_id")
        if classification not in CLASSIFICATIONS_V1:
            reject_v1("INVALID_CLASSIFICATION", str(index))
        if type(identifier) is not str or not identifier:
            reject_v1("INVALID_DEPENDENCY_ID", str(index))
        identifiers.append(identifier)
    if identifiers != sorted(identifiers) or len(identifiers) != len(set(identifiers)):
        reject_v1("DEPENDENCY_ORDER_OR_DUPLICATE", "dependencies")
    if value != expected:
        reject_v1("SUBJECT_REPLAY_MISMATCH", "artifact")
    return dict(value)


def validate_inventory_bytes_v1(raw: bytes, *, root: Path) -> dict[str, object]:
    value = _decode_artifact_v1(raw)
    if canonical_json_bytes_v1(value) != raw:
        reject_v1("NONCANONICAL_ARTIFACT", INVENTORY_PATH_V1.as_posix())
    if EXPECTED_ARTIFACT_SHA256_V1 == "UNSET":
        reject_v1("CHECKER_EXPECTATION_UNSET", "artifact-sha256")
    digest = sha256_prefixed_v1(raw)
    if digest != EXPECTED_ARTIFACT_SHA256_V1:
        reject_v1("ARTIFACT_DIGEST_MISMATCH", digest)
    return validate_inventory_object_v1(value, expected=build_inventory_object_v1(root))


def _read_artifact_v1(path: Path) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        before = path.lstat()
        if stat.S_ISLNK(before.st_mode) or not stat.S_ISREG(before.st_mode) or before.st_size > MAX_ARTIFACT_BYTES_V1:
            raise InventoryRejectV1("ARTIFACT_NOT_BOUNDED_REGULAR_FILE", str(path))
        descriptor = os.open(path, flags)
        opened = os.fstat(descriptor)
        if (opened.st_dev, opened.st_ino) != (before.st_dev, before.st_ino):
            raise InventoryRejectV1("ARTIFACT_CHANGED_DURING_READ", str(path))
        raw = os.read(descriptor, MAX_ARTIFACT_BYTES_V1 + 1)
        after = path.lstat()
    except OSError as exc:
        raise InventoryRejectV1("ARTIFACT_READ_FAILED", type(exc).__name__) from exc
    finally:
        if "descriptor" in locals():
            os.close(descriptor)
    if len(raw) != before.st_size or (after.st_dev, after.st_ino, after.st_mtime_ns) != (
        before.st_dev,
        before.st_ino,
        before.st_mtime_ns,
    ):
        reject_v1("ARTIFACT_CHANGED_DURING_READ", str(path))
    return raw


def _failure_report(code: str, detail: str) -> dict[str, object]:
    return {
        "artifact_sha256": "",
        "classifications": [],
        "dependency_count": 0,
        "findings": [{"code": code, "detail": detail}],
        "ok": False,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": CHECK_SCHEMA_V1,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }


def check_retired_tau_bridge_inventory_v1(root: Path) -> dict[str, object]:
    try:
        raw = _read_artifact_v1(root / INVENTORY_PATH_V1)
        artifact = validate_inventory_bytes_v1(raw, root=root)
    except InventoryRejectV1 as exc:
        return _failure_report(exc.code, exc.detail)
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        return _failure_report("CHECKER_INPUT_ERROR", type(exc).__name__)
    dependencies = artifact["dependencies"]
    if type(dependencies) is not list:
        return _failure_report("DEPENDENCIES_NOT_LIST", type(dependencies).__name__)
    return {
        "artifact_sha256": sha256_prefixed_v1(raw),
        "classifications": sorted({str(row["classification"]) for row in dependencies}),
        "dependency_count": len(dependencies),
        "findings": [],
        "ok": True,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "schema": CHECK_SCHEMA_V1,
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    report = check_retired_tau_bridge_inventory_v1(parser.parse_args(argv).root)
    print(json.dumps(report, sort_keys=True))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
