#!/usr/bin/env python3
"""Check the proof-toolchain lock manifest used by ZenoLedger proof metadata."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.proof_toolchain_lock import (  # noqa: E402
    PROOF_TOOLCHAIN_LOCK_SCHEMA_V0,
    build_proof_toolchain_lock_manifest_v0,
    proof_toolchain_lock_hash_v0,
    toolchain_lock_paths_v0,
)
from src.integration.zeno_ledger_v0 import ZERO_ROOT_V0  # noqa: E402


REPORT_SCHEMA = "zenodex/proof_toolchain_lock_check/v0"
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")


def validate_proof_toolchain_lock_manifest_v0(
    manifest: Any,
    *,
    root: Path = ROOT,
) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(manifest, "manifest", errors)
    if obj.get("schema") != PROOF_TOOLCHAIN_LOCK_SCHEMA_V0:
        errors.append("schema mismatch")
    if obj.get("version") != 0:
        errors.append("version must be 0")
    files = _list(obj.get("files"), "files", errors)

    toolchain_paths = toolchain_lock_paths_v0(root)
    expected_group_by_path = {
        path: group
        for group, paths in toolchain_paths
        for path in paths
    }
    expected_paths = {
        path
        for _group, paths in toolchain_paths
        for path in paths
    }
    expected_groups = {group for group, _paths in toolchain_paths}
    seen_paths: set[str] = set()
    seen_groups: set[str] = set()

    for index, raw_entry in enumerate(files):
        entry = _mapping(raw_entry, f"files[{index}]", errors)
        group = _str(entry.get("group"), f"files[{index}].group", errors)
        rel_path = _str(entry.get("path"), f"files[{index}].path", errors)
        size_bytes = _positive_int(entry.get("size_bytes"), f"files[{index}].size_bytes", errors)
        sha256 = _str(entry.get("sha256"), f"files[{index}].sha256", errors)
        if group is not None:
            seen_groups.add(group)
            if group not in expected_groups:
                errors.append(f"files[{index}].group is unexpected: {group}")
        if rel_path is not None:
            if rel_path in seen_paths:
                errors.append(f"files[{index}].path is duplicated: {rel_path}")
            seen_paths.add(rel_path)
            if rel_path not in expected_paths:
                errors.append(f"files[{index}].path is unexpected: {rel_path}")
            elif group is not None and expected_group_by_path[rel_path] != group:
                errors.append(
                    f"files[{index}].group mismatch for {rel_path}: "
                    f"expected {expected_group_by_path[rel_path]}"
                )
            path = root / rel_path
            if not path.is_file():
                errors.append(f"files[{index}].path does not exist: {rel_path}")
            elif size_bytes is not None and path.stat().st_size != size_bytes:
                errors.append(f"files[{index}].size_bytes mismatch for {rel_path}")
            elif sha256 is not None and SHA256_RE.match(sha256) and _file_sha256(path) != sha256:
                errors.append(f"files[{index}].sha256 mismatch for {rel_path}")
        if sha256 is not None and not SHA256_RE.match(sha256):
            errors.append(f"files[{index}].sha256 must be sha256:<64 hex>")

    missing_paths = sorted(expected_paths - seen_paths)
    extra_paths = sorted(seen_paths - expected_paths)
    missing_groups = sorted(expected_groups - seen_groups)
    if missing_paths:
        errors.append(f"missing lock paths: {','.join(missing_paths)}")
    if extra_paths:
        errors.append(f"extra lock paths: {','.join(extra_paths)}")
    if missing_groups:
        errors.append(f"missing lock groups: {','.join(missing_groups)}")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "file_count": len(files),
        "groups": sorted(seen_groups),
        "paths": sorted(seen_paths),
    }


def check_proof_toolchain_lock_v0(root: Path = ROOT) -> dict[str, Any]:
    manifest = build_proof_toolchain_lock_manifest_v0(root)
    validation = validate_proof_toolchain_lock_manifest_v0(manifest, root=root)
    lock_hash = proof_toolchain_lock_hash_v0(root)
    errors = list(validation["errors"])
    if lock_hash == ZERO_ROOT_V0:
        errors.append("proof toolchain lock hash must be non-zero")
    return {
        **validation,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "lock_hash": lock_hash,
        "manifest": manifest,
    }


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if isinstance(value, Mapping):
        return value
    errors.append(f"{name} must be an object")
    return {}


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if isinstance(value, list):
        return value
    errors.append(f"{name} must be a list")
    return []


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if isinstance(value, str) and value:
        return value
    errors.append(f"{name} must be a non-empty string")
    return None


def _positive_int(value: Any, name: str, errors: list[str]) -> int | None:
    if isinstance(value, int) and not isinstance(value, bool) and value > 0:
        return value
    errors.append(f"{name} must be a positive int")
    return None


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def _print_human(report: dict[str, Any]) -> None:
    if report["ok"]:
        print(f"ok {report['lock_hash']}")
        return
    print("error: proof toolchain lock check failed", file=sys.stderr)
    for error in report["errors"]:
        print(f"  - {error}", file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="emit machine-readable report")
    args = parser.parse_args(argv)

    report = check_proof_toolchain_lock_v0(ROOT)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        _print_human(report)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
