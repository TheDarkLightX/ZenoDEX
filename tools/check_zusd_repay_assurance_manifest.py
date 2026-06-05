#!/usr/bin/env python3
"""Fail-closed verifier for pinned ESSO assurance manifests.

REVIEW [C -> A-]: several assurance wrappers imported this shared checker, but
the file was absent in this branch. Restoring it makes the gates executable
again; the checker stays deliberately narrow and hash-based.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "zusd_repay_assurance_manifest.json"


class ManifestError(RuntimeError):
    """Raised when an assurance manifest or pinned report is invalid."""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ManifestError(message)


def _as_mapping(value: Any, context: str) -> Mapping[str, Any]:
    _require(isinstance(value, Mapping), f"{context}: expected object")
    return value


def _repo_file(path_text: str, context: str) -> Path:
    path = Path(path_text)
    _require(not path.is_absolute(), f"{context}: path must be repo-relative")
    resolved = (REPO_ROOT / path).resolve()
    try:
        resolved.relative_to(REPO_ROOT.resolve())
    except ValueError as exc:
        raise ManifestError(f"{context}: path escapes repo: {path_text}") from exc
    _require(resolved.is_file(), f"{context}: missing file: {path_text}")
    return resolved


def _load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ManifestError(f"failed to load JSON {path}: {exc}") from exc


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _check_source_file(entry: Any, index: int) -> None:
    item = _as_mapping(entry, f"source_files[{index}]")
    path_text = str(item.get("path", ""))
    expected = str(item.get("sha256", ""))
    _require(bool(path_text), f"source_files[{index}]: missing path")
    _require(bool(expected), f"source_files[{index}]: missing sha256")
    actual = _sha256_file(_repo_file(path_text, f"source_files[{index}].path"))
    _require(actual == expected, f"source_files[{index}]: sha256 mismatch for {path_text}")


def _check_report(section: Any, name: str) -> None:
    item = _as_mapping(section, name)
    report_path = str(item.get("report_path", ""))
    _require(bool(report_path), f"{name}: missing report_path")
    report = _as_mapping(_load_json(_repo_file(report_path, f"{name}.report_path")), f"{name} report")
    if "ir_hash" in item:
        expected = str(item["ir_hash"])
        _require(
            report.get("ir_hash") in {expected, expected.removeprefix("sha256:")},
            f"{name}: ir_hash mismatch",
        )
    if "verdict" in item:
        _require(report.get("verdict") == item["verdict"], f"{name}: verdict mismatch")
    if "solvers_agreed" in item:
        _require(report.get("solvers_agreed") is item["solvers_agreed"], f"{name}: solvers_agreed mismatch")


def check_manifest(manifest_path: Path) -> None:
    """DbC: every pinned source and replay report must exist and match."""
    manifest = _as_mapping(_load_json(manifest_path), str(manifest_path))
    _require(manifest.get("manifest_version") == 1, "unsupported manifest_version")
    _as_mapping(manifest.get("toolchain"), "toolchain")
    for index, entry in enumerate(list(manifest.get("source_files") or [])):
        _check_source_file(entry, index)
    for section_name in ("validate", "shell_lint", "verify_shell", "verify_multi"):
        if section_name in manifest:
            _check_report(manifest[section_name], section_name)
    for index, path_text in enumerate(list(manifest.get("adapter_regression_tests") or [])):
        _repo_file(str(path_text), f"adapter_regression_tests[{index}]")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    args = parser.parse_args(argv)
    try:
        check_manifest(args.manifest)
    except ManifestError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    print("ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
