#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Mapping


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "recompute_batch_proof_boundary_assurance_manifest.json"


class ManifestError(RuntimeError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ManifestError(message)


def _as_dict(obj: Any, *, ctx: str) -> Mapping[str, Any]:
    _require(isinstance(obj, dict), f"{ctx}: expected object")
    return obj


def _load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        raise ManifestError(f"failed to read JSON {path}: {exc}") from exc


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _check_source_files(entries: list[Mapping[str, Any]]) -> None:
    for entry in entries:
        rel = str(entry["path"])
        expected = str(entry["sha256"])
        path = REPO_ROOT / rel
        _require(path.is_file(), f"missing source/test file: {rel}")
        actual = _sha256_file(path)
        _require(actual == expected, f"source hash mismatch for {rel}: {actual} != {expected}")


def _check_regression_report(entry: Mapping[str, Any], regression_tests: list[str]) -> None:
    report_path = REPO_ROOT / str(entry["report_path"])
    report = _as_dict(_load_json(report_path), ctx=str(report_path))
    _require(report.get("schema") == entry["schema"], f"{report_path}: schema mismatch")
    _require(bool(report.get("ok", False)), f"{report_path}: ok=false")
    _require(int(report.get("returncode", -1)) == 0, f"{report_path}: returncode mismatch")
    _require(report.get("command") == entry["command"], f"{report_path}: command mismatch")
    _require(report.get("tests") == entry["tests"], f"{report_path}: tests mismatch")
    _require(report.get("tests") == regression_tests, f"{report_path}: regression_tests drift")
    _require(int(report.get("passed", -1)) == int(entry["passed"]), f"{report_path}: passed mismatch")
    _require(int(report.get("failed", -1)) == int(entry["failed"]), f"{report_path}: failed mismatch")
    _require(int(report.get("errors", -1)) == int(entry["errors"]), f"{report_path}: errors mismatch")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate the pinned recompute-batch proof-boundary assurance manifest.")
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    args = parser.parse_args(argv)

    manifest_path = args.manifest.resolve()
    manifest = _as_dict(_load_json(manifest_path), ctx=str(manifest_path))
    _require(int(manifest.get("manifest_version", -1)) == 1, "manifest_version mismatch")

    source_files = manifest.get("source_files")
    _require(isinstance(source_files, list) and source_files, "source_files must be a non-empty list")
    _check_source_files([_as_dict(entry, ctx="source_files[]") for entry in source_files])

    regression_tests_obj = manifest.get("regression_tests")
    _require(isinstance(regression_tests_obj, list) and regression_tests_obj, "regression_tests must be a non-empty list")
    regression_tests = [str(rel) for rel in regression_tests_obj]
    for rel in regression_tests:
        path = REPO_ROOT / rel
        _require(path.is_file(), f"missing regression test file: {rel}")

    _check_regression_report(_as_dict(manifest.get("regression_report"), ctx="regression_report"), regression_tests)

    print("ok")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main(sys.argv[1:]))
    except ManifestError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
