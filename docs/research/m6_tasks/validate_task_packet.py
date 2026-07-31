"""Fail-closed validation for one FCIS M6 task evidence packet."""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any

_DIGEST = re.compile(r"^[0-9a-f]{64}$")
_GIT_SHA = re.compile(r"^(NONE|[0-9a-f]{40})$")
_TASK_ID = re.compile(r"^[A-Z][A-Z0-9]*[0-9]+$")
_STATUS = frozenset(
    {
        "PLANNED",
        "IMPLEMENTED",
        "TESTED",
        "PROVED",
        "MOUNTED",
        "UNMOUNTED",
        "GAP",
        "UNKNOWN",
    }
)


def _fail(message: str) -> None:
    raise SystemExit(f"FAIL: {message}")


def _safe_relative(value: str) -> Path:
    path = Path(value)
    if path.is_absolute() or "\\" in value or ".." in path.parts:
        _fail(f"unsafe repository-relative path: {value!r}")
    if not value or value == ".":
        _fail("empty path")
    return path


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _require_string(mapping: dict[str, Any], key: str) -> str:
    value = mapping.get(key)
    if type(value) is not str or not value:
        _fail(f"{key} must be a nonempty string")
    return value


def _validate_report(report: str, task_id: str) -> None:
    required = (
        f"TASK_ID: {task_id}",
        "BASE_SHA:",
        "SOURCE_HEAD_SHA:",
        "SOURCE_HEAD_TREE:",
        "BRANCH:",
        "FILES_CHANGED:",
        "CLAIM_IMPLEMENTED:",
        "COMMANDS_RUN:",
        "RESULTS:",
        "MUTANTS_ADDED:",
        "FORMAL_EVIDENCE:",
        "REMAINING_NONCLAIMS:",
        "REVIEW_RISKS:",
    )
    for marker in required:
        if marker not in report:
            _fail(f"report is missing marker {marker!r}")


def _validate_evidence(
    evidence: dict[str, Any],
    task_id: str,
    repo_root: Path,
) -> None:
    required = {
        "schema_version",
        "task_id",
        "status",
        "branch",
        "evidence_files",
        "commands",
        "tool_versions",
        "source_hashes",
        "results",
        "mutants",
        "nonclaims",
    }
    missing = required.difference(evidence)
    if missing:
        _fail(f"evidence is missing fields: {sorted(missing)}")
    if evidence["schema_version"] != "zenodex.fcis.m6.task-evidence.v1":
        _fail("wrong evidence schema version")
    if evidence["task_id"] != task_id or not _TASK_ID.fullmatch(task_id):
        _fail("task ID is not canonical")
    if evidence["status"] not in _STATUS:
        _fail("unknown task status")
    for key in ("evidence_files", "commands", "nonclaims", "mutants"):
        if type(evidence[key]) is not list:
            _fail(f"{key} must be a list")
    if type(evidence["results"]) is not dict:
        _fail("results must be an object")
    tool_versions = evidence["tool_versions"]
    if type(tool_versions) is not dict or not tool_versions:
        _fail("tool_versions must be a nonempty object")
    if not all(type(value) is str and value for value in tool_versions.values()):
        _fail("tool_versions values must be nonempty strings")
    source_hashes = evidence["source_hashes"]
    if type(source_hashes) is not dict or not source_hashes:
        _fail("source_hashes must be a nonempty object")
    for raw_path, expected in source_hashes.items():
        path = repo_root / _safe_relative(raw_path)
        if not path.is_file():
            _fail(f"source hash path is missing: {raw_path}")
        if type(expected) is not str or not _DIGEST.fullmatch(expected):
            _fail(f"invalid source hash for {raw_path}")
        if _sha256(path) != expected:
            _fail(f"source hash mismatch for {raw_path}")
    for raw_path in evidence["evidence_files"]:
        path = repo_root / _safe_relative(raw_path)
        if not path.is_file():
            _fail(f"evidence file is missing: {raw_path}")
    base_sha = evidence.get("base_sha", "NONE")
    source_head_sha = evidence.get("source_head_sha", "NONE")
    source_head_tree = evidence.get("source_head_tree", "NONE")
    for name, value in (
        ("base_sha", base_sha),
        ("source_head_sha", source_head_sha),
        ("source_head_tree", source_head_tree),
    ):
        if type(value) is not str or not _GIT_SHA.fullmatch(value):
            _fail(f"{name} is not a canonical Git identity")


def _validate_manifest(manifest: Path, repo_root: Path) -> int:
    seen: set[str] = set()
    count = 0
    for line_number, line in enumerate(manifest.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        fields = line.split()
        if len(fields) != 2:
            _fail(f"manifest line {line_number} is not a sha256sum record")
        expected, raw_path = fields
        path = _safe_relative(raw_path)
        normalized = path.as_posix()
        if normalized in seen:
            _fail(f"duplicate manifest path: {normalized}")
        if normalized == manifest.relative_to(repo_root).as_posix():
            _fail("manifest must not hash itself")
        seen.add(normalized)
        if not _DIGEST.fullmatch(expected):
            _fail(f"invalid manifest digest on line {line_number}")
        target = repo_root / path
        if not target.is_file():
            _fail(f"manifest path is missing: {normalized}")
        if _sha256(target) != expected:
            _fail(f"manifest digest mismatch: {normalized}")
        count += 1
    if count == 0:
        _fail("manifest has no entries")
    return count


def _validate_packet(packet_dir: Path, repo_root: Path, evidence_path: Path) -> int:
    task_id = evidence_path.stem.removeprefix("TASK_").removesuffix("_EVIDENCE")
    report_path = packet_dir / f"TASK_{task_id}_REPORT.md"
    manifest_path = packet_dir / f"TASK_{task_id}_SOURCE_MANIFEST.sha256"
    if not report_path.is_file() or not manifest_path.is_file():
        _fail("report or source manifest is missing")
    try:
        evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        _fail(f"evidence JSON is invalid: {exc}")
    if type(evidence) is not dict:
        _fail("evidence JSON must be an object")
    _validate_report(report_path.read_text(encoding="utf-8"), task_id)
    _validate_evidence(evidence, task_id, repo_root)
    count = _validate_manifest(manifest_path, repo_root)
    print(f"OK: {task_id} report/evidence/manifest validated; {count} manifest entries")
    return count


def main(argv: list[str]) -> int:
    if len(argv) not in (2, 3):
        _fail("usage: validate_task_packet.py <packet-directory> [task-id]")
    packet_dir = Path(argv[1]).resolve()
    if not packet_dir.is_dir() or packet_dir.name != "m6_tasks":
        _fail("packet directory must be an existing m6_tasks directory")
    repo_root = packet_dir.parents[2]
    evidence_paths = sorted(packet_dir.glob("TASK_*_EVIDENCE.json"))
    if len(argv) == 3:
        task_id = argv[2]
        evidence_paths = [packet_dir / f"TASK_{task_id}_EVIDENCE.json"]
        if not evidence_paths[0].is_file():
            _fail(f"task evidence JSON is missing: {task_id}")
    if not evidence_paths:
        _fail("packet directory has no task evidence JSON")
    total_entries = sum(
        _validate_packet(packet_dir, repo_root, evidence_path)
        for evidence_path in evidence_paths
    )
    if len(evidence_paths) > 1:
        print(
            f"OK: validated {len(evidence_paths)} task packets; "
            f"{total_entries} manifest entries"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
