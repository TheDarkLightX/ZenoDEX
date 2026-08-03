"""Fail-closed validation for one FCIS M6 task evidence packet."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterator, NoReturn

_DIGEST = re.compile(r"^[0-9a-f]{64}$")
_GIT_SHA = re.compile(r"^(NONE|[0-9a-f]{40})$")
_GIT_COMMIT = re.compile(r"^[0-9a-f]{40}$")
_TASK_ID = re.compile(r"^[A-Z][A-Z0-9]*[0-9]+$")
_REPORT_IDENTITY = re.compile(
    r"^(BASE_SHA|SOURCE_HEAD_SHA|SOURCE_HEAD_TREE|BRANCH|"
    r"IMPLEMENTATION_HEAD_SHA|IMPLEMENTATION_TREE|IMPLEMENTATION_PARENT|"
    r"DEPENDENCY_REFRESH_HEAD|DEPENDENCY_REFRESH_TREE|"
    r"DEPENDENCY_REFRESH_PARENT):"
    r"\s*`?([^`\s]+)"
)
_REPORT_FUNCTIONAL_IDENTITY = re.compile(r"^-\s*(commit|tree|parent):\s*`?([^`\s]+)")
_COMMIT_FIELDS = frozenset(
    {
        "base_sha",
        "source_head_sha",
        "implementation_commit",
        "implementation_parent",
        "dependency_refresh_commit",
        "integration_head",
        "merged_d04_head",
        "implementation_head_sha",
        "functional_commit",
        "functional_head_sha",
        "source_commit",
        "source_head_commit",
        "packet_commit",
    }
)
_TREE_FIELDS = frozenset(
    {
        "source_head_tree",
        "implementation_tree",
        "dependency_refresh_tree",
        "integration_tree",
        "functional_tree",
        "source_tree",
        "packet_tree",
    }
)
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


def _fail(message: str) -> NoReturn:
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


def _validate_report(report: str, task_id: str) -> dict[str, str]:
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
    identities: dict[str, str] = {}
    functional_head = False
    for line in report.splitlines():
        stripped = line.strip()
        match = _REPORT_IDENTITY.fullmatch(stripped)
        if match is not None:
            identities[match.group(1)] = match.group(2)
        if stripped == "FUNCTIONAL_HEAD:":
            functional_head = True
            continue
        if functional_head:
            nested = _REPORT_FUNCTIONAL_IDENTITY.fullmatch(stripped)
            if nested is not None:
                identities[f"FUNCTIONAL_HEAD_{nested.group(1).upper()}"] = nested.group(2)
            elif stripped and not stripped.startswith("-"):
                functional_head = False
    return identities


def _git(repo_root: Path, *arguments: str) -> str:
    try:
        completed = subprocess.run(
            ["git", "-C", str(repo_root), *arguments],
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError as exc:
        _fail(f"Git identity resolution could not start: {exc}")
    if completed.returncode != 0:
        detail = completed.stderr.strip() or "no Git diagnostic"
        _fail(f"Git identity resolution failed for {arguments!r}: {detail}")
    return completed.stdout.strip()


def _validate_git_commit(repo_root: Path, value: str, field: str) -> None:
    if value == "NONE":
        return
    if not _GIT_COMMIT.fullmatch(value):
        _fail(f"{field} is not a full Git commit identity")
    resolved = _git(repo_root, "rev-parse", f"{value}^{{commit}}")
    if resolved != value:
        _fail(f"{field} does not resolve to the declared commit")


def _validate_git_tree(repo_root: Path, value: str, field: str) -> None:
    if value == "NONE":
        return
    if not _GIT_COMMIT.fullmatch(value):
        _fail(f"{field} is not a full Git tree identity")
    object_type = _git(repo_root, "cat-file", "-t", value)
    if object_type != "tree":
        _fail(f"{field} does not resolve to a Git tree")


def _validate_commit_tree(
    repo_root: Path,
    commit: str,
    tree: str,
    field: str,
) -> None:
    _validate_git_commit(repo_root, commit, f"{field} commit")
    _validate_git_tree(repo_root, tree, f"{field} tree")
    if commit == "NONE" or tree == "NONE":
        return
    actual_tree = _git(repo_root, "rev-parse", f"{commit}^{{tree}}")
    if actual_tree != tree:
        _fail(
            f"{field} commit/tree mismatch: commit {commit} has tree {actual_tree}, declared {tree}"
        )


def _identity_kind(field: str, value: object) -> str | None:
    if type(value) is not str:
        return None
    if field in _TREE_FIELDS or field.endswith("_tree"):
        if value == "NONE" or _GIT_COMMIT.fullmatch(value):
            return "tree"
        return None
    if field in _COMMIT_FIELDS:
        return "commit"
    if field.endswith(("_commit", "_parent", "_head")):
        if value == "NONE" or _GIT_COMMIT.fullmatch(value):
            return "commit"
    return None


def _declared_identities(value: object) -> Iterator[tuple[str, str, str]]:
    if isinstance(value, dict):
        for key, child in value.items():
            if type(key) is str:
                kind = _identity_kind(key, child)
                if kind is not None and type(child) is str:
                    yield key, child, kind
            yield from _declared_identities(child)
    elif isinstance(value, list):
        for child in value:
            yield from _declared_identities(child)


def _tree_counterpart(field: str) -> str | None:
    if field == "source_head_sha":
        return "source_head_tree"
    if field == "implementation_head_sha":
        return "implementation_tree"
    if field == "merged_d04_head":
        return "merge_tree"
    if field.endswith("_commit"):
        return f"{field.removesuffix('_commit')}_tree"
    if field.endswith("_head"):
        return f"{field.removesuffix('_head')}_tree"
    return None


def _validate_git_lineage(
    evidence: dict[str, Any],
    repo_root: Path,
    expected_head: str | None,
) -> None:
    identities = list(_declared_identities(evidence))
    fields: dict[str, str] = {field: value for field, value, _kind in identities}
    commits: set[str] = set()
    for field, value, kind in identities:
        if value == "NONE":
            continue
        if kind == "commit":
            _validate_git_commit(repo_root, value, field)
            commits.add(value)
        else:
            _validate_git_tree(repo_root, value, field)
    for field, value, kind in identities:
        if kind != "commit" or value == "NONE":
            continue
        tree_field = _tree_counterpart(field)
        if tree_field is None:
            continue
        tree = fields.get(tree_field)
        if tree is not None:
            _validate_commit_tree(repo_root, value, tree, field)
    if expected_head is None:
        return
    _validate_git_commit(repo_root, expected_head, "expected packet head")
    for commit in sorted(commits):
        result = subprocess.run(
            [
                "git",
                "-C",
                str(repo_root),
                "merge-base",
                "--is-ancestor",
                commit,
                expected_head,
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode != 0:
            _fail(
                f"declared commit {commit} is not an ancestor of expected "
                f"packet head {expected_head}"
            )


def _evidence_identity(evidence: dict[str, Any], key: str) -> str | None:
    evidence_value: object = evidence.get(key)
    if type(evidence_value) is str:
        return evidence_value
    results = evidence.get("results")
    if isinstance(results, dict):
        result_value: object = results.get(key)
        if type(result_value) is str:
            return result_value
    return None


def _validate_report_bindings(report_identities: dict[str, str], evidence: dict[str, Any]) -> None:
    mapping = {
        "BASE_SHA": "base_sha",
        "SOURCE_HEAD_SHA": "source_head_sha",
        "SOURCE_HEAD_TREE": "source_head_tree",
        "BRANCH": "branch",
        "IMPLEMENTATION_HEAD_SHA": "implementation_commit",
        "IMPLEMENTATION_TREE": "implementation_tree",
        "IMPLEMENTATION_PARENT": "implementation_parent",
        "DEPENDENCY_REFRESH_HEAD": "dependency_refresh_commit",
        "DEPENDENCY_REFRESH_TREE": "dependency_refresh_tree",
        "DEPENDENCY_REFRESH_PARENT": "dependency_refresh_parent",
        "FUNCTIONAL_HEAD_COMMIT": "implementation_commit",
        "FUNCTIONAL_HEAD_TREE": "implementation_tree",
        "FUNCTIONAL_HEAD_PARENT": "implementation_parent",
    }
    for report_key, evidence_key in mapping.items():
        report_value = report_identities.get(report_key)
        if report_value is None:
            continue
        evidence_value = _evidence_identity(evidence, evidence_key)
        if evidence_value is None:
            _fail(f"report identity {report_key} has no evidence field {evidence_key}")
        if report_value != evidence_value:
            _fail(
                f"report/evidence identity mismatch for {report_key}: "
                f"report {report_value}, evidence {evidence_value}"
            )


def _validate_identity_shapes(value: object) -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if type(key) is str and (key in _COMMIT_FIELDS or key in _TREE_FIELDS):
                if type(child) is not str or not _GIT_SHA.fullmatch(child):
                    _fail(f"{key} is not a canonical Git identity")
            _validate_identity_shapes(child)
    elif isinstance(value, list):
        for child in value:
            _validate_identity_shapes(child)


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
    _validate_identity_shapes(evidence)


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


def _validate_packet(
    packet_dir: Path,
    repo_root: Path,
    evidence_path: Path,
    expected_head: str | None,
) -> int:
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
    report_identities = _validate_report(report_path.read_text(encoding="utf-8"), task_id)
    _validate_evidence(evidence, task_id, repo_root)
    _validate_report_bindings(report_identities, evidence)
    _validate_git_lineage(evidence, repo_root, expected_head)
    count = _validate_manifest(manifest_path, repo_root)
    print(f"OK: {task_id} report/evidence/manifest validated; {count} manifest entries")
    return count


def _parse_arguments(argv: list[str]) -> tuple[str, str | None, str | None]:
    positional: list[str] = []
    expected_head: str | None = None
    index = 1
    while index < len(argv):
        argument = argv[index]
        if argument == "--expected-head":
            if expected_head is not None or index + 1 >= len(argv):
                _fail("--expected-head requires exactly one value")
            expected_head = argv[index + 1]
            index += 2
            continue
        if argument.startswith("--expected-head="):
            if expected_head is not None:
                _fail("--expected-head was supplied more than once")
            expected_head = argument.removeprefix("--expected-head=")
            index += 1
            continue
        if argument.startswith("--"):
            _fail(f"unknown option: {argument}")
        positional.append(argument)
        index += 1
    if len(positional) not in (1, 2):
        _fail(
            "usage: validate_task_packet.py <packet-directory> [task-id] [--expected-head <commit>]"
        )
    if expected_head is not None and not _GIT_COMMIT.fullmatch(expected_head):
        _fail("--expected-head must be a full 40-character Git commit")
    task_id = positional[1] if len(positional) == 2 else None
    return positional[0], task_id, expected_head


def main(argv: list[str]) -> int:
    packet_directory, requested_task, expected_head = _parse_arguments(argv)
    packet_dir = Path(packet_directory).resolve()
    if not packet_dir.is_dir() or packet_dir.name != "m6_tasks":
        _fail("packet directory must be an existing m6_tasks directory")
    repo_root = packet_dir.parents[2]
    evidence_paths = sorted(packet_dir.glob("TASK_*_EVIDENCE.json"))
    if requested_task is not None:
        task_id = requested_task
        evidence_paths = [packet_dir / f"TASK_{task_id}_EVIDENCE.json"]
        if not evidence_paths[0].is_file():
            _fail(f"task evidence JSON is missing: {task_id}")
    if not evidence_paths:
        _fail("packet directory has no task evidence JSON")
    total_entries = sum(
        _validate_packet(packet_dir, repo_root, evidence_path, expected_head)
        for evidence_path in evidence_paths
    )
    if len(evidence_paths) > 1:
        print(f"OK: validated {len(evidence_paths)} task packets; {total_entries} manifest entries")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
