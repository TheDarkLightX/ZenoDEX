"""Bounded Git topology and checkout verification for O-004 V2."""

from __future__ import annotations

import os
import subprocess
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Final

from tools.operator_surface_registry_common_v2 import (
    HEX_40_V2,
    MAX_JSON_BYTES_V2,
    OperatorSurfaceRegistryRejectV2,
    canonical_json_bytes_v2,
    decode_json_object_v2,
    reject_v2,
    sha256_hex_v2,
)
from tools.operator_surface_registry_projection_v2 import MAX_SOURCE_BYTES_V2
from tools.operator_surface_registry_v2 import (
    ARTIFACT_RELATIVE_PATH_V2,
    CHECK_SCHEMA_V2,
    NO_AUTHORITY_V2,
    SOURCE_PATHS_V2,
    build_registry_artifact_from_sources_v2,
    source_manifest_v2,
    validate_registry_artifact_v2,
)

MAX_GIT_OUTPUT_BYTES_V2: Final = 8_388_608
GIT_TIMEOUT_SECONDS_V2: Final = 15


@dataclass
class _CheckStateV2:
    artifact_sha256: str = ""
    implementation_subject: str = ""
    historical_valid: bool = False


def _git_environment_v2() -> dict[str, str]:
    environment = {
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_OPTIONAL_LOCKS": "0",
        "GIT_TERMINAL_PROMPT": "0",
        "LANG": "C",
        "LC_ALL": "C",
    }
    path = os.environ.get("PATH")
    if path:
        environment["PATH"] = path
    return environment


def _git_v2(
    root: Path,
    *arguments: str,
    allowed_returncodes: tuple[int, ...] = (0,),
) -> tuple[int, bytes]:
    command = (
        "git",
        "-c",
        "advice.detachedHead=false",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "diff.external=",
        "-C",
        str(root),
        *arguments,
    )
    try:
        result = subprocess.run(
            command,
            check=False,
            capture_output=True,
            env=_git_environment_v2(),
            timeout=GIT_TIMEOUT_SECONDS_V2,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        reject_v2("GIT_EXECUTION", "git", type(exc).__name__)
    if len(result.stdout) > MAX_GIT_OUTPUT_BYTES_V2 or len(result.stderr) > MAX_GIT_OUTPUT_BYTES_V2:
        reject_v2("GIT_OUTPUT_LIMIT", "git", "output exceeds the fixed limit")
    if result.returncode not in allowed_returncodes:
        detail = result.stderr[:512].decode("utf-8", errors="replace")
        reject_v2("GIT_COMMAND", "git", f"exit={result.returncode} {detail}")
    return result.returncode, result.stdout


def _root_v2(root: Path) -> Path:
    try:
        resolved = root.resolve(strict=True)
    except OSError as exc:
        reject_v2("ROOT_PATH", str(root), type(exc).__name__)
    if not resolved.is_dir():
        reject_v2("ROOT_PATH", str(root), "root must be a directory")
    _git_v2(resolved, "rev-parse", "--git-dir")
    _reject_history_overrides_v2(resolved)
    return resolved


def _reject_history_overrides_v2(root: Path) -> None:
    _code, replacements = _git_v2(root, "for-each-ref", "--format=%(refname)", "refs/replace")
    if replacements.strip():
        reject_v2("GIT_HISTORY_OVERRIDE", "refs/replace", "replacement refs are forbidden")
    _code, raw_path = _git_v2(root, "rev-parse", "--git-path", "info/grafts")
    try:
        decoded = raw_path.decode("utf-8").strip()
    except UnicodeDecodeError:
        reject_v2("GIT_HISTORY_OVERRIDE", "info/grafts", "invalid graft path")
    graft_path = Path(decoded)
    if not graft_path.is_absolute():
        graft_path = root / graft_path
    try:
        if graft_path.is_file() and graft_path.stat().st_size > 0:
            reject_v2("GIT_HISTORY_OVERRIDE", "info/grafts", "grafts are forbidden")
    except OSError as exc:
        reject_v2("GIT_HISTORY_OVERRIDE", "info/grafts", type(exc).__name__)


def _commit_v2(root: Path, revision: str = "HEAD") -> str:
    _code, raw = _git_v2(root, "rev-parse", "--verify", f"{revision}^{{commit}}")
    try:
        value = raw.decode("ascii").strip()
    except UnicodeDecodeError:
        reject_v2("GIT_COMMIT", revision, "commit identity is not ASCII")
    if HEX_40_V2.fullmatch(value) is None:
        reject_v2("GIT_COMMIT", revision, "expected one full SHA-1 commit identity")
    return value


def _git_blob_v2(root: Path, commit: str, relative_path: str) -> bytes:
    pure = PurePosixPath(relative_path)
    if pure.is_absolute() or ".." in pure.parts or str(pure) != relative_path:
        reject_v2("SOURCE_PATH", relative_path, "path must be canonical and relative")
    _code, tree_raw = _git_v2(root, "ls-tree", "-z", commit, "--", relative_path)
    entries = tuple(entry for entry in tree_raw.split(b"\0") if entry)
    if len(entries) != 1 or b"\t" not in entries[0]:
        reject_v2("GIT_SOURCE_MODE", relative_path, "expected one tree entry")
    metadata, encoded_path = entries[0].split(b"\t", 1)
    fields = metadata.split(b" ")
    try:
        decoded_path = encoded_path.decode("utf-8")
        object_id = fields[2].decode("ascii") if len(fields) == 3 else ""
    except UnicodeDecodeError:
        reject_v2("GIT_SOURCE_MODE", relative_path, "invalid tree entry encoding")
    if (
        fields[:2] != [b"100644", b"blob"]
        or len(fields) != 3
        or HEX_40_V2.fullmatch(object_id) is None
        or decoded_path != relative_path
    ):
        reject_v2("GIT_SOURCE_MODE", relative_path, "must be one regular non-executable blob")
    _code, raw = _git_v2(root, "cat-file", "blob", f"{commit}:{relative_path}")
    if len(raw) > MAX_SOURCE_BYTES_V2:
        reject_v2("SOURCE_SIZE", relative_path, "source exceeds the fixed byte limit")
    return raw


def _source_bytes_v2(root: Path, commit: str) -> dict[str, bytes]:
    return {path: _git_blob_v2(root, commit, path) for path in SOURCE_PATHS_V2}


def _worktree_path_dirty_v2(root: Path, paths: tuple[str, ...]) -> bool:
    _code, raw = _git_v2(
        root,
        "status",
        "--porcelain=v1",
        "-z",
        "--untracked-files=all",
        "--",
        *paths,
    )
    return raw != b""


def _require_unsuppressed_sources_v2(root: Path) -> None:
    _code, raw = _git_v2(root, "ls-files", "-v", "-z", "--", *SOURCE_PATHS_V2)
    rows: dict[str, str] = {}
    for entry in (part for part in raw.split(b"\0") if part):
        if len(entry) < 3 or entry[1:2] != b" ":
            reject_v2("INDEX_SUPPRESSION", "source_manifest", "invalid ls-files row")
        try:
            marker = entry[:1].decode("ascii")
            path = entry[2:].decode("utf-8")
        except UnicodeDecodeError:
            reject_v2("INDEX_SUPPRESSION", "source_manifest", "invalid ls-files encoding")
        if path in rows:
            reject_v2("INDEX_SUPPRESSION", path, "duplicate tracked path")
        rows[path] = marker
    if tuple(rows) != SOURCE_PATHS_V2 or any(marker != "H" for marker in rows.values()):
        reject_v2(
            "INDEX_SUPPRESSION",
            "source_manifest",
            "critical sources must be tracked without skip-worktree or assume-unchanged",
        )


def build_registry_artifact_from_repo_v2(root: Path) -> dict[str, object]:
    resolved = _root_v2(root)
    _require_unsuppressed_sources_v2(resolved)
    if _worktree_path_dirty_v2(resolved, SOURCE_PATHS_V2):
        reject_v2("WORKTREE_SOURCE_DRIFT", "source_manifest", "critical sources are dirty")
    subject = _commit_v2(resolved)
    return build_registry_artifact_from_sources_v2(subject, _source_bytes_v2(resolved, subject))


def _artifact_commit_v2(root: Path) -> str:
    _code, raw = _git_v2(
        root,
        "log",
        "-n",
        "1",
        "--format=%H",
        "--",
        ARTIFACT_RELATIVE_PATH_V2.as_posix(),
    )
    try:
        value = raw.decode("ascii").strip()
    except UnicodeDecodeError:
        reject_v2("ARTIFACT_TOPOLOGY", str(ARTIFACT_RELATIVE_PATH_V2), "invalid commit")
    if value == "":
        reject_v2("ARTIFACT_UNAVAILABLE", str(ARTIFACT_RELATIVE_PATH_V2), "no committed artifact")
    if HEX_40_V2.fullmatch(value) is None:
        reject_v2("ARTIFACT_TOPOLOGY", str(ARTIFACT_RELATIVE_PATH_V2), "invalid commit")
    return value


def _commit_parents_v2(root: Path, commit: str) -> tuple[str, ...]:
    _code, raw = _git_v2(root, "cat-file", "-p", commit)
    parents: list[str] = []
    for line in raw.splitlines():
        if line.startswith(b"parent "):
            try:
                candidate = line[7:].decode("ascii")
            except UnicodeDecodeError:
                reject_v2("ARTIFACT_TOPOLOGY", commit, "invalid parent encoding")
            if HEX_40_V2.fullmatch(candidate) is None:
                reject_v2("ARTIFACT_TOPOLOGY", commit, "invalid parent identity")
            parents.append(candidate)
        elif line == b"":
            break
    return tuple(parents)


def _artifact_only_child_v2(root: Path, artifact_commit: str) -> str:
    parents = _commit_parents_v2(root, artifact_commit)
    if len(parents) != 1:
        reject_v2("ARTIFACT_TOPOLOGY", artifact_commit, "artifact commit must have one parent")
    parent = parents[0]
    _code, raw = _git_v2(
        root,
        "diff",
        "--name-only",
        "-z",
        "--no-renames",
        parent,
        artifact_commit,
        "--",
    )
    try:
        paths = tuple(part.decode("utf-8") for part in raw.split(b"\0") if part)
    except UnicodeDecodeError:
        reject_v2("ARTIFACT_TOPOLOGY", artifact_commit, "non-UTF-8 changed path")
    if paths != (ARTIFACT_RELATIVE_PATH_V2.as_posix(),):
        reject_v2("ARTIFACT_TOPOLOGY", artifact_commit, "Stage B must change only the artifact")
    return parent


def _read_checkout_artifact_v2(path: Path, committed_raw: bytes) -> None:
    if path.is_symlink() or not path.is_file():
        reject_v2("ARTIFACT_WORKTREE_TYPE", str(ARTIFACT_RELATIVE_PATH_V2), "must be regular")
    try:
        if path.stat().st_size > MAX_JSON_BYTES_V2:
            reject_v2("JSON_SIZE", str(ARTIFACT_RELATIVE_PATH_V2), "artifact is oversized")
        live_raw = path.read_bytes()
    except OSError as exc:
        reject_v2("ARTIFACT_WORKTREE_TYPE", str(ARTIFACT_RELATIVE_PATH_V2), type(exc).__name__)
    if live_raw == committed_raw:
        return
    live = decode_json_object_v2(live_raw, str(ARTIFACT_RELATIVE_PATH_V2))
    if canonical_json_bytes_v2(live) != live_raw:
        reject_v2("NONCANONICAL_ARTIFACT", str(ARTIFACT_RELATIVE_PATH_V2), "noncanonical")
    reject_v2("WORKTREE_ARTIFACT_DRIFT", str(ARTIFACT_RELATIVE_PATH_V2), "artifact drift")


def _load_historical_v2(root: Path, state: _CheckStateV2) -> dict[str, object]:
    artifact_commit = _artifact_commit_v2(root)
    state.implementation_subject = _artifact_only_child_v2(root, artifact_commit)
    committed_raw = _git_blob_v2(root, artifact_commit, ARTIFACT_RELATIVE_PATH_V2.as_posix())
    state.artifact_sha256 = sha256_hex_v2(committed_raw)
    _read_checkout_artifact_v2(root / ARTIFACT_RELATIVE_PATH_V2, committed_raw)
    artifact = decode_json_object_v2(committed_raw, str(ARTIFACT_RELATIVE_PATH_V2))
    if canonical_json_bytes_v2(artifact) != committed_raw:
        reject_v2("NONCANONICAL_ARTIFACT", str(ARTIFACT_RELATIVE_PATH_V2), "noncanonical")
    validate_registry_artifact_v2(artifact)
    if artifact.get("implementation_subject") != state.implementation_subject:
        reject_v2("ARTIFACT_TOPOLOGY", "implementation_subject", "must bind direct parent")
    expected = build_registry_artifact_from_sources_v2(
        state.implementation_subject,
        _source_bytes_v2(root, state.implementation_subject),
    )
    if artifact != expected:
        reject_v2("ARTIFACT_PROJECTION_DRIFT", str(ARTIFACT_RELATIVE_PATH_V2), "projection drift")
    state.historical_valid = True
    return artifact


def _check_current_v2(root: Path, artifact: dict[str, object]) -> None:
    _require_unsuppressed_sources_v2(root)
    if _worktree_path_dirty_v2(root, SOURCE_PATHS_V2):
        reject_v2("WORKTREE_SOURCE_DRIFT", "source_manifest", "critical sources are dirty")
    head = _commit_v2(root)
    current_manifest = source_manifest_v2(_source_bytes_v2(root, head))
    if current_manifest != artifact.get("source_manifest"):
        reject_v2("CURRENT_SOURCE_DRIFT", "source_manifest", "current sources differ")


def _report_v2(
    state: _CheckStateV2,
    *,
    ok: bool,
    findings: list[dict[str, str]],
    current_applicable: bool,
) -> dict[str, object]:
    return {
        "artifact_sha256": state.artifact_sha256,
        "authority": dict(NO_AUTHORITY_V2),
        "current_applicable": current_applicable,
        "findings": findings,
        "historical_valid": state.historical_valid,
        "implementation_subject": state.implementation_subject,
        "ok": ok,
        "runtime_test_execution": "OUTSIDE_DETERMINISTIC_ARTIFACT",
        "schema": CHECK_SCHEMA_V2,
        "vm_gates_closed": [],
    }


def check_registry_from_repo_v2(root: Path) -> dict[str, object]:
    state = _CheckStateV2()
    try:
        resolved = _root_v2(root)
        artifact = _load_historical_v2(resolved, state)
        _check_current_v2(resolved, artifact)
    except OperatorSurfaceRegistryRejectV2 as exc:
        return _report_v2(
            state,
            ok=False,
            findings=[{"code": exc.code, "path": exc.path, "detail": exc.detail}],
            current_applicable=False,
        )
    except (MemoryError, OSError, RecursionError, TypeError, ValueError) as exc:
        return _report_v2(
            state,
            ok=False,
            findings=[
                {"code": "CHECKER_INPUT_ERROR", "path": str(root), "detail": type(exc).__name__}
            ],
            current_applicable=False,
        )
    return _report_v2(state, ok=True, findings=[], current_applicable=True)


__all__ = ["build_registry_artifact_from_repo_v2", "check_registry_from_repo_v2"]
