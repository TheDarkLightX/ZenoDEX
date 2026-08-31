"""Bounded Git topology and checkout verification for the O-005B V2 ledger."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from tools.operator_surface_registry_common_v2 import (
    HEX_40_V2,
    MAX_JSON_BYTES_V2,
    OperatorSurfaceRegistryRejectV2,
    canonical_json_bytes_v2,
    decode_json_object_v2,
    reject_v2,
    sha256_hex_v2,
)
from tools.operator_surface_registry_git_v2 import (
    _commit_parents_v2,
    _commit_v2,
    _git_blob_v2,
    _git_v2,
    _root_v2,
    _worktree_path_dirty_v2,
)
from tools.value_movement_closure_ledger_v2 import (
    ARTIFACT_RELATIVE_PATH_V2,
    CHECK_SCHEMA_V2,
    EXPECTED_ACTIVE_PLAN_COMMIT_V2,
    NO_AUTHORITY_V2,
    SOURCE_PATHS_V2,
    build_ledger_artifact_from_sources_v2,
    source_manifest_v2,
    validate_ledger_artifact_v2,
)


@dataclass
class _CheckStateV2:
    artifact_sha256: str = ""
    implementation_subject: str = ""
    historical_valid: bool = False
    current_applicable: bool = False


def _source_bytes_v2(root: Path, commit: str) -> dict[str, bytes]:
    return {path: _git_blob_v2(root, commit, path) for path in SOURCE_PATHS_V2}


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
            reject_v2("INDEX_SUPPRESSION", "source_manifest", "invalid encoding")
        if path in rows:
            reject_v2("INDEX_SUPPRESSION", path, "duplicate tracked path")
        rows[path] = marker
    if tuple(rows) != SOURCE_PATHS_V2 or any(marker != "H" for marker in rows.values()):
        reject_v2(
            "INDEX_SUPPRESSION",
            "source_manifest",
            "critical sources must be tracked without index suppression",
        )


def _require_active_plan_ancestor_v2(root: Path, subject: str) -> None:
    code, _raw = _git_v2(
        root,
        "merge-base",
        "--is-ancestor",
        EXPECTED_ACTIVE_PLAN_COMMIT_V2,
        subject,
        allowed_returncodes=(0, 1),
    )
    if code != 0:
        reject_v2(
            "ADMITTED_PLAN_ANCESTRY",
            subject,
            "exact Stage-A subject must descend from the active admitted plan",
        )


def build_ledger_artifact_from_repo_v2(root: Path) -> dict[str, object]:
    resolved = _root_v2(root)
    _require_unsuppressed_sources_v2(resolved)
    if _worktree_path_dirty_v2(resolved, SOURCE_PATHS_V2):
        reject_v2("WORKTREE_SOURCE_DRIFT", "source_manifest", "critical sources are dirty")
    subject = _commit_v2(resolved)
    _require_active_plan_ancestor_v2(resolved, subject)
    return build_ledger_artifact_from_sources_v2(subject, _source_bytes_v2(resolved, subject))


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
        reject_v2("ARTIFACT_UNAVAILABLE", str(ARTIFACT_RELATIVE_PATH_V2), "no artifact commit")
    if HEX_40_V2.fullmatch(value) is None:
        reject_v2("ARTIFACT_TOPOLOGY", str(ARTIFACT_RELATIVE_PATH_V2), "invalid commit")
    return value


def _artifact_only_parent_v2(root: Path, artifact_commit: str) -> str:
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
    if live_raw != committed_raw:
        decoded = decode_json_object_v2(live_raw, str(ARTIFACT_RELATIVE_PATH_V2))
        if canonical_json_bytes_v2(decoded) != live_raw:
            reject_v2("NONCANONICAL_ARTIFACT", str(ARTIFACT_RELATIVE_PATH_V2), "noncanonical")
        reject_v2("WORKTREE_ARTIFACT_DRIFT", str(ARTIFACT_RELATIVE_PATH_V2), "artifact drift")


def _load_historical_v2(root: Path, state: _CheckStateV2) -> dict[str, object]:
    artifact_commit = _artifact_commit_v2(root)
    state.implementation_subject = _artifact_only_parent_v2(root, artifact_commit)
    committed_raw = _git_blob_v2(root, artifact_commit, ARTIFACT_RELATIVE_PATH_V2.as_posix())
    state.artifact_sha256 = sha256_hex_v2(committed_raw)
    _read_checkout_artifact_v2(root / ARTIFACT_RELATIVE_PATH_V2, committed_raw)
    artifact = decode_json_object_v2(committed_raw, str(ARTIFACT_RELATIVE_PATH_V2))
    if canonical_json_bytes_v2(artifact) != committed_raw:
        reject_v2("NONCANONICAL_ARTIFACT", str(ARTIFACT_RELATIVE_PATH_V2), "noncanonical")
    validate_ledger_artifact_v2(artifact)
    if artifact.get("implementation_subject") != state.implementation_subject:
        reject_v2("ARTIFACT_TOPOLOGY", "implementation_subject", "must bind direct parent")
    expected = build_ledger_artifact_from_sources_v2(
        state.implementation_subject,
        _source_bytes_v2(root, state.implementation_subject),
    )
    if artifact != expected:
        reject_v2("ARTIFACT_PROJECTION_DRIFT", str(ARTIFACT_RELATIVE_PATH_V2), "projection drift")
    _require_active_plan_ancestor_v2(root, state.implementation_subject)
    state.historical_valid = True
    return artifact


def _check_current_v2(root: Path, artifact: dict[str, object], state: _CheckStateV2) -> None:
    _require_unsuppressed_sources_v2(root)
    if _worktree_path_dirty_v2(root, SOURCE_PATHS_V2):
        reject_v2("WORKTREE_SOURCE_DRIFT", "source_manifest", "critical sources are dirty")
    head = _commit_v2(root)
    _require_active_plan_ancestor_v2(root, head)
    if source_manifest_v2(_source_bytes_v2(root, head)) != artifact.get("source_manifest"):
        reject_v2("CURRENT_SOURCE_DRIFT", "source_manifest", "current sources differ")
    state.current_applicable = True


def _report_v2(state: _CheckStateV2, findings: list[dict[str, str]]) -> dict[str, object]:
    return {
        "artifact_sha256": state.artifact_sha256,
        "authority": dict(NO_AUTHORITY_V2),
        "closed_value_movement_gate_count": 0,
        "current_applicable": state.current_applicable,
        "current_closure_ledger_gap_closed": state.current_applicable,
        "findings": findings,
        "gate_count": 12,
        "historical_valid": state.historical_valid,
        "implementation_subject": state.implementation_subject,
        "ok": findings == [],
        "schema": CHECK_SCHEMA_V2,
    }


def check_ledger_from_repo_v2(root: Path) -> dict[str, object]:
    state = _CheckStateV2()
    try:
        resolved = _root_v2(root)
        artifact = _load_historical_v2(resolved, state)
        _check_current_v2(resolved, artifact, state)
        return _report_v2(state, [])
    except OperatorSurfaceRegistryRejectV2 as exc:
        return _report_v2(
            state,
            [{"code": exc.code, "detail": exc.detail, "path": exc.path}],
        )
    except Exception:
        return _report_v2(
            state,
            [
                {
                    "code": "CHECKER_INTERNAL_ERROR",
                    "detail": "unexpected failure",
                    "path": "internal",
                }
            ],
        )
