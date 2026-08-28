#!/usr/bin/env python3
"""Verify one exact O-008A evidence commit E.

V1 has no descendant replay mode. The checked root must be a clean checkout
whose HEAD is E, with E directly adding the artifact to implementation commit
C and C directly adding the implementation to fixed parent P. An external,
immutable launcher must pin these checker bytes before it can make a stronger
bootstrap claim; this Python process cannot authenticate its own startup.
"""

from __future__ import annotations

import argparse
import os
import stat
import sys
from pathlib import Path
from typing import Final, cast

REPO_ROOT: Final = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.build_risc0_build_host_qualification_v1 import (  # noqa: E402
    GitObjectStoreV1,
    GitTreeEntryV1,
    QualificationInputErrorV1,
    collect_qualification_snapshot_v1,
    resource_observation_from_artifact_v1,
    verify_implementation_subject_v1,
)
from tools.risc0_build_host_qualification_v1 import (  # noqa: E402
    ARTIFACT_PATH_V1,
    EXPECTED_PARENT_SHA256_V1,
    MAX_ARTIFACT_BYTES_V1,
    QualificationRejectV1,
    blocked_check_report_v1,
    build_qualification_artifact_v1,
    canonical_json_bytes_v1,
    decode_json_object_v1,
    replay_binding_from_artifact_v1,
    sha256_prefixed_v1,
)

_ARTIFACT_PARENT_COMPONENTS_V1: Final = ("docs", "research")


def _report_v1(
    *,
    status: str,
    artifact_valid: bool,
    findings: list[dict[str, str]],
    evidence: dict[str, object] | None = None,
) -> dict[str, object]:
    report = blocked_check_report_v1(
        status=status,
        artifact_valid=artifact_valid,
        findings=findings,
    )
    if evidence is not None:
        report["exact_evidence"] = evidence
    return report


def _finding_v1(code: str, path: str, detail: str) -> dict[str, str]:
    return {"code": code, "path": path, "detail": detail}


def _clean_tracked_worktree_v1(store: GitObjectStoreV1) -> None:
    """Reject tracked live-file ambiguity before reading the live artifact."""

    _returncode, raw, _stderr = store.run_v1(
        "status",
        "--porcelain=v1",
        "-z",
        "--untracked-files=no",
    )
    if raw:
        raise QualificationInputErrorV1(
            "LIVE_WORKTREE_AMBIGUITY",
            "worktree",
            "tracked paths differ from exact evidence commit E",
        )


def _exact_e_shape_v1(store: GitObjectStoreV1, evidence_commit: str) -> tuple[str, GitTreeEntryV1, bytes]:
    """Return C and E's exact regular artifact blob without history traversal."""

    entries = store.tree_entries_v1(evidence_commit, (ARTIFACT_PATH_V1,))
    if len(entries) != 1:
        raise QualificationInputErrorV1(
            "EVIDENCE_ARTIFACT_MISSING",
            ARTIFACT_PATH_V1,
            "HEAD has no single artifact entry and cannot be E",
        )
    artifact_entry = entries[0]
    if artifact_entry.path != ARTIFACT_PATH_V1:
        raise QualificationInputErrorV1("EVIDENCE_ARTIFACT_MISSING", ARTIFACT_PATH_V1, "fixed path required")
    if artifact_entry.git_mode != "100644" or artifact_entry.object_type != "blob":
        raise QualificationInputErrorV1(
            "ARTIFACT_GIT_MODE",
            ARTIFACT_PATH_V1,
            "E artifact must be a regular Git mode 100644 blob",
        )
    if artifact_entry.size_bytes > MAX_ARTIFACT_BYTES_V1:
        raise QualificationInputErrorV1("ARTIFACT_SIZE_LIMIT", ARTIFACT_PATH_V1, "E artifact exceeds the byte bound")
    parents = store.commit_parents_v1(evidence_commit)
    if len(parents) != 1:
        raise QualificationInputErrorV1("EVIDENCE_COMMIT_SHAPE", evidence_commit, "E requires one direct parent C")
    implementation_commit = parents[0]
    changes = store.diff_name_status_v1(implementation_commit, evidence_commit)
    if changes != (("A", ARTIFACT_PATH_V1),):
        if ("A", ARTIFACT_PATH_V1) in changes:
            code = "EVIDENCE_COMMIT_SHAPE"
            detail = "E may add only the fixed artifact path"
        else:
            code = "DESCENDANT_REPLAY_FORBIDDEN"
            detail = "HEAD is not exact artifact commit E"
        raise QualificationInputErrorV1(code, evidence_commit, detail)
    return implementation_commit, artifact_entry, store.blob_bytes_v1(artifact_entry)


def _live_artifact_bytes_v1(store: GitObjectStoreV1, entry: GitTreeEntryV1) -> bytes:
    """Bind the checked live regular file to E's Git blob after the clean check."""

    directory = store.root
    for component in _ARTIFACT_PARENT_COMPONENTS_V1:
        directory = directory / component
        try:
            metadata = directory.lstat()
        except OSError as exc:
            raise QualificationInputErrorV1("LIVE_ARTIFACT_BINDING", ARTIFACT_PATH_V1, type(exc).__name__) from exc
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
            raise QualificationInputErrorV1(
                "LIVE_ARTIFACT_BINDING",
                ARTIFACT_PATH_V1,
                "artifact parent must be a non-symlink directory",
            )
    no_follow = getattr(os, "O_NOFOLLOW", 0)
    if no_follow == 0:
        raise QualificationInputErrorV1("LIVE_ARTIFACT_BINDING", ARTIFACT_PATH_V1, "platform lacks O_NOFOLLOW")
    try:
        descriptor = os.open(directory / Path(ARTIFACT_PATH_V1).name, os.O_RDONLY | os.O_CLOEXEC | no_follow)
    except OSError as exc:
        raise QualificationInputErrorV1("LIVE_ARTIFACT_BINDING", ARTIFACT_PATH_V1, type(exc).__name__) from exc
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or before.st_size != entry.size_bytes:
            raise QualificationInputErrorV1("LIVE_ARTIFACT_BINDING", ARTIFACT_PATH_V1, "regular exact-size file required")
        chunks: list[bytes] = []
        remaining = entry.size_bytes
        while remaining:
            chunk = os.read(descriptor, min(64 * 1024, remaining))
            if not chunk:
                raise QualificationInputErrorV1("LIVE_ARTIFACT_BINDING", ARTIFACT_PATH_V1, "short read")
            chunks.append(chunk)
            remaining -= len(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns) != (
        after.st_dev,
        after.st_ino,
        after.st_size,
        after.st_mtime_ns,
    ):
        raise QualificationInputErrorV1("LIVE_ARTIFACT_BINDING", ARTIFACT_PATH_V1, "file changed while read")
    raw = b"".join(chunks)
    if raw != store.blob_bytes_v1(entry):
        raise QualificationInputErrorV1("LIVE_ARTIFACT_BINDING", ARTIFACT_PATH_V1, "live bytes differ from E blob")
    return raw


def _replay_exact_e_v1(
    store: GitObjectStoreV1,
    evidence_commit: str,
    *,
    expected_parent: str,
) -> tuple[str, dict[str, object]]:
    """Rebuild C's deterministic blocked projection and return its E binding."""

    implementation_commit, entry, git_raw = _exact_e_shape_v1(store, evidence_commit)
    live_raw = _live_artifact_bytes_v1(store, entry)
    artifact = decode_json_object_v1(git_raw, ARTIFACT_PATH_V1)
    if canonical_json_bytes_v1(artifact) != git_raw:
        raise QualificationInputErrorV1("NONCANONICAL_ARTIFACT", ARTIFACT_PATH_V1, "E blob is not canonical JSON")
    _base_commit, bound_commit, implementation_tree = replay_binding_from_artifact_v1(
        artifact,
        expected_parent=expected_parent,
    )
    if bound_commit != implementation_commit:
        raise QualificationInputErrorV1("ARTIFACT_PARENT", evidence_commit, "artifact must bind direct parent C")
    observed_tree = verify_implementation_subject_v1(
        store,
        implementation_commit,
        expected_parent=expected_parent,
    )
    if observed_tree != implementation_tree:
        raise QualificationInputErrorV1("IMPLEMENTATION_TREE_DRIFT", implementation_commit, "artifact C tree binding differs")
    snapshot = collect_qualification_snapshot_v1(
        store.root,
        implementation_commit=implementation_commit,
        expected_parent=expected_parent,
    )
    resource = resource_observation_from_artifact_v1(artifact)
    expected_artifact = build_qualification_artifact_v1(snapshot, resource=resource)
    if canonical_json_bytes_v1(expected_artifact) != git_raw:
        raise QualificationInputErrorV1("ARTIFACT_PROJECTION_DRIFT", ARTIFACT_PATH_V1, "E blob differs from C projection")
    result = expected_artifact.get("result")
    if type(result) is not dict or type(result.get("status")) is not str:
        raise QualificationInputErrorV1("ARTIFACT_RESULT", "result.status", "typed blocked status required")
    return cast(str, result["status"]), {
        "artifact_blob_oid": entry.blob_oid,
        "artifact_git_mode": entry.git_mode,
        "artifact_sha256": sha256_prefixed_v1(live_raw),
        "artifact_size_bytes": entry.size_bytes,
        "evidence_commit": evidence_commit,
        "implementation_commit": implementation_commit,
    }


def _status_for_reject_v1(code: str) -> str:
    if code == "EVIDENCE_ARTIFACT_MISSING":
        return "REJECTED_ARTIFACT_COMMIT_NOT_FOUND"
    if code == "DESCENDANT_REPLAY_FORBIDDEN":
        return "REJECTED_DESCENDANT_REPLAY"
    if code == "EVIDENCE_COMMIT_SHAPE":
        return "REJECTED_ARTIFACT_COMMIT_SHAPE"
    if code == "ARTIFACT_GIT_MODE":
        return "REJECTED_ARTIFACT_GIT_MODE"
    if code in {"LIVE_ARTIFACT_BINDING", "LIVE_WORKTREE_AMBIGUITY"}:
        return "REJECTED_LIVE_ARTIFACT_AMBIGUITY"
    return "REJECTED_ARTIFACT_BINDING"


def check_risc0_build_host_qualification_v1(
    *,
    root: Path = REPO_ROOT,
    expected_parent: str = EXPECTED_PARENT_SHA256_V1,
) -> dict[str, object]:
    """Fail closed unless the clean checked root is exactly source-bound E."""

    try:
        store = GitObjectStoreV1.open_v1(root)
        _clean_tracked_worktree_v1(store)
        evidence_commit = store.commit_oid_v1("HEAD")
        status, evidence = _replay_exact_e_v1(
            store,
            evidence_commit,
            expected_parent=expected_parent,
        )
        return _report_v1(status=status, artifact_valid=True, findings=[], evidence=evidence)
    except (QualificationInputErrorV1, QualificationRejectV1) as exc:
        return _report_v1(
            status=_status_for_reject_v1(exc.code),
            artifact_valid=False,
            findings=[_finding_v1(exc.code, exc.path, exc.detail)],
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    args = parser.parse_args(argv)
    report = check_risc0_build_host_qualification_v1(root=args.root)
    print(canonical_json_bytes_v1(report).decode("utf-8"))
    return 0 if report["ok"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
