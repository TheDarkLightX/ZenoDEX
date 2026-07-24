"""Exact governed-file rollback after a rejected ZRPF materialization."""

from __future__ import annotations

from pathlib import Path, PurePosixPath
from typing import Mapping, Sequence

from tools import zrpf_v6_identity_materialization_git as git_boundary
from tools.zrpf_v6_identity_source_snapshot import read_bounded_regular


def rollback_materialization(
    repo_root: Path,
    source_commit: str,
    patch: bytes,
    before: Mapping[str, bytes],
    after: Mapping[str, bytes],
    paths: Sequence[str],
) -> None:
    """Restore the exact governed files or report persistent partial state."""

    git_boundary.require_checkout_at_source(
        repo_root,
        source_commit,
        require_clean=False,
    )
    state = _classify_governed_bytes(repo_root, before, after, paths)
    if state == "after":
        _run_git_reverse_apply(repo_root, patch)
    elif state != "before":
        raise git_boundary.MaterializationPartialStateError(
            "materialization rejected with mixed governed checkout state"
        )
    if _classify_governed_bytes(repo_root, before, after, paths) != "before":
        raise git_boundary.MaterializationPartialStateError(
            "materialization rejected and governed rollback did not complete"
        )
    status = git_boundary.git_stdout(
        repo_root,
        ["status", "--porcelain=v1", "-z", "--untracked-files=all"],
        1024 * 1024,
    )
    if status:
        raise git_boundary.MaterializationPartialStateError(
            "materialization rejected; governed files were restored but external checkout changes remain"
        )


def _run_git_reverse_apply(repo_root: Path, patch: bytes) -> None:
    git_boundary.git_command(
        repo_root,
        ["apply", "--reverse", "--index", "--whitespace=error-all"],
        input_bytes=patch,
        maximum_stdout=128,
    )


def _classify_governed_bytes(
    repo_root: Path,
    before: Mapping[str, bytes],
    after: Mapping[str, bytes],
    paths: Sequence[str],
) -> str:
    matches_before = True
    matches_after = True
    for path in paths:
        worktree = read_bounded_regular(
            repo_root.joinpath(*PurePosixPath(path).parts),
            f"rollback checkout file {path}",
            git_boundary.MAX_TRANSITION_FILE_BYTES,
        )
        index = git_boundary.git_stdout(
            repo_root,
            ["show", f":{path}"],
            git_boundary.MAX_TRANSITION_FILE_BYTES,
        )
        matches_before &= worktree == before[path] and index == before[path]
        matches_after &= worktree == after[path] and index == after[path]
    if matches_before:
        return "before"
    if matches_after:
        return "after"
    return "mixed"
