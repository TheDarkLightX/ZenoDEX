"""Bounded Git and filesystem boundary for ZRPF identity materialization."""

from __future__ import annotations

import os
import re
import stat
import subprocess
import tempfile
from pathlib import Path, PurePosixPath
from typing import Mapping, Sequence

from tools.zrpf_v6_identity_source_snapshot import (
    read_bounded_regular,
    replace_regular,
)

MAX_PATCH_BYTES = 2 * 1024 * 1024
MAX_TRANSITION_FILE_BYTES = 1024 * 1024


class MaterializationError(ValueError):
    """Stable fail-closed materialization rejection."""


class MaterializationPartialStateError(MaterializationError):
    """A rejected apply left checkout state requiring operator inspection."""


def require_clean_checkout(repo_root: Path) -> Path:
    root = repo_root.resolve(strict=True)
    require_no_git_replace_refs(root)
    top = git_stdout(root, ["rev-parse", "--show-toplevel"], 4096).decode().strip()
    if Path(top).resolve(strict=True) != root:
        raise MaterializationError("repository root is not the Git worktree root")
    status = git_stdout(
        root,
        ["status", "--porcelain=v1", "-z", "--untracked-files=all"],
        1024 * 1024,
    )
    if status:
        raise MaterializationError("materialization requires a clean checkout and index")
    return root


def canonical_existing_directory(path: Path) -> Path:
    try:
        resolved = path.resolve(strict=True)
        facts = path.lstat()
    except OSError as exc:
        raise MaterializationError("governed run snapshot is unavailable") from exc
    if resolved != path or not stat.S_ISDIR(facts.st_mode) or stat.S_ISLNK(facts.st_mode):
        raise MaterializationError("governed run snapshot path is noncanonical")
    return resolved


def write_new(path: Path, raw: bytes) -> None:
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        path.unlink(missing_ok=True)
        raise
    finally:
        os.close(descriptor)


def build_patch(
    before: Mapping[str, bytes],
    after: Mapping[str, bytes],
    paths: Sequence[str],
) -> bytes:
    expected = set(paths)
    if set(before) != expected or set(after) != expected:
        raise MaterializationError("transition path inventory mismatch")
    if any(before[path] == after[path] for path in paths):
        raise MaterializationError("every governed transition path must change")
    with tempfile.TemporaryDirectory(prefix="zrpf-v6-patch-") as temporary:
        root = Path(temporary)
        git_command(root, ["init", "-q"], maximum_stdout=128)
        for path in paths:
            _write_relative(root, path, before[path])
        git_command(root, ["add", "--all"], maximum_stdout=128)
        for path in paths:
            replace_regular(root.joinpath(*PurePosixPath(path).parts), after[path])
        patch = git_stdout(
            root,
            [
                "diff",
                "--binary",
                "--full-index",
                "--no-ext-diff",
                "--no-renames",
                "--",
                *paths,
            ],
            MAX_PATCH_BYTES,
        )
    if not patch or len(patch) > MAX_PATCH_BYTES:
        raise MaterializationError("generated patch is empty or exceeds its bound")
    _require_exact_patch_paths(patch, paths)
    return patch


def check_patch(repo_root: Path, patch: bytes, source_commit: str) -> None:
    require_checkout_at_source(repo_root, source_commit, require_clean=True)
    _run_git_apply(repo_root, patch, check_only=True)
    require_checkout_at_source(repo_root, source_commit, require_clean=True)


def apply_patch(
    repo_root: Path,
    patch: bytes,
    after: Mapping[str, bytes],
    paths: Sequence[str],
    source_commit: str,
) -> str:
    expected_tree = _expected_materialized_tree(
        repo_root,
        source_commit,
        after,
        paths,
    )
    require_checkout_at_source(repo_root, source_commit, require_clean=True)
    _run_git_apply(repo_root, patch, check_only=False)
    require_checkout_at_source(repo_root, source_commit, require_clean=False)
    staged = git_stdout(
        repo_root,
        ["diff", "--cached", "--name-only", "-z", "--diff-filter=ACMRTUXB"],
        64 * 1024,
    )
    actual_paths = tuple(
        sorted(item.decode("utf-8") for item in staged.split(b"\0") if item)
    )
    if actual_paths != tuple(paths):
        raise MaterializationError("staged materialization path set mismatch")
    if git_stdout(repo_root, ["diff", "--name-only", "-z"], 64 * 1024):
        raise MaterializationError("unstaged changes appeared during materialization")
    status = git_stdout(
        repo_root,
        ["status", "--porcelain=v1", "-z", "--untracked-files=all"],
        1024 * 1024,
    )
    expected_status = tuple(sorted(f"M  {path}".encode("utf-8") for path in paths))
    actual_status = tuple(sorted(item for item in status.split(b"\0") if item))
    if actual_status != expected_status:
        raise MaterializationError("post-apply checkout status contains an extra path")
    git_command(repo_root, ["diff", "--cached", "--check"], maximum_stdout=128)
    _require_index_and_worktree_bytes(repo_root, after, paths)
    actual_tree = git_stdout(repo_root, ["write-tree"], 128).decode("ascii").strip()
    if actual_tree != expected_tree:
        raise MaterializationError("materialized index tree is not C0 plus the exact patch")
    require_checkout_at_source(repo_root, source_commit, require_clean=False)
    return actual_tree


def require_materialized_state(
    repo_root: Path,
    source_commit: str,
    expected_tree: str,
    after: Mapping[str, bytes],
    paths: Sequence[str],
) -> None:
    """Recheck the exact C0-plus-patch state before emitting evidence."""

    require_checkout_at_source(repo_root, source_commit, require_clean=False)
    status = git_stdout(
        repo_root,
        ["status", "--porcelain=v1", "-z", "--untracked-files=all"],
        1024 * 1024,
    )
    expected_status = tuple(sorted(f"M  {path}".encode("utf-8") for path in paths))
    actual_status = tuple(sorted(item for item in status.split(b"\0") if item))
    if actual_status != expected_status:
        raise MaterializationError("materialized checkout changed before evidence emission")
    _require_index_and_worktree_bytes(repo_root, after, paths)
    actual_tree = git_stdout(repo_root, ["write-tree"], 128).decode("ascii").strip()
    if actual_tree != expected_tree:
        raise MaterializationError("materialized index tree changed before evidence emission")


def require_checkout_at_source(
    repo_root: Path,
    source_commit: str,
    *,
    require_clean: bool,
) -> None:
    require_no_git_replace_refs(repo_root)
    head = git_stdout(repo_root, ["rev-parse", "HEAD"], 128).decode("ascii").strip()
    if head != source_commit:
        raise MaterializationError("checkout HEAD differs from the materialization source")
    if require_clean:
        status = git_stdout(
            repo_root,
            ["status", "--porcelain=v1", "-z", "--untracked-files=all"],
            1024 * 1024,
        )
        if status:
            raise MaterializationError("materialization source checkout is not clean")


def git_stdout(root: Path, arguments: list[str], maximum: int) -> bytes:
    return git_command(root, arguments, maximum_stdout=maximum).stdout


def require_no_git_replace_refs(repo_root: Path) -> None:
    refs = git_stdout(
        repo_root,
        ["for-each-ref", "--format=%(refname)", "refs/replace"],
        64 * 1024,
    )
    if refs:
        raise MaterializationError("Git replace refs are forbidden for materialization")


def _require_index_and_worktree_bytes(
    repo_root: Path,
    after: Mapping[str, bytes],
    paths: Sequence[str],
) -> None:
    for path in paths:
        checkout = read_bounded_regular(
            repo_root.joinpath(*PurePosixPath(path).parts),
            f"materialized checkout file {path}",
            MAX_TRANSITION_FILE_BYTES,
        )
        if checkout != after[path]:
            raise MaterializationError("materialized checkout bytes mismatch")
        if git_stdout(repo_root, ["show", f":{path}"], MAX_TRANSITION_FILE_BYTES) != (
            after[path]
        ):
            raise MaterializationError("materialized index bytes mismatch")


def _require_exact_patch_paths(patch: bytes, paths: Sequence[str]) -> None:
    try:
        decoded = patch.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise MaterializationError("generated patch is not UTF-8") from exc
    headers = re.findall(r"^diff --git a/([^ ]+) b/([^\n]+)$", decoded, re.MULTILINE)
    if len(headers) != len(paths):
        raise MaterializationError("generated patch file count mismatch")
    if any(left != right for left, right in headers):
        raise MaterializationError("generated patch contains a rename")
    if tuple(sorted(left for left, _right in headers)) != tuple(paths):
        raise MaterializationError("generated patch path set mismatch")


def _run_git_apply(repo_root: Path, patch: bytes, *, check_only: bool) -> None:
    arguments = ["apply", "--index", "--whitespace=error-all"]
    if check_only:
        arguments.insert(1, "--check")
    git_command(repo_root, arguments, input_bytes=patch, maximum_stdout=128)


def _expected_materialized_tree(
    repo_root: Path,
    source_commit: str,
    after: Mapping[str, bytes],
    paths: Sequence[str],
) -> str:
    if set(after) != set(paths):
        raise MaterializationError("expected-tree path inventory mismatch")
    with tempfile.TemporaryDirectory(prefix="zrpf-v6-index-") as temporary:
        index_path = Path(temporary) / "index"
        environment = {"GIT_INDEX_FILE": str(index_path)}
        git_command(
            repo_root,
            ["read-tree", source_commit],
            maximum_stdout=128,
            environment_overrides=environment,
        )
        for path in paths:
            blob = git_command(
                repo_root,
                ["hash-object", "-w", "--stdin"],
                input_bytes=after[path],
                maximum_stdout=128,
                environment_overrides=environment,
            ).stdout.decode("ascii").strip()
            if not re.fullmatch(r"[0-9a-f]{40,64}", blob):
                raise MaterializationError("materialized blob identity is invalid")
            git_command(
                repo_root,
                ["update-index", "--add", "--cacheinfo", f"100644,{blob},{path}"],
                maximum_stdout=128,
                environment_overrides=environment,
            )
        tree = git_command(
            repo_root,
            ["write-tree"],
            maximum_stdout=128,
            environment_overrides=environment,
        ).stdout.decode("ascii").strip()
    if not re.fullmatch(r"[0-9a-f]{40,64}", tree):
        raise MaterializationError("expected materialized tree identity is invalid")
    return tree


def _write_relative(root: Path, relative: str, raw: bytes) -> None:
    pure = PurePosixPath(relative)
    if pure.is_absolute() or ".." in pure.parts or pure.as_posix() != relative:
        raise MaterializationError("patch source path is noncanonical")
    path = root.joinpath(*pure.parts)
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    write_new(path, raw)


def git_command(
    root: Path,
    arguments: list[str],
    *,
    input_bytes: bytes | None = None,
    maximum_stdout: int,
    environment_overrides: Mapping[str, str] | None = None,
) -> subprocess.CompletedProcess[bytes]:
    environment = {
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "HOME": "/nonexistent",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "TZ": "UTC",
    }
    if environment_overrides is not None:
        if set(environment_overrides) - {"GIT_INDEX_FILE"}:
            raise MaterializationError("unsupported Git environment override")
        environment.update(environment_overrides)
    try:
        completed = subprocess.run(
            [
                "/usr/bin/git",
                "-c",
                "core.fsmonitor=false",
                "-c",
                "core.untrackedCache=false",
                "-c",
                "core.hooksPath=/dev/null",
                "-C",
                str(root),
                *arguments,
            ],
            input=input_bytes,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise MaterializationError("bounded Git materialization command failed") from exc
    if completed.returncode != 0 or completed.stderr:
        raise MaterializationError("bounded Git materialization command rejected")
    if len(completed.stdout) > maximum_stdout:
        raise MaterializationError("bounded Git output exceeds its cap")
    return completed
