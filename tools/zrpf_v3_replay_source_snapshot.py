"""Private pinned source snapshots for retained ZRPF V3 replay builds."""

from __future__ import annotations

import importlib
import subprocess
from pathlib import Path
from types import TracebackType
from typing import Literal

_MODULE_PREFIX = "tools." if __package__ else ""
environment = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_environment")
process_runner = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_process")

MAX_GIT_OUTPUT = 4 * 1024 * 1024


class SourceSnapshot:
    def __init__(
        self,
        repo_root: Path,
        target_directory: Path,
        commit: str,
        tree: str,
    ) -> None:
        self._repo_root = repo_root
        self._path = target_directory / "source-snapshot"
        self._disabled_hooks = target_directory / "disabled-git-hooks"
        self._commit = commit
        self._tree = tree
        self._added = False

    def __enter__(self) -> Path:
        self._disabled_hooks.mkdir(mode=0o700)
        _run_git(
            [
                "-c",
                f"core.hooksPath={self._disabled_hooks}",
                "worktree",
                "add",
                "--detach",
                str(self._path),
                self._commit,
            ],
            self._repo_root,
        )
        self._added = True
        try:
            self._path.chmod(0o700)
            head = _git_value(["rev-parse", "HEAD^{commit}"], self._path)
            tree = _git_value(["show", "-s", "--format=%T", "HEAD"], self._path)
            if head != self._commit or tree != self._tree:
                raise RuntimeError("private source snapshot identity mismatch")
        except BaseException:
            try:
                self._remove()
            finally:
                raise
        return self._path

    def __exit__(
        self,
        exception_type: type[BaseException] | None,
        _exception: BaseException | None,
        _traceback: TracebackType | None,
    ) -> Literal[False]:
        if not self._added:
            return False
        try:
            self._remove()
        except RuntimeError:
            if exception_type is None:
                raise
        return False

    def _remove(self) -> None:
        _run_git(
            [
                "-c",
                f"core.hooksPath={self._disabled_hooks}",
                "worktree",
                "remove",
                "--force",
                str(self._path),
            ],
            self._repo_root,
        )
        self._added = False


def _git_value(arguments: list[str], cwd: Path) -> str:
    return _run_git(arguments, cwd).stdout.decode("ascii").strip()


def _run_git(
    arguments: list[str],
    cwd: Path,
) -> subprocess.CompletedProcess[bytes]:
    process = process_runner.run_bounded(
        process_runner.ProcessRequest(
            command=("/usr/bin/git", *arguments),
            cwd=cwd,
            env=environment.clean_environment(),
            timeout_seconds=120,
            output_limit_bytes=MAX_GIT_OUTPUT,
            profile=process_runner.ProcessProfile.TOOL,
        )
    )
    if process.returncode != 0:
        raise RuntimeError("Git source snapshot operation failed")
    return process
