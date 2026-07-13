"""Trusted run-root creation and report writes for the ZRPF V6 executor."""

from __future__ import annotations

import os
import stat
from pathlib import Path

from tools.zrpf_v6_identity_executor_types import ExecutionError


def prepare_run_root(path: Path, repo_root: Path) -> Path:
    """Create one private run root beneath a stable, trusted parent."""

    if not path.is_absolute():
        raise ExecutionError("run root must be an absent absolute path")
    try:
        parent = path.parent.resolve(strict=True)
        repository = repo_root.resolve(strict=True)
    except OSError as exc:
        raise ExecutionError("run root parent is unavailable") from exc
    candidate = parent / path.name
    if candidate != path or candidate == repository or repository in candidate.parents:
        raise ExecutionError("run root must be canonical and external")
    parent_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0)
    )
    try:
        parent_descriptor = os.open(parent, parent_flags)
    except OSError as exc:
        raise ExecutionError("run root parent is unavailable") from exc
    candidate_descriptor: int | None = None
    created = False
    try:
        parent_identity = _require_trusted_run_parent(parent, parent_descriptor)
        try:
            os.stat(path.name, dir_fd=parent_descriptor, follow_symlinks=False)
        except FileNotFoundError:
            pass
        except OSError as exc:
            raise ExecutionError("run root absence check failed") from exc
        else:
            raise ExecutionError("run root must begin absent")
        os.mkdir(path.name, mode=0o700, dir_fd=parent_descriptor)
        created = True
        candidate_descriptor = os.open(path.name, parent_flags, dir_fd=parent_descriptor)
        _require_private_run_directory(candidate_descriptor, "run root")
        os.mkdir("targets", mode=0o700, dir_fd=candidate_descriptor)
        os.mkdir("outputs", mode=0o700, dir_fd=candidate_descriptor)
        if set(os.listdir(candidate_descriptor)) != {"targets", "outputs"}:
            raise ExecutionError("run root initial inventory mismatch")
        if _require_trusted_run_parent(parent, parent_descriptor) != parent_identity:
            raise ExecutionError("run root parent changed during creation")
    except BaseException:
        if created:
            _remove_partial_run_root(parent_descriptor, candidate_descriptor, path.name)
        raise
    finally:
        if candidate_descriptor is not None:
            os.close(candidate_descriptor)
        os.close(parent_descriptor)
    return candidate


def write_new(path: Path, raw: bytes) -> None:
    """Create and synchronize one report beneath the private run root."""

    parent_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0)
    )
    parent_descriptor = os.open(path.parent, parent_flags)
    descriptor: int | None = None
    try:
        _require_private_run_directory(parent_descriptor, "report output parent")
        descriptor = os.open(
            path.name,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
            0o600,
            dir_fd=parent_descriptor,
        )
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        os.fsync(parent_descriptor)
    finally:
        if descriptor is not None:
            os.close(descriptor)
        os.close(parent_descriptor)


def _require_trusted_run_parent(
    parent: Path,
    descriptor: int,
) -> tuple[int, int, int, int, int]:
    try:
        descriptor_facts = os.fstat(descriptor)
        path_facts = parent.lstat()
    except OSError as exc:
        raise ExecutionError("run root parent identity is unavailable") from exc
    mode = stat.S_IMODE(descriptor_facts.st_mode)
    if (
        not stat.S_ISDIR(descriptor_facts.st_mode)
        or stat.S_ISLNK(path_facts.st_mode)
        or descriptor_facts.st_uid != os.getuid()
        or mode & (stat.S_IWGRP | stat.S_IWOTH)
        or mode & stat.S_ISVTX
        or (descriptor_facts.st_dev, descriptor_facts.st_ino)
        != (path_facts.st_dev, path_facts.st_ino)
    ):
        raise ExecutionError("run root parent ownership or permissions are unsafe")
    return (
        descriptor_facts.st_dev,
        descriptor_facts.st_ino,
        descriptor_facts.st_uid,
        descriptor_facts.st_gid,
        mode,
    )


def _require_private_run_directory(descriptor: int, label: str) -> None:
    try:
        facts = os.fstat(descriptor)
    except OSError as exc:
        raise ExecutionError(f"{label} identity is unavailable") from exc
    if (
        not stat.S_ISDIR(facts.st_mode)
        or facts.st_uid != os.getuid()
        or stat.S_IMODE(facts.st_mode) != 0o700
    ):
        raise ExecutionError(f"{label} identity is unsafe")


def _remove_partial_run_root(
    parent_descriptor: int,
    candidate_descriptor: int | None,
    name: str,
) -> None:
    if candidate_descriptor is not None:
        for child in ("targets", "outputs"):
            try:
                os.rmdir(child, dir_fd=candidate_descriptor)
            except OSError:
                pass
    try:
        os.rmdir(name, dir_fd=parent_descriptor)
    except OSError:
        pass
