"""Stable external-output capability for ZRPF identity materialization."""

from __future__ import annotations

import os
import stat
from dataclasses import dataclass
from pathlib import Path

from tools.zrpf_v6_identity_materialization_git import MaterializationError


@dataclass(frozen=True)
class ExternalOutput:
    """Opened parent-directory capability for one absent external output."""

    path: Path
    parent: Path
    name: str
    directory_fd: int
    parent_identity: tuple[int, int, int, int]


def open_absent_external_output(path: Path, repo_root: Path) -> ExternalOutput:
    if not path.is_absolute() or path.exists() or path.is_symlink():
        raise MaterializationError("manifest output must be an absent absolute path")
    parent = path.parent.resolve(strict=True)
    candidate = parent / path.name
    repository = repo_root.resolve(strict=True)
    if candidate != path or candidate == repository or repository in candidate.parents:
        raise MaterializationError("manifest output must be canonical and external")
    flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0)
    )
    try:
        directory_fd = os.open(parent, flags)
    except OSError as exc:
        raise MaterializationError("manifest output parent is unavailable") from exc
    facts = os.fstat(directory_fd)
    if (
        not stat.S_ISDIR(facts.st_mode)
        or facts.st_uid != os.getuid()
        or stat.S_IMODE(facts.st_mode) & 0o022
    ):
        os.close(directory_fd)
        raise MaterializationError("manifest output parent is not private to this UID")
    try:
        os.stat(path.name, dir_fd=directory_fd, follow_symlinks=False)
    except FileNotFoundError:
        pass
    except OSError as exc:
        os.close(directory_fd)
        raise MaterializationError("manifest output absence check failed") from exc
    else:
        os.close(directory_fd)
        raise MaterializationError("manifest output must begin absent")
    return ExternalOutput(
        path=candidate,
        parent=parent,
        name=path.name,
        directory_fd=directory_fd,
        parent_identity=_directory_identity(facts),
    )


def close_external_output(output: ExternalOutput) -> None:
    os.close(output.directory_fd)


def write_external_output(output: ExternalOutput, raw: bytes) -> None:
    _require_external_parent_current(output)
    flags = (
        os.O_WRONLY
        | os.O_CREAT
        | os.O_EXCL
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0)
    )
    descriptor = os.open(
        output.name,
        flags,
        0o600,
        dir_fd=output.directory_fd,
    )
    try:
        with os.fdopen(descriptor, "wb", closefd=False) as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        _require_external_parent_current(output)
        os.fsync(output.directory_fd)
    except BaseException:
        try:
            os.unlink(output.name, dir_fd=output.directory_fd)
        except OSError:
            pass
        raise
    finally:
        os.close(descriptor)


def _directory_identity(facts: os.stat_result) -> tuple[int, int, int, int]:
    return (
        facts.st_dev,
        facts.st_ino,
        facts.st_uid,
        stat.S_IMODE(facts.st_mode),
    )


def _require_external_parent_current(output: ExternalOutput) -> None:
    descriptor_facts = os.fstat(output.directory_fd)
    if (
        not stat.S_ISDIR(descriptor_facts.st_mode)
        or _directory_identity(descriptor_facts) != output.parent_identity
    ):
        raise MaterializationError("manifest output parent descriptor changed")
    try:
        lexical_facts = output.parent.lstat()
        resolved = output.parent.resolve(strict=True)
    except OSError as exc:
        raise MaterializationError("manifest output parent path changed") from exc
    if (
        resolved != output.parent
        or stat.S_ISLNK(lexical_facts.st_mode)
        or not stat.S_ISDIR(lexical_facts.st_mode)
        or _directory_identity(lexical_facts) != output.parent_identity
    ):
        raise MaterializationError("manifest output parent path changed")
