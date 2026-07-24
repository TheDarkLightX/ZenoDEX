"""Stable executable and trusted-path handles for the ZRPF jailer."""

from __future__ import annotations

import hashlib
import os
import stat
from dataclasses import dataclass
from pathlib import Path

MAX_EXECUTABLE_BYTES = 64 * 1024 * 1024


class JailerLauncherReject(RuntimeError):
    """Stable fail-closed rejection at the jailer launch boundary."""

    def __init__(self, code: str) -> None:
        super().__init__(code)
        self.code = code


@dataclass(frozen=True, slots=True)
class ExecutableExpectationV1:
    sha256: str
    size_bytes: int

    def __post_init__(self) -> None:
        if (
            type(self.sha256) is not str
            or type(self.size_bytes) is not int
            or len(self.sha256) != 64
            or any(character not in "0123456789abcdef" for character in self.sha256)
            or not 0 < self.size_bytes <= MAX_EXECUTABLE_BYTES
        ):
            raise JailerLauncherReject("jailer_executable_expectation_invalid")


@dataclass(frozen=True, slots=True)
class _OpenedIdentityV1:
    parent_fd: int
    file_fd: int
    file_name: str
    device: int
    inode: int


class PinnedExecutableV1:
    """Open executable plus immutable trusted-parent path identity."""

    def __init__(
        self,
        *,
        path: Path,
        identity: _OpenedIdentityV1,
        expectation: ExecutableExpectationV1,
        trusted_uid: int,
    ) -> None:
        self.path = path
        self._identity = identity
        self._expectation = expectation
        self._trusted_uid = trusted_uid
        self._closed = False

    @property
    def trusted_uid(self) -> int:
        return self._trusted_uid

    def reverify(self) -> None:
        if self._closed:
            raise JailerLauncherReject("jailer_executable_closed")
        current, opened = _restat(self._identity, "jailer_executable_identity_changed")
        expected = (self._identity.device, self._identity.inode)
        if (
            (current.st_dev, current.st_ino) != expected
            or (opened.st_dev, opened.st_ino) != expected
            or opened.st_size != self._expectation.size_bytes
            or not stat.S_ISREG(opened.st_mode)
            or opened.st_uid != self._trusted_uid
            or stat.S_IMODE(opened.st_mode) & 0o022
            or stat.S_IMODE(opened.st_mode) & 0o111 == 0
            or _sha256_fd(self._identity.file_fd) != self._expectation.sha256
        ):
            raise JailerLauncherReject("jailer_executable_identity_changed")

    def close(self) -> None:
        if not self._closed:
            _close_identity(self._identity)
            self._closed = True


def open_pinned_executable(
    *,
    path: Path,
    expectation: ExecutableExpectationV1,
    trusted_root: Path = Path("/"),
    trusted_uid: int = 0,
) -> PinnedExecutableV1:
    identity = _open_under_trusted_root(
        path,
        trusted_root=trusted_root,
        trusted_uid=trusted_uid,
        executable=True,
    )
    try:
        opened = os.fstat(identity.file_fd)
        if (
            opened.st_size != expectation.size_bytes
            or _sha256_fd(identity.file_fd) != expectation.sha256
        ):
            raise JailerLauncherReject("jailer_executable_digest_mismatch")
        return PinnedExecutableV1(
            path=path,
            identity=identity,
            expectation=expectation,
            trusted_uid=trusted_uid,
        )
    except Exception:
        _close_identity(identity)
        raise


def verify_fresh_chroot_target(
    *,
    chroot_base_dir: Path,
    exec_file_path: Path,
    jail_id: str,
    trusted_root: Path = Path("/"),
    trusted_uid: int = 0,
) -> None:
    """Verify the trusted Jailer base and reject its exact stale jail target."""

    if (
        not jail_id
        or "/" in jail_id
        or jail_id in {".", ".."}
        or exec_file_path.name in {"", ".", ".."}
    ):
        raise JailerLauncherReject("jailer_chroot_target_invalid")
    base_fd = _open_directory_under_trusted_root(
        chroot_base_dir,
        trusted_root=trusted_root,
        trusted_uid=trusted_uid,
    )
    try:
        try:
            os.stat(exec_file_path.name, dir_fd=base_fd, follow_symlinks=False)
        except FileNotFoundError:
            return
        exec_fd = _open_directory_at(base_fd, exec_file_path.name, trusted_uid)
        try:
            try:
                os.stat(jail_id, dir_fd=exec_fd, follow_symlinks=False)
            except FileNotFoundError:
                return
            raise JailerLauncherReject("jailer_chroot_target_not_fresh")
        finally:
            os.close(exec_fd)
    finally:
        os.close(base_fd)


def _open_under_trusted_root(
    path: Path,
    *,
    trusted_root: Path,
    trusted_uid: int,
    executable: bool,
) -> _OpenedIdentityV1:
    if not path.is_absolute() or not trusted_root.is_absolute():
        raise JailerLauncherReject("jailer_trusted_path_not_absolute")
    try:
        relative = path.relative_to(trusted_root)
    except ValueError as exc:
        raise JailerLauncherReject("jailer_path_outside_trusted_root") from exc
    if not relative.parts or any(part in {"", ".", ".."} for part in relative.parts):
        raise JailerLauncherReject("jailer_trusted_path_invalid")
    current = _open_trusted_directory(trusted_root, trusted_uid)
    file_fd = -1
    try:
        for component in relative.parts[:-1]:
            child = _open_directory_at(current, component, trusted_uid)
            os.close(current)
            current = child
        file_name = relative.parts[-1]
        before = os.stat(file_name, dir_fd=current, follow_symlinks=False)
        file_fd = os.open(
            file_name,
            os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
            dir_fd=current,
        )
        after = os.fstat(file_fd)
        _require_trusted_file(before, after, trusted_uid, executable)
        return _OpenedIdentityV1(
            parent_fd=current,
            file_fd=file_fd,
            file_name=file_name,
            device=after.st_dev,
            inode=after.st_ino,
        )
    except Exception:
        if file_fd >= 0:
            os.close(file_fd)
        os.close(current)
        raise


def _open_directory_under_trusted_root(
    path: Path,
    *,
    trusted_root: Path,
    trusted_uid: int,
) -> int:
    if not path.is_absolute() or not trusted_root.is_absolute():
        raise JailerLauncherReject("jailer_trusted_path_not_absolute")
    try:
        relative = path.relative_to(trusted_root)
    except ValueError as exc:
        raise JailerLauncherReject("jailer_path_outside_trusted_root") from exc
    if any(part in {"", ".", ".."} for part in relative.parts):
        raise JailerLauncherReject("jailer_trusted_path_invalid")
    current = _open_trusted_directory(trusted_root, trusted_uid)
    try:
        for component in relative.parts:
            child = _open_directory_at(current, component, trusted_uid)
            os.close(current)
            current = child
        return current
    except BaseException:
        os.close(current)
        raise


def _open_trusted_directory(path: Path, trusted_uid: int) -> int:
    try:
        before = path.lstat()
        descriptor = os.open(
            path,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
        )
    except OSError as exc:
        raise JailerLauncherReject("jailer_trusted_directory_open_failed") from exc
    try:
        _require_directory(before, os.fstat(descriptor), trusted_uid)
        return descriptor
    except Exception:
        os.close(descriptor)
        raise


def _open_directory_at(parent_fd: int, name: str, trusted_uid: int) -> int:
    try:
        before = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
        descriptor = os.open(
            name,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
            dir_fd=parent_fd,
        )
    except OSError as exc:
        raise JailerLauncherReject("jailer_trusted_directory_open_failed") from exc
    try:
        _require_directory(before, os.fstat(descriptor), trusted_uid)
        return descriptor
    except Exception:
        os.close(descriptor)
        raise


def _require_directory(before: os.stat_result, after: os.stat_result, trusted_uid: int) -> None:
    if (
        (before.st_dev, before.st_ino, before.st_mode, before.st_uid)
        != (after.st_dev, after.st_ino, after.st_mode, after.st_uid)
        or not stat.S_ISDIR(after.st_mode)
        or after.st_uid != trusted_uid
        or stat.S_IMODE(after.st_mode) & 0o022
    ):
        raise JailerLauncherReject("jailer_trusted_directory_invalid")


def _require_trusted_file(
    before: os.stat_result,
    after: os.stat_result,
    trusted_uid: int,
    executable: bool,
) -> None:
    if (
        (before.st_dev, before.st_ino, before.st_mode, before.st_uid)
        != (after.st_dev, after.st_ino, after.st_mode, after.st_uid)
        or not stat.S_ISREG(after.st_mode)
        or after.st_uid != trusted_uid
        or stat.S_IMODE(after.st_mode) & 0o022
        or (executable and stat.S_IMODE(after.st_mode) & 0o111 == 0)
    ):
        raise JailerLauncherReject("jailer_trusted_file_invalid")


def _restat(
    identity: _OpenedIdentityV1,
    code: str,
) -> tuple[os.stat_result, os.stat_result]:
    try:
        return (
            os.stat(identity.file_name, dir_fd=identity.parent_fd, follow_symlinks=False),
            os.fstat(identity.file_fd),
        )
    except OSError as exc:
        raise JailerLauncherReject(code) from exc


def _sha256_fd(descriptor: int) -> str:
    digest = hashlib.sha256()
    try:
        os.lseek(descriptor, 0, os.SEEK_SET)
        total = 0
        while True:
            chunk = os.read(descriptor, min(1024 * 1024, MAX_EXECUTABLE_BYTES + 1 - total))
            if not chunk:
                return digest.hexdigest()
            total += len(chunk)
            if total > MAX_EXECUTABLE_BYTES:
                raise JailerLauncherReject("jailer_executable_too_large")
            digest.update(chunk)
    except OSError as exc:
        raise JailerLauncherReject("jailer_executable_read_failed") from exc


def _close_identity(identity: _OpenedIdentityV1) -> None:
    os.close(identity.file_fd)
    os.close(identity.parent_fd)
