"""Stable network-namespace authority for the ZRPF Firecracker jailer."""

from __future__ import annotations

import os
from pathlib import Path

from tools.zrpf_v3_firecracker_trusted_runtime import (
    JailerLauncherReject,
    _close_identity,
    _open_under_trusted_root,
    _OpenedIdentityV1,
    _restat,
)

MAX_MOUNTINFO_BYTES = 4 * 1024 * 1024
MAX_PROC_ENTRIES = 1_048_576


class PinnedNetworkNamespaceV1:
    """Stable nsfs handle whose path and active process membership are checked."""

    def __init__(
        self,
        *,
        path: Path,
        identity: _OpenedIdentityV1,
        proc_root: Path,
        trusted_uid: int,
    ) -> None:
        self.path = path
        self._identity = identity
        self._proc_root = proc_root
        self._trusted_uid = trusted_uid
        self._closed = False

    @property
    def trusted_uid(self) -> int:
        return self._trusted_uid

    def reverify_path(self) -> None:
        if self._closed:
            raise JailerLauncherReject("jailer_netns_closed")
        current, opened = _restat(self._identity, "jailer_netns_identity_changed")
        expected = (self._identity.device, self._identity.inode)
        if (current.st_dev, current.st_ino) != expected or (
            opened.st_dev,
            opened.st_ino,
        ) != expected:
            raise JailerLauncherReject("jailer_netns_identity_changed")

    def verify_process_membership(self, pids: frozenset[int]) -> None:
        """Compatibility name for exact, exclusive namespace membership."""

        self.verify_exact_process_set(pids)

    def verify_empty(self) -> None:
        self.verify_exact_process_set(frozenset())

    def verify_exact_process_set(self, pids: frozenset[int]) -> None:
        if not pids:
            expected: frozenset[int] = frozenset()
        elif any(type(pid) is not int or pid <= 0 for pid in pids):
            raise JailerLauncherReject("jailer_netns_expected_process_set_invalid")
        else:
            expected = pids
        self.reverify_path()
        self._require_expected_members(expected)
        first = self._members_once()
        self.reverify_path()
        second = self._members_once()
        if first != second:
            raise JailerLauncherReject("jailer_netns_process_set_unstable")
        if second != expected:
            raise JailerLauncherReject("jailer_netns_process_set_mismatch")
        self.reverify_path()

    def _require_expected_members(self, pids: frozenset[int]) -> None:
        expected_identity = (self._identity.device, self._identity.inode)
        for pid in sorted(pids):
            try:
                observed = (self._proc_root / str(pid) / "ns" / "net").stat()
            except OSError as exc:
                raise JailerLauncherReject("jailer_netns_process_identity_missing") from exc
            if (observed.st_dev, observed.st_ino) != expected_identity:
                raise JailerLauncherReject("jailer_netns_process_identity_mismatch")

    def _members_once(self) -> frozenset[int]:
        expected_identity = (self._identity.device, self._identity.inode)
        members: set[int] = set()
        scanned = 0
        try:
            entries = os.scandir(self._proc_root)
        except OSError as exc:
            raise JailerLauncherReject("jailer_netns_proc_scan_failed") from exc
        with entries:
            for entry in entries:
                if not entry.name.isascii() or not entry.name.isdigit():
                    continue
                pid = int(entry.name)
                if str(pid) != entry.name or pid <= 0:
                    continue
                scanned += 1
                if scanned > MAX_PROC_ENTRIES:
                    raise JailerLauncherReject("jailer_netns_proc_scan_too_large")
                try:
                    observed = os.stat(
                        self._proc_root / entry.name / "ns" / "net",
                        follow_symlinks=True,
                    )
                except FileNotFoundError:
                    continue
                except OSError as exc:
                    raise JailerLauncherReject("jailer_netns_process_identity_missing") from exc
                if (observed.st_dev, observed.st_ino) == expected_identity:
                    members.add(pid)
        return frozenset(members)

    def close(self) -> None:
        if not self._closed:
            _close_identity(self._identity)
            self._closed = True


def open_pinned_network_namespace(
    *,
    path: Path,
    mountinfo_path: Path = Path("/proc/self/mountinfo"),
    proc_root: Path = Path("/proc"),
    trusted_root: Path = Path("/"),
    trusted_uid: int = 0,
) -> PinnedNetworkNamespaceV1:
    identity = _open_under_trusted_root(
        path,
        trusted_root=trusted_root,
        trusted_uid=trusted_uid,
        executable=False,
    )
    try:
        _require_mount_type(path, os.fstat(identity.file_fd), mountinfo_path, "nsfs")
        value = PinnedNetworkNamespaceV1(
            path=path,
            identity=identity,
            proc_root=proc_root,
            trusted_uid=trusted_uid,
        )
        value.reverify_path()
        return value
    except Exception:
        _close_identity(identity)
        raise


def _require_mount_type(
    path: Path,
    opened: os.stat_result,
    mountinfo_path: Path,
    expected_type: str,
) -> None:
    raw = _read_bounded(mountinfo_path, MAX_MOUNTINFO_BYTES)
    expected_device = f"{os.major(opened.st_dev)}:{os.minor(opened.st_dev)}"
    expected_path = path.as_posix()
    try:
        lines = raw.decode("ascii").splitlines()
    except UnicodeDecodeError as exc:
        raise JailerLauncherReject("jailer_mountinfo_non_ascii") from exc
    for line in lines:
        left, separator, right = line.partition(" - ")
        if not separator:
            continue
        left_fields = left.split()
        right_fields = right.split()
        if (
            len(left_fields) >= 5
            and right_fields
            and left_fields[2] == expected_device
            and _unescape_mountinfo(left_fields[4]) == expected_path
            and right_fields[0] == expected_type
        ):
            return
    raise JailerLauncherReject("jailer_netns_not_nsfs_mount")


def _read_bounded(path: Path, maximum: int) -> bytes:
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0))
    except OSError as exc:
        raise JailerLauncherReject("jailer_boundary_file_open_failed") from exc
    try:
        output = bytearray()
        while len(output) <= maximum:
            chunk = os.read(descriptor, min(65_536, maximum + 1 - len(output)))
            if not chunk:
                return bytes(output)
            output.extend(chunk)
        raise JailerLauncherReject("jailer_boundary_file_too_large")
    finally:
        os.close(descriptor)


def _unescape_mountinfo(value: str) -> str:
    for encoded, decoded in (
        ("\\040", " "),
        ("\\011", "\t"),
        ("\\012", "\n"),
        ("\\134", "\\"),
    ):
        value = value.replace(encoded, decoded)
    return value
