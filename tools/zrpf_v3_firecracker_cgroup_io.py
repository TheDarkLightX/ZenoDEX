"""Descriptor-relative cgroup and procfs I/O for the ZRPF jailer control."""

from __future__ import annotations

import os
import stat
from pathlib import Path

from tools.zrpf_v3_firecracker_cgroup_contract import CgroupV2Reject

MAX_CONTROL_BYTES = 64 * 1024
MAX_MOUNTINFO_BYTES = 4 * 1024 * 1024


def open_trusted_directory(path: Path, *, trusted_uid: int) -> int:
    if not path.is_absolute():
        raise CgroupV2Reject("cgroup_mount_path_not_absolute")
    try:
        before = path.lstat()
        descriptor = os.open(
            path,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
        )
    except OSError as exc:
        raise CgroupV2Reject("cgroup_mount_open_failed") from exc
    try:
        _require_trusted_directory(before, os.fstat(descriptor), trusted_uid)
        return descriptor
    except Exception:
        os.close(descriptor)
        raise


def walk_directories(root_fd: int, components: tuple[str, ...], *, trusted_uid: int) -> int:
    current = os.dup(root_fd)
    try:
        for component in components:
            child = open_directory_at(current, component, trusted_uid=trusted_uid)
            os.close(current)
            current = child
        return current
    except Exception:
        os.close(current)
        raise


def open_directory_at(parent_fd: int, name: str, *, trusted_uid: int) -> int:
    try:
        before = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
        descriptor = os.open(
            name,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
            dir_fd=parent_fd,
        )
    except OSError as exc:
        raise CgroupV2Reject("cgroup_directory_open_failed") from exc
    try:
        _require_trusted_directory(before, os.fstat(descriptor), trusted_uid)
        return descriptor
    except Exception:
        os.close(descriptor)
        raise


def require_cgroup2_mount(
    mount_path: Path,
    mount_fd: int,
    opened: os.stat_result,
    mountinfo_path: Path,
) -> None:
    raw = read_bounded_path(mountinfo_path, MAX_MOUNTINFO_BYTES)
    expected_device = f"{os.major(opened.st_dev)}:{os.minor(opened.st_dev)}"
    try:
        descriptor_path = os.readlink(f"/proc/self/fd/{mount_fd}")
    except OSError as exc:
        raise CgroupV2Reject("cgroup_mount_descriptor_path_unavailable") from exc
    if descriptor_path != mount_path.as_posix():
        raise CgroupV2Reject("cgroup_mount_path_identity_changed")
    try:
        lines = raw.decode("ascii").splitlines()
    except UnicodeDecodeError as exc:
        raise CgroupV2Reject("cgroup_mountinfo_non_ascii") from exc
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
            and _unescape_mountinfo(left_fields[4]) == descriptor_path
            and right_fields[0] == "cgroup2"
        ):
            return
    raise CgroupV2Reject("cgroup_mount_not_cgroup_v2")


def read_value(directory_fd: int, name: str) -> str:
    raw = _read_at(directory_fd, name)
    try:
        return raw.decode("ascii").rstrip("\n")
    except UnicodeDecodeError as exc:
        raise CgroupV2Reject("cgroup_control_non_ascii") from exc


def write_control(directory_fd: int, name: str, raw: bytes) -> None:
    _require_control_name(name)
    if not raw or len(raw) > MAX_CONTROL_BYTES or b"\x00" in raw:
        raise CgroupV2Reject("cgroup_control_write_invalid")
    try:
        descriptor = os.open(
            name,
            os.O_WRONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_TRUNC", 0),
            dir_fd=directory_fd,
        )
    except OSError as exc:
        raise CgroupV2Reject("cgroup_control_open_failed") from exc
    try:
        view = memoryview(raw)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise CgroupV2Reject("cgroup_control_short_write")
            view = view[written:]
    except OSError as exc:
        raise CgroupV2Reject("cgroup_control_write_failed") from exc
    finally:
        os.close(descriptor)


def read_pids(directory_fd: int) -> frozenset[int]:
    text = read_value(directory_fd, "cgroup.procs")
    if not text:
        return frozenset()
    try:
        values = [int(line) for line in text.splitlines()]
    except ValueError as exc:
        raise CgroupV2Reject("cgroup_process_list_invalid") from exc
    if any(value <= 0 for value in values) or len(values) != len(set(values)):
        raise CgroupV2Reject("cgroup_process_list_invalid")
    return frozenset(values)


def keyed_integer(directory_fd: int, name: str, key: str) -> int:
    rows: dict[str, int] = {}
    for line in read_value(directory_fd, name).splitlines():
        fields = line.split()
        if len(fields) != 2 or fields[0] in rows:
            raise CgroupV2Reject("cgroup_keyed_file_invalid")
        try:
            rows[fields[0]] = int(fields[1])
        except ValueError as exc:
            raise CgroupV2Reject("cgroup_keyed_file_invalid") from exc
    if key not in rows or rows[key] < 0:
        raise CgroupV2Reject("cgroup_keyed_file_invalid")
    return rows[key]


def read_process_cgroup(proc_root: Path, pid: int) -> str:
    raw = read_bounded_path(proc_root / str(pid) / "cgroup", MAX_CONTROL_BYTES)
    try:
        rows = raw.decode("ascii").splitlines()
    except UnicodeDecodeError as exc:
        raise CgroupV2Reject("cgroup_process_membership_file_invalid") from exc
    matches = [row[3:] for row in rows if row.startswith("0::")]
    if len(matches) != 1 or not matches[0].startswith("/"):
        raise CgroupV2Reject("cgroup_process_membership_file_invalid")
    return matches[0]


def is_descendant(
    pid: int,
    supervisor_pid: int,
    allowed_pids: frozenset[int],
    identities: dict[int, tuple[int, int]],
) -> bool:
    seen: set[int] = set()
    current = pid
    while current != supervisor_pid:
        if current in seen or current not in allowed_pids or current not in identities:
            return False
        seen.add(current)
        current = identities[current][0]
    return True


def read_process_identities(
    proc_root: Path,
    pids: frozenset[int],
) -> dict[int, tuple[int, int]]:
    return {pid: _read_process_identity(proc_root, pid) for pid in sorted(pids)}


def read_bounded_path(path: Path, maximum: int) -> bytes:
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0))
    except OSError as exc:
        raise CgroupV2Reject("cgroup_boundary_file_open_failed") from exc
    try:
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, min(65_536, maximum + 1 - total))
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)
            total += len(chunk)
            if total > maximum:
                raise CgroupV2Reject("cgroup_boundary_file_too_large")
    finally:
        os.close(descriptor)


def _read_at(directory_fd: int, name: str) -> bytes:
    _require_control_name(name)
    try:
        descriptor = os.open(
            name,
            os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
            dir_fd=directory_fd,
        )
    except OSError as exc:
        raise CgroupV2Reject("cgroup_control_open_failed") from exc
    try:
        chunks: list[bytes] = []
        total = 0
        while True:
            chunk = os.read(descriptor, min(4096, MAX_CONTROL_BYTES + 1 - total))
            if not chunk:
                return b"".join(chunks)
            chunks.append(chunk)
            total += len(chunk)
            if total > MAX_CONTROL_BYTES:
                raise CgroupV2Reject("cgroup_control_too_large")
    finally:
        os.close(descriptor)


def _read_process_identity(proc_root: Path, pid: int) -> tuple[int, int]:
    raw = read_bounded_path(proc_root / str(pid) / "stat", MAX_CONTROL_BYTES)
    try:
        text = raw.decode("ascii").rstrip("\n")
    except UnicodeDecodeError as exc:
        raise CgroupV2Reject("cgroup_process_stat_invalid") from exc
    close = text.rfind(")")
    fields = text[close + 1 :].split() if close > 0 else []
    if len(fields) < 20 or len(fields[0]) != 1:
        raise CgroupV2Reject("cgroup_process_stat_invalid")
    try:
        parent = int(fields[1])
        start_time = int(fields[19])
    except ValueError as exc:
        raise CgroupV2Reject("cgroup_process_stat_invalid") from exc
    if parent <= 0 or start_time <= 0:
        raise CgroupV2Reject("cgroup_process_stat_invalid")
    return parent, start_time


def _require_trusted_directory(
    before: os.stat_result,
    after: os.stat_result,
    trusted_uid: int,
) -> None:
    before_identity = (before.st_dev, before.st_ino, before.st_mode, before.st_uid)
    after_identity = (after.st_dev, after.st_ino, after.st_mode, after.st_uid)
    if before_identity != after_identity or not stat.S_ISDIR(after.st_mode):
        raise CgroupV2Reject("cgroup_directory_identity_mismatch")
    if after.st_uid != trusted_uid or stat.S_IMODE(after.st_mode) & 0o022:
        raise CgroupV2Reject("cgroup_directory_not_trusted")


def _require_control_name(name: str) -> None:
    if not name or "/" in name or name in {".", ".."}:
        raise CgroupV2Reject("cgroup_control_name_invalid")


def _unescape_mountinfo(value: str) -> str:
    for encoded, decoded in (("\\040", " "), ("\\011", "\t"), ("\\012", "\n"), ("\\134", "\\")):
        value = value.replace(encoded, decoded)
    return value
