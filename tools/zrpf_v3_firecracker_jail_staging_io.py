"""Descriptor-safe file and canonical-config primitives for jail staging."""

from __future__ import annotations

import hashlib
import json
import os
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Final, NoReturn

from tools.zrpf_v3_firecracker_output_protocol import OUTPUT_BYTES_V1
from tools.zrpf_v3_firecracker_trusted_runtime import JailerLauncherReject

_READ_CHUNK_BYTES: Final = 1024 * 1024
_MAX_CONFIG_BYTES: Final = 64 * 1024


@dataclass(frozen=True, slots=True)
class FileVersionV2:
    device: int
    inode: int
    mode: int
    uid: int
    gid: int
    links: int
    size: int
    mtime_ns: int
    ctime_ns: int


def open_exec_directory(
    *,
    chroot_base_dir: Path,
    firecracker_file_name: str,
    trusted_root: Path,
    trusted_uid: int,
) -> int:
    base_fd = _open_trusted_directory_path(
        chroot_base_dir,
        trusted_root=trusted_root,
        trusted_uid=trusted_uid,
    )
    try:
        return open_directory_at(base_fd, firecracker_file_name, trusted_uid)
    finally:
        os.close(base_fd)


def open_directory_at(parent_fd: int, name: str, trusted_uid: int) -> int:
    try:
        before = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
        descriptor = os.open(
            name,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
            dir_fd=parent_fd,
        )
    except OSError as exc:
        raise JailerLauncherReject("jail_stage_directory_open_failed") from exc
    try:
        _require_trusted_directory(before, os.fstat(descriptor), trusted_uid)
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def open_trusted_source(
    path: Path,
    *,
    trusted_root: Path,
    trusted_uid: int,
) -> int:
    parent_fd = _open_trusted_directory_path(
        path.parent,
        trusted_root=trusted_root,
        trusted_uid=trusted_uid,
    )
    descriptor: int | None = None
    try:
        before = os.stat(path.name, dir_fd=parent_fd, follow_symlinks=False)
        descriptor = os.open(
            path.name,
            os.O_RDONLY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
            dir_fd=parent_fd,
        )
        after = os.fstat(descriptor)
        if (
            (before.st_dev, before.st_ino, before.st_mode, before.st_uid)
            != (after.st_dev, after.st_ino, after.st_mode, after.st_uid)
            or not stat.S_ISREG(after.st_mode)
            or after.st_nlink != 1
            or after.st_uid != trusted_uid
            or stat.S_IMODE(after.st_mode) & 0o022
        ):
            raise JailerLauncherReject("jail_stage_source_untrusted")
        return descriptor
    except BaseException as exc:
        if descriptor is not None:
            try:
                os.close(descriptor)
            except OSError:
                pass
        if isinstance(exc, OSError):
            raise JailerLauncherReject("jail_stage_source_open_failed") from exc
        raise
    finally:
        os.close(parent_fd)


def copy_exact_artifact(
    *,
    source_fd: int,
    destination_dir_fd: int,
    role: str,
    expected_sha256: str,
    expected_size: int,
    trusted_uid: int,
) -> int:
    source_before = os.fstat(source_fd)
    if source_before.st_size != expected_size:
        raise JailerLauncherReject("jail_stage_source_size_mismatch")
    if sha256_fd(source_fd, expected_size) != expected_sha256:
        raise JailerLauncherReject("jail_stage_source_digest_mismatch")
    output = os.open(
        role,
        os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
        0o400,
        dir_fd=destination_dir_fd,
    )
    try:
        os.lseek(source_fd, 0, os.SEEK_SET)
        _copy_exact_bytes(source_fd, output, expected_size)
        os.fchmod(output, 0o444)
        if trusted_uid == 0:
            os.fchown(output, 0, 0)
        os.fsync(output)
        if file_version(source_before) != file_version(os.fstat(source_fd)):
            raise JailerLauncherReject("jail_stage_source_changed_while_copying")
        staged = os.fstat(output)
        if staged.st_size != expected_size or sha256_fd(output, expected_size) != expected_sha256:
            raise JailerLauncherReject("jail_stage_copy_verification_failed")
        return output
    except BaseException:
        os.close(output)
        try:
            os.unlink(role, dir_fd=destination_dir_fd)
        except OSError:
            pass
        raise


def create_exact_file(
    directory_fd: int,
    name: str,
    raw: bytes,
    *,
    uid: int,
    gid: int,
    mode: int,
) -> int:
    descriptor = os.open(
        name,
        os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
        0o600,
        dir_fd=directory_fd,
    )
    try:
        _write_all(descriptor, raw)
        os.fchmod(descriptor, mode)
        _require_or_set_owner(descriptor, uid=uid, gid=gid)
        os.fsync(descriptor)
        if pread_exact(descriptor, len(raw), 0) != raw:
            raise JailerLauncherReject("jail_stage_exact_file_mismatch")
        return descriptor
    except BaseException:
        os.close(descriptor)
        try:
            os.unlink(name, dir_fd=directory_fd)
        except OSError:
            pass
        raise


def create_fresh_output(
    directory_fd: int,
    request_bytes: bytes,
    *,
    uid: int,
    gid: int,
) -> int:
    descriptor = os.open(
        "output",
        os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
        0o600,
        dir_fd=directory_fd,
    )
    try:
        os.ftruncate(descriptor, OUTPUT_BYTES_V1)
        os.pwrite(descriptor, request_bytes, 0)
        os.fchmod(descriptor, 0o600)
        _require_or_set_owner(descriptor, uid=uid, gid=gid)
        os.fsync(descriptor)
        return descriptor
    except BaseException:
        os.close(descriptor)
        try:
            os.unlink("output", dir_fd=directory_fd)
        except OSError:
            pass
        raise


def validate_config_bytes(raw: bytes) -> None:
    if type(raw) is not bytes or not 0 < len(raw) <= _MAX_CONFIG_BYTES:
        raise JailerLauncherReject("jail_stage_config_invalid")
    try:
        value = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as exc:
        raise JailerLauncherReject("jail_stage_config_invalid") from exc
    if raw != _canonical_json_bytes(value) or type(value) is not dict:
        raise JailerLauncherReject("jail_stage_config_noncanonical")
    if set(value) != {"boot-source", "drives", "machine-config"}:
        raise JailerLauncherReject("jail_stage_config_fields_invalid")
    _require_exact_resource_paths(value)


def file_version(metadata: os.stat_result) -> FileVersionV2:
    return FileVersionV2(
        metadata.st_dev,
        metadata.st_ino,
        metadata.st_mode,
        metadata.st_uid,
        metadata.st_gid,
        metadata.st_nlink,
        metadata.st_size,
        metadata.st_mtime_ns,
        metadata.st_ctime_ns,
    )


def sha256_fd(descriptor: int, expected_size: int) -> str:
    digest = hashlib.sha256()
    offset = 0
    while offset < expected_size:
        chunk = os.pread(
            descriptor,
            min(_READ_CHUNK_BYTES, expected_size - offset),
            offset,
        )
        if not chunk:
            raise JailerLauncherReject("jail_stage_short_read")
        digest.update(chunk)
        offset += len(chunk)
    if os.pread(descriptor, 1, expected_size):
        raise JailerLauncherReject("jail_stage_oversized_read")
    return digest.hexdigest()


def pread_exact(descriptor: int, size: int, offset: int) -> bytes:
    output = bytearray()
    while len(output) < size:
        chunk = os.pread(
            descriptor,
            min(_READ_CHUNK_BYTES, size - len(output)),
            offset + len(output),
        )
        if not chunk:
            raise JailerLauncherReject("jail_stage_short_read")
        output.extend(chunk)
    return bytes(output)


def region_has_nonzero(descriptor: int, *, start: int, size: int) -> bool:
    offset = 0
    while offset < size:
        chunk = os.pread(
            descriptor,
            min(_READ_CHUNK_BYTES, size - offset),
            start + offset,
        )
        if not chunk:
            raise JailerLauncherReject("jail_stage_short_read")
        if any(chunk):
            return True
        offset += len(chunk)
    return False


def _open_trusted_directory_path(
    path: Path,
    *,
    trusted_root: Path,
    trusted_uid: int,
) -> int:
    if not path.is_absolute() or not trusted_root.is_absolute():
        raise JailerLauncherReject("jail_stage_trusted_path_invalid")
    try:
        relative = path.relative_to(trusted_root)
    except ValueError as exc:
        raise JailerLauncherReject("jail_stage_path_outside_trusted_root") from exc
    current = _open_directory_path_root(trusted_root, trusted_uid)
    try:
        for component in relative.parts:
            if component in {"", ".", ".."}:
                raise JailerLauncherReject("jail_stage_trusted_path_invalid")
            child = open_directory_at(current, component, trusted_uid)
            os.close(current)
            current = child
        return current
    except BaseException:
        os.close(current)
        raise


def _open_directory_path_root(path: Path, trusted_uid: int) -> int:
    try:
        before = path.lstat()
        descriptor = os.open(
            path,
            os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC | getattr(os, "O_NOFOLLOW", 0),
        )
    except OSError as exc:
        raise JailerLauncherReject("jail_stage_directory_open_failed") from exc
    try:
        _require_trusted_directory(before, os.fstat(descriptor), trusted_uid)
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def _require_trusted_directory(
    before: os.stat_result,
    after: os.stat_result,
    trusted_uid: int,
) -> None:
    if (
        (before.st_dev, before.st_ino, before.st_mode, before.st_uid)
        != (after.st_dev, after.st_ino, after.st_mode, after.st_uid)
        or not stat.S_ISDIR(after.st_mode)
        or after.st_uid != trusted_uid
        or stat.S_IMODE(after.st_mode) & 0o022
    ):
        raise JailerLauncherReject("jail_stage_directory_untrusted")


def _copy_exact_bytes(source_fd: int, destination_fd: int, size: int) -> None:
    os.lseek(source_fd, 0, os.SEEK_SET)
    remaining = size
    while remaining:
        chunk = os.read(source_fd, min(_READ_CHUNK_BYTES, remaining))
        if not chunk:
            raise JailerLauncherReject("jail_stage_source_changed_while_copying")
        _write_all(destination_fd, chunk)
        remaining -= len(chunk)


def _require_or_set_owner(descriptor: int, *, uid: int, gid: int) -> None:
    if os.geteuid() == 0:
        os.fchown(descriptor, uid, gid)
    elif uid != os.geteuid() or gid != os.getegid():
        raise JailerLauncherReject("jail_stage_chown_requires_root")


def _require_exact_resource_paths(value: dict[str, Any]) -> None:
    boot = value["boot-source"]
    drives = value["drives"]
    if (
        type(boot) is not dict
        or boot.get("kernel_image_path") != "/resources/kernel"
        or type(drives) is not list
        or len(drives) != 3
    ):
        raise JailerLauncherReject("jail_stage_config_resource_binding_invalid")
    expected_paths = {
        "rootfs": ("/resources/rootfs", True, True),
        "input": ("/resources/input", False, True),
        "output": ("/resources/output", False, False),
    }
    observed: dict[str, tuple[object, object, object]] = {}
    for drive in drives:
        if type(drive) is not dict or type(drive.get("drive_id")) is not str:
            raise JailerLauncherReject("jail_stage_config_drive_invalid")
        drive_id = drive["drive_id"]
        if drive_id in observed:
            raise JailerLauncherReject("jail_stage_config_drive_invalid")
        observed[drive_id] = (
            drive.get("path_on_host"),
            drive.get("is_root_device"),
            drive.get("is_read_only"),
        )
    if observed != expected_paths:
        raise JailerLauncherReject("jail_stage_config_resource_binding_invalid")


def _canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n"
    ).encode("ascii")


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    output: dict[str, Any] = {}
    for key, value in pairs:
        if key in output:
            raise ValueError("duplicate key")
        output[key] = value
    return output


def _reject_constant(_value: str) -> NoReturn:
    raise ValueError("non-finite number")


def _write_all(descriptor: int, raw: bytes) -> None:
    view = memoryview(raw)
    offset = 0
    while offset < len(view):
        written = os.write(descriptor, view[offset:])
        if written <= 0:
            raise JailerLauncherReject("jail_stage_write_failed")
        offset += written
