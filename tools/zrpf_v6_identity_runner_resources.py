"""Deterministic CPU, job, memory, tmpfs, and path policy for V6 builds."""

from __future__ import annotations

import fcntl
import json
import os
import re
import stat
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools.zrpf_v6_identity_executor_types import BuildRequest, ExecutionError
from tools.zrpf_v6_identity_runner_protocol import require_output_name

RISC0_TOOLCHAIN_DIRECTORY = "v1.94.1-rust-x86_64-unknown-linux-gnu"
TARGET_TMPFS_QUOTA_BYTES = planner.TARGET_TMPFS_QUOTA_BYTES
OUTPUT_TMPFS_QUOTA_BYTES = planner.OUTPUT_TMPFS_QUOTA_BYTES
TMP_TMPFS_QUOTA_BYTES = planner.TMP_TMPFS_QUOTA_BYTES
CARGO_TMPFS_QUOTA_BYTES = planner.CARGO_TMPFS_QUOTA_BYTES
HOME_TMPFS_QUOTA_BYTES = planner.HOME_TMPFS_QUOTA_BYTES
RISC0_TMPFS_QUOTA_BYTES = planner.RISC0_TMPFS_QUOTA_BYTES
MINIMUM_PROCESS_MEMORY_HEADROOM_BYTES = planner.MINIMUM_PROCESS_MEMORY_HEADROOM_BYTES
MINIMUM_HOST_MEM_AVAILABLE_BYTES = planner.MINIMUM_HOST_MEM_AVAILABLE_BYTES
NESTED_CARGO_WRAPPER_FILE = "nested-cargo-wrapper"
NESTED_CARGO_WRAPPER_CONTAINER_PATH = "/pinned-bin/cargo"
NESTED_CARGO_WRAPPER_BYTES = planner.NESTED_CARGO_WRAPPER_BYTES
NESTED_CARGO_WRAPPER_SHA256 = planner.NESTED_CARGO_WRAPPER_SHA256
MAX_PROC_MEMINFO_BYTES = 64 * 1024
HOST_BUILD_LEASE_PATH = Path("/tmp/zenodex-zrpf-v6-identity-build.lock")
HOST_BUILD_LEASE_SCHEMA = "zenodex/zrpf_v6_host_build_lease/v1"
MAX_HOST_BUILD_LEASE_BYTES = 4_096
_CLEAR_LEASE_BYTES = (
    json.dumps(
        {"schema": HOST_BUILD_LEASE_SCHEMA, "state": "clear"},
        allow_nan=False,
        separators=(",", ":"),
        sort_keys=True,
    )
    + "\n"
).encode("utf-8")


@dataclass(frozen=True)
class HostBuildRecoveryRecord:
    container_name: str
    container_id_file: Path


@dataclass
class HostBuildLease:
    """Exclusive same-host lease held across preflight, build, and cleanup."""

    descriptor: int
    active_record: dict[str, object]
    clear_on_exit: bool = True

    def __enter__(self) -> HostBuildLease:
        return self

    def mark_cleanup_incomplete(self) -> None:
        # The already-fsynced active record contains the exact recovery
        # identity.  Retain it verbatim. Rewriting after cleanup failure could
        # truncate the only durable poison marker on a second I/O failure.
        self.clear_on_exit = False

    def __exit__(self, *_exc: object) -> None:
        try:
            if self.clear_on_exit:
                _write_lease_record(self.descriptor, _CLEAR_LEASE_BYTES)
        finally:
            fcntl.flock(self.descriptor, fcntl.LOCK_UN)
            os.close(self.descriptor)


@dataclass
class HostBuildRecoveryLease:
    """Exclusive recovery capability for one persisted active/orphan record."""

    descriptor: int
    record: HostBuildRecoveryRecord
    recovered: bool = False

    def __enter__(self) -> HostBuildRecoveryLease:
        return self

    def mark_recovered(self) -> None:
        self.recovered = True

    def __exit__(self, *_exc: object) -> None:
        try:
            if self.recovered:
                _write_lease_record(self.descriptor, _CLEAR_LEASE_BYTES)
        finally:
            fcntl.flock(self.descriptor, fcntl.LOCK_UN)
            os.close(self.descriptor)


def security_resource_policy() -> dict[str, Any]:
    return dict(planner.RUNNER_RESOURCE_POLICY)


def validate_resource_policy() -> None:
    # Docker charges tmpfs pages to the container cgroup. Reserve process
    # headroom after every writable mount reaches its governed maximum.
    writable_tmpfs = (
        TARGET_TMPFS_QUOTA_BYTES
        + OUTPUT_TMPFS_QUOTA_BYTES
        + TMP_TMPFS_QUOTA_BYTES
        + CARGO_TMPFS_QUOTA_BYTES
        + HOME_TMPFS_QUOTA_BYTES
        + RISC0_TMPFS_QUOTA_BYTES
    )
    if (
        planner.BUILD_CPUS != 2
        or planner.BUILD_JOBS != 2
        or planner.CANONICAL_CARGO != f"/risc0/toolchains/{RISC0_TOOLCHAIN_DIRECTORY}/bin/cargo"
        or writable_tmpfs + MINIMUM_PROCESS_MEMORY_HEADROOM_BYTES > planner.BUILD_MEMORY_BYTES
    ):
        raise ExecutionError("build CPU, job, memory, and tmpfs policy is inconsistent")
    if OUTPUT_TMPFS_QUOTA_BYTES <= (
        planner.MAX_PROGRAM_BINARY_BYTES + planner.MAX_HOST_BINARY_BYTES
    ):
        raise ExecutionError("build output tmpfs lacks bounded framing headroom")


def require_host_memory_available(
    meminfo_path: Path = Path("/proc/meminfo"),
) -> int:
    """Fail closed before a heavy build when host memory headroom is insufficient."""

    available = parse_mem_available_bytes(_read_bounded_proc_file(meminfo_path))
    if available < MINIMUM_HOST_MEM_AVAILABLE_BYTES:
        raise ExecutionError("host MemAvailable is below the governed build minimum")
    return available


def acquire_host_build_lease(
    container_name: str,
    container_id_file: Path,
    path: Path = HOST_BUILD_LEASE_PATH,
) -> HostBuildLease:
    """Acquire one nonblocking host-wide build slot for this governed profile."""

    _validate_recovery_identity(container_name, container_id_file)
    descriptor = _open_locked_lease(path)
    try:
        previous = _read_lease_record(descriptor)
        if previous not in (b"", _CLEAR_LEASE_BYTES):
            raise ExecutionError(
                "host build lease is poisoned by an active or incompletely cleaned run"
            )
        record: dict[str, object] = {
            "schema": HOST_BUILD_LEASE_SCHEMA,
            "state": "active",
            "pid": os.getpid(),
            "container_name": container_name,
            "container_id_file": container_id_file.as_posix(),
        }
        _write_lease_record(descriptor, _canonical_lease_bytes(record))
    except BaseException:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)
        raise
    return HostBuildLease(descriptor, record)


def acquire_host_build_recovery_lease(
    path: Path = HOST_BUILD_LEASE_PATH,
) -> HostBuildRecoveryLease:
    """Open a persisted active/orphan record for exact Docker cleanup."""

    descriptor = _open_locked_lease(path)
    try:
        record = _parse_recovery_record(_read_lease_record(descriptor))
    except BaseException:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)
        raise
    return HostBuildRecoveryLease(descriptor, record)


def _open_locked_lease(path: Path) -> int:
    if not path.is_absolute() or path.parent.resolve(strict=True) != path.parent:
        raise ExecutionError("host build lease path is noncanonical")
    flags = os.O_RDWR | os.O_CREAT | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        descriptor = os.open(path, flags, 0o600)
    except OSError as exc:
        raise ExecutionError("host build lease is unavailable") from exc
    try:
        descriptor_facts = os.fstat(descriptor)
        path_facts = path.lstat()
        expected = _lease_identity(descriptor_facts)
        if (
            expected != _lease_identity(path_facts)
            or not stat.S_ISREG(descriptor_facts.st_mode)
            or descriptor_facts.st_uid != os.getuid()
            or descriptor_facts.st_nlink != 1
            or stat.S_IMODE(descriptor_facts.st_mode) != 0o600
        ):
            raise ExecutionError("host build lease identity rejected")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ExecutionError(
                "another governed ZRPF identity build holds the host lease"
            ) from exc
    except BaseException:
        os.close(descriptor)
        raise
    return descriptor


def _lease_identity(facts: os.stat_result) -> tuple[int, ...]:
    return (
        facts.st_dev,
        facts.st_ino,
        facts.st_mode,
        facts.st_uid,
        facts.st_gid,
        facts.st_nlink,
    )


def _read_lease_record(descriptor: int) -> bytes:
    os.lseek(descriptor, 0, os.SEEK_SET)
    raw = os.read(descriptor, MAX_HOST_BUILD_LEASE_BYTES + 1)
    if len(raw) > MAX_HOST_BUILD_LEASE_BYTES:
        raise ExecutionError("host build lease record exceeds its byte bound")
    return raw


def _write_lease_record(descriptor: int, raw: bytes) -> None:
    if not raw or len(raw) > MAX_HOST_BUILD_LEASE_BYTES:
        raise ExecutionError("host build lease record is outside its byte bound")
    os.ftruncate(descriptor, 0)
    os.lseek(descriptor, 0, os.SEEK_SET)
    if os.write(descriptor, raw) != len(raw):
        raise ExecutionError("host build lease record was truncated")
    os.fsync(descriptor)


def _canonical_lease_bytes(record: dict[str, object]) -> bytes:
    return (
        json.dumps(
            record,
            allow_nan=False,
            separators=(",", ":"),
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def _parse_recovery_record(raw: bytes) -> HostBuildRecoveryRecord:
    try:
        document = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ExecutionError("host build lease recovery record is invalid") from exc
    if (
        not isinstance(document, dict)
        or _canonical_lease_bytes(document) != raw
        or set(document) != {"schema", "state", "pid", "container_name", "container_id_file"}
        or document.get("schema") != HOST_BUILD_LEASE_SCHEMA
        or document.get("state") not in {"active", "cleanup_incomplete"}
        or not isinstance(document.get("pid"), int)
        or isinstance(document.get("pid"), bool)
        or document["pid"] <= 0
        or not isinstance(document.get("container_name"), str)
        or not isinstance(document.get("container_id_file"), str)
    ):
        raise ExecutionError("host build lease recovery record is invalid")
    container_id_file = Path(document["container_id_file"])
    _validate_recovery_identity(document["container_name"], container_id_file)
    return HostBuildRecoveryRecord(document["container_name"], container_id_file)


def _validate_recovery_identity(container_name: str, container_id_file: Path) -> None:
    if (
        re.fullmatch(r"zrpf-v6-[0-9a-f]{20}", container_name) is None
        or not container_id_file.is_absolute()
        or container_id_file.name != "docker-container.cid"
        or ".." in container_id_file.parts
    ):
        raise ExecutionError("host build lease recovery identity is invalid")


def parse_mem_available_bytes(raw: bytes) -> int:
    """Parse exactly one Linux ``MemAvailable`` row into bytes."""

    rows = [line.split() for line in raw.splitlines() if line.startswith(b"MemAvailable:")]
    if len(rows) != 1 or len(rows[0]) != 3:
        raise ExecutionError("host MemAvailable row is missing or ambiguous")
    name, digits, unit = rows[0]
    if name != b"MemAvailable:" or not digits.isdigit() or unit != b"kB":
        raise ExecutionError("host MemAvailable row is malformed")
    kibibytes = int(digits)
    if kibibytes <= 0 or kibibytes > (2**63 - 1) // 1024:
        raise ExecutionError("host MemAvailable value is outside its bound")
    return kibibytes * 1024


def _read_bounded_proc_file(path: Path) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise ExecutionError("host memory information is unavailable") from exc
    try:
        raw = os.read(descriptor, MAX_PROC_MEMINFO_BYTES + 1)
    finally:
        os.close(descriptor)
    if not raw or len(raw) > MAX_PROC_MEMINFO_BYTES:
        raise ExecutionError("host memory information exceeds its byte bound")
    return raw


def validate_build_request(request: BuildRequest) -> None:
    require_output_name(request.artifact_file)
    _require_container_build_path(
        request.container_target_directory,
        "container target directory",
    )
    _require_container_build_path(
        request.container_output_directory,
        "container output directory",
    )
    if request.container_target_directory == request.container_output_directory:
        raise ExecutionError("container target and output directories must differ")
    _require_container_artifact_path(
        request.extraction_source,
        request.container_target_directory,
        "artifact extraction source",
    )
    _validate_companion_request(request)
    _validate_archive_request(request)
    _validate_command_resources(request)


def _validate_archive_request(request: BuildRequest) -> None:
    if request.kind.value != "archive":
        if request.archive_members:
            raise ExecutionError("archive members require the archive build kind")
        return
    if request.companion_artifact_file is not None or not 0 < len(request.archive_members) <= 16:
        raise ExecutionError("archive build has an invalid member or companion inventory")
    names: set[str] = set()
    sources: set[str] = set()
    for member in request.archive_members:
        require_output_name(member.name)
        _require_container_artifact_path(
            member.source,
            request.container_target_directory,
            "archive member source",
        )
        if (
            type(member.executable) is not bool
            or member.name in names
            or member.source in sources
            or member.source == request.extraction_source
        ):
            raise ExecutionError("archive member inventory is ambiguous")
        names.add(member.name)
        sources.add(member.source)


def auxiliary_tmpfs_arguments() -> list[str]:
    uid = os.getuid()
    gid = os.getgid()
    return [
        "--tmpfs",
        tmpfs("/tmp", TMP_TMPFS_QUOTA_BYTES, "1777", uid, gid, noexec=True),
        "--tmpfs",
        tmpfs("/cargo", CARGO_TMPFS_QUOTA_BYTES, "0700", uid, gid, noexec=True),
        "--tmpfs",
        tmpfs(
            "/sandbox-home",
            HOME_TMPFS_QUOTA_BYTES,
            "0700",
            uid,
            gid,
            noexec=True,
        ),
        "--tmpfs",
        tmpfs("/risc0", RISC0_TMPFS_QUOTA_BYTES, "0700", uid, gid, noexec=True),
    ]


def tmpfs(
    target: str,
    size_bytes: int,
    mode: str,
    uid: int,
    gid: int,
    *,
    noexec: bool,
) -> str:
    # Docker applies ``noexec`` to ``--tmpfs`` mounts by default.  The target
    # directory must execute Cargo build scripts and freshly linked host tools,
    # so the executable case needs an explicit ``exec`` override.
    execution = ",noexec" if noexec else ",exec"
    return f"{target}:rw,nosuid,nodev{execution},size={size_bytes},mode={mode},uid={uid},gid={gid}"


def _validate_companion_request(request: BuildRequest) -> None:
    if request.companion_artifact_file is None:
        if request.companion_extraction_source is not None:
            raise ExecutionError("companion extraction source is unexpected")
        return
    require_output_name(request.companion_artifact_file)
    if (
        request.companion_artifact_file == request.artifact_file
        or request.companion_extraction_source is None
    ):
        raise ExecutionError("companion artifact contract is invalid")
    _require_container_artifact_path(
        request.companion_extraction_source,
        request.container_target_directory,
        "companion extraction source",
    )


def _validate_command_resources(request: BuildRequest) -> None:
    jobs = [index for index, value in enumerate(request.command) if value == "--jobs"]
    if (
        len(jobs) != 1
        or jobs[0] + 1 >= len(request.command)
        or request.command[jobs[0] + 1] != str(planner.BUILD_JOBS)
        or any(value.startswith("--jobs=") for value in request.command)
    ):
        raise ExecutionError("build command must bind the exact outer Cargo job count")
    if not request.command or request.command[0] != planner.CANONICAL_CARGO:
        raise ExecutionError("build command must use the pinned outer Cargo path")
    targets = tuple(
        request.command[index + 1]
        for index, value in enumerate(request.command[:-1])
        if value == "--target-dir"
    )
    if targets != (request.container_target_directory,):
        raise ExecutionError("build command target directory is not exact")


def _require_container_build_path(path: str, label: str) -> None:
    pure = PurePosixPath(path)
    if (
        not pure.is_absolute()
        or len(pure.parts) < 3
        or pure.parts[1] != "build"
        or pure.as_posix() != path
        or ".." in pure.parts
        or _contains_forbidden_mount_character(path)
    ):
        raise ExecutionError(f"{label} is noncanonical")


def _require_container_artifact_path(path: str, target: str, label: str) -> None:
    pure = PurePosixPath(path)
    try:
        relative = pure.relative_to(PurePosixPath(target))
    except ValueError as exc:
        raise ExecutionError(f"{label} escapes the target directory") from exc
    if (
        pure.as_posix() != path
        or ".." in pure.parts
        or not relative.parts
        or _contains_forbidden_mount_character(path)
    ):
        raise ExecutionError(f"{label} is noncanonical")


def _contains_forbidden_mount_character(value: str) -> bool:
    return any(character in value for character in (",", ":", "\n", "\r", "\0"))
