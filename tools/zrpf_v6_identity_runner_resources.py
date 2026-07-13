"""Deterministic CPU, job, memory, tmpfs, and path policy for V6 builds."""

from __future__ import annotations

import os
from pathlib import PurePosixPath
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools.zrpf_v6_identity_executor_types import BuildRequest, ExecutionError
from tools.zrpf_v6_identity_runner_protocol import require_output_name

RISC0_TOOLCHAIN_DIRECTORY = "v1.94.1-rust-x86_64-unknown-linux-gnu"
TARGET_TMPFS_QUOTA_BYTES = planner.TARGET_TMPFS_QUOTA_BYTES
OUTPUT_TMPFS_QUOTA_BYTES = planner.OUTPUT_TMPFS_QUOTA_BYTES
TMP_TMPFS_QUOTA_BYTES = 256 * 1024 * 1024
CARGO_TMPFS_QUOTA_BYTES = 512 * 1024 * 1024
HOME_TMPFS_QUOTA_BYTES = 4 * 1024 * 1024
RISC0_TMPFS_QUOTA_BYTES = 4 * 1024 * 1024
MINIMUM_PROCESS_MEMORY_HEADROOM_BYTES = 2 * 1024 * 1024 * 1024
NESTED_CARGO_WRAPPER_FILE = "nested-cargo-wrapper"
NESTED_CARGO_WRAPPER_CONTAINER_PATH = "/pinned-bin/cargo"
NESTED_CARGO_WRAPPER_BYTES = planner.NESTED_CARGO_WRAPPER_BYTES
NESTED_CARGO_WRAPPER_SHA256 = planner.NESTED_CARGO_WRAPPER_SHA256


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
    _validate_command_resources(request)


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
    execution = ",noexec" if noexec else ""
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
