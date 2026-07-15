"""Pinned no-network Docker runner for the Spot V6 identity rebuild."""

from __future__ import annotations

import hashlib
import os
import re
import shlex
import stat
from collections.abc import Callable
from pathlib import Path
from typing import Any

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import zrpf_v3_replay_environment as replay_environment
from tools import zrpf_v3_replay_process as process_runner
from tools import zrpf_v6_identity_runner_protocol as runner_protocol
from tools import zrpf_v6_identity_runner_resources as runner_resources
from tools.zrpf_v6_identity_executor_types import (
    BuildKind,
    BuildRequest,
    BuildResult,
    ExecutionError,
    IncompleteContainerCleanupError,
)
from tools.zrpf_v6_identity_runner_integrity import (
    StableFileIdentity,
    capture_cargo_registry,
    capture_pinned_tool,
    capture_stable_executable,
)

RUNNER_SECURITY_POSTURE_SCHEMA = planner.RUNNER_SECURITY_POSTURE_SCHEMA
BUILD_TIMEOUT_SECONDS = 4 * 60 * 60
RISC0_TOOLCHAIN_DIRECTORY = runner_resources.RISC0_TOOLCHAIN_DIRECTORY
RISC0_EXTENSION_DIRECTORY = "v3.0.5-cargo-risczero-x86_64-unknown-linux-gnu"
TARGET_TMPFS_QUOTA_BYTES = runner_resources.TARGET_TMPFS_QUOTA_BYTES
OUTPUT_TMPFS_QUOTA_BYTES = runner_resources.OUTPUT_TMPFS_QUOTA_BYTES
MAX_BUILD_OUTPUT_BYTES = runner_protocol.MAX_BUILD_OUTPUT_BYTES
NESTED_CARGO_WRAPPER_FILE = runner_resources.NESTED_CARGO_WRAPPER_FILE
NESTED_CARGO_WRAPPER_CONTAINER_PATH = runner_resources.NESTED_CARGO_WRAPPER_CONTAINER_PATH
NESTED_CARGO_WRAPPER_BYTES = runner_resources.NESTED_CARGO_WRAPPER_BYTES
NESTED_CARGO_WRAPPER_SHA256 = runner_resources.NESTED_CARGO_WRAPPER_SHA256
CONTAINER_ID_FILE = "docker-container.cid"


class DockerBuildRunner:
    """Execute exact plan commands inside the pinned, bounded OCI image."""

    def __init__(
        self,
        *,
        risc0_home: Path,
        cargo_registry_directory: Path,
        docker: Path = Path("/usr/bin/docker"),
        repo_root: Path = planner.REPO_ROOT,
    ) -> None:
        self._repo_root = repo_root.resolve(strict=True)
        self._risc0_home = _canonical_directory(risc0_home, "RISC0 home")
        self._toolchain = _canonical_directory(
            self._risc0_home / "toolchains" / RISC0_TOOLCHAIN_DIRECTORY,
            "RISC0 toolchain",
        )
        self._extension = _canonical_directory(
            self._risc0_home / "extensions" / RISC0_EXTENSION_DIRECTORY,
            "RISC0 extension",
        )
        self._registry = _canonical_directory(
            cargo_registry_directory,
            "Cargo registry",
        )
        self._docker = _canonical_executable(docker, "Docker client")
        runner_resources.validate_resource_policy()
        self._tool_identities = self._capture_tool_identities()
        self._docker_identity = self._capture_docker_identity()
        self._registry_identity = capture_cargo_registry(self._registry)
        self._validate_image()
        self._require_external_inputs_unchanged("after build image validation")

    def security_posture(self) -> dict[str, Any]:
        """Return deterministic candidate-evidence facts and explicit non-claims."""

        return {
            "schema": RUNNER_SECURITY_POSTURE_SCHEMA,
            "tool_identities": {
                name: identity.evidence()
                for name, identity in sorted(self._tool_identities.items())
            },
            "observed_docker_client_identity": self._docker_identity.evidence(),
            "cargo_registry_identity": self._registry_identity.evidence(),
            "resource_policy": runner_resources.security_resource_policy(),
            "same_uid_resistance": False,
            "complete_build_input_closure_verified": False,
        }

    def run(self, request: BuildRequest) -> BuildResult:
        if request.target_directory.exists() or request.output_directory.exists():
            raise ExecutionError("runner target and output must begin absent")
        runner_resources.validate_build_request(request)
        container_name = _container_name(request)
        container_id_file = request.target_directory / CONTAINER_ID_FILE
        with runner_resources.acquire_host_build_lease(
            container_name,
            container_id_file,
        ) as lease:
            runner_resources.require_host_memory_available()
            return self._run_with_host_lease(
                request,
                container_name,
                container_id_file,
                lease,
            )

    def _run_with_host_lease(
        self,
        request: BuildRequest,
        container_name: str,
        container_id_file: Path,
        lease: runner_resources.HostBuildLease,
    ) -> BuildResult:
        self._require_external_inputs_unchanged(f"before {request.pass_id}")
        _create_private_directory(request.target_directory)
        wrapper = request.target_directory / NESTED_CARGO_WRAPPER_FILE
        _write_new_output(wrapper, NESTED_CARGO_WRAPPER_BYTES, 0o555)
        wrapper_identity = capture_pinned_tool(
            wrapper,
            "nested Cargo wrapper",
            NESTED_CARGO_WRAPPER_SHA256,
        )
        self._require_container_absent(container_name)
        command = self._docker_command(
            request,
            container_name,
            wrapper,
            container_id_file,
        )
        primary_error: BaseException | None = None
        payload: runner_protocol.RunnerPayload | None = None
        try:
            result = process_runner.run_bounded(
                process_runner.ProcessRequest(
                    command=tuple(command),
                    cwd=request.source_snapshot,
                    env=replay_environment.clean_environment(),
                    timeout_seconds=BUILD_TIMEOUT_SECONDS,
                    output_limit_bytes=MAX_BUILD_OUTPUT_BYTES,
                    profile=process_runner.ProcessProfile.BUILD,
                )
            )
            if result.returncode != 0:
                raise ExecutionError(
                    f"{request.pass_id} container build rejected with exit {result.returncode}"
                )
            payload = _parse_runner_payload(result.stdout, request)
        except (OSError, RuntimeError) as exc:
            wrapped = ExecutionError(f"{request.pass_id} container build failed")
            primary_error = wrapped
            raise wrapped from exc
        except BaseException as exc:
            primary_error = exc
            raise
        finally:
            self._finalize_run(
                request.pass_id,
                container_name,
                container_id_file,
                wrapper,
                wrapper_identity,
                primary_error,
                lease,
            )
        if payload is None:
            raise ExecutionError(f"{request.pass_id} produced no verified runner payload")
        _materialize_runner_payload(request, payload)
        return payload.result

    def _finalize_run(
        self,
        pass_id: str,
        container_name: str,
        container_id_file: Path,
        wrapper: Path,
        wrapper_identity: StableFileIdentity,
        primary_error: BaseException | None,
        lease: runner_resources.HostBuildLease,
    ) -> None:
        cleanup_error = _capture_failure(
            lambda: self._cleanup_owned_container(container_name, container_id_file)
        )
        integrity_error = _capture_failure(
            lambda: self._require_external_inputs_unchanged(f"after {pass_id}")
        )
        wrapper_error = _capture_failure(
            lambda: _require_wrapper_unchanged(wrapper, wrapper_identity, pass_id)
        )
        integrity_error = _combine_failures(integrity_error, wrapper_error)
        if cleanup_error is not None:
            lease.mark_cleanup_incomplete()
        if primary_error is not None:
            if cleanup_error is not None:
                raise IncompleteContainerCleanupError(
                    f"{pass_id} failed and owned-container cleanup is incomplete: "
                    f"{cleanup_error}; recovery state must be retained"
                ) from primary_error
            if integrity_error is not None:
                raise ExecutionError(
                    f"{pass_id} failed and post-run integrity verification also failed: "
                    f"{integrity_error}"
                ) from primary_error
            return
        if cleanup_error is not None:
            raise IncompleteContainerCleanupError(
                f"{pass_id} completed but owned-container cleanup is incomplete: "
                f"{cleanup_error}; recovery state must be retained"
            ) from cleanup_error
        if integrity_error is not None:
            raise integrity_error

    def recover_host_build_lease(
        self,
        lease_path: Path = runner_resources.HOST_BUILD_LEASE_PATH,
    ) -> runner_resources.HostBuildRecoveryRecord:
        """Remove the exact recorded owned container and clear the poisoned lease."""

        with runner_resources.acquire_host_build_recovery_lease(lease_path) as recovery:
            self._cleanup_owned_container(
                recovery.record.container_name,
                recovery.record.container_id_file,
            )
            recovery.mark_recovered()
            return recovery.record

    def _capture_tool_identities(self) -> dict[str, StableFileIdentity]:
        tools = {
            "cargo": (
                self._toolchain / "bin/cargo",
                planner.TOOLCHAIN["outer_cargo_sha256"],
            ),
            "rustc": (
                self._toolchain / "bin/rustc",
                planner.TOOLCHAIN["rustc_sha256"],
            ),
            "r0vm": (
                self._extension / "r0vm",
                planner.TOOLCHAIN["r0vm_sha256"],
            ),
            "cargo_risczero": (
                self._extension / "cargo-risczero",
                planner.TOOLCHAIN["cargo_risczero_sha256"],
            ),
        }
        return {
            name: capture_pinned_tool(path, name, digest) for name, (path, digest) in tools.items()
        }

    def _capture_docker_identity(self) -> StableFileIdentity:
        return capture_stable_executable(self._docker, "Docker client")

    def _require_external_inputs_unchanged(self, transition: str) -> None:
        if self._capture_tool_identities() != self._tool_identities:
            raise ExecutionError(f"pinned tool identity changed {transition}")
        if self._capture_docker_identity() != self._docker_identity:
            raise ExecutionError(f"Docker client identity changed {transition}")
        if capture_cargo_registry(self._registry) != self._registry_identity:
            raise ExecutionError(f"Cargo registry identity changed {transition}")

    def _validate_image(self) -> None:
        try:
            result = process_runner.run_bounded(
                process_runner.ProcessRequest(
                    command=(
                        str(self._docker),
                        "image",
                        "inspect",
                        "--format",
                        "{{.Id}}",
                        planner.BUILD_IMAGE,
                    ),
                    cwd=self._risc0_home,
                    env=replay_environment.clean_environment(),
                    timeout_seconds=60,
                    output_limit_bytes=4_096,
                    profile=process_runner.ProcessProfile.TOOL,
                )
            )
        except (OSError, RuntimeError) as exc:
            raise ExecutionError("pinned build image inspection failed") from exc
        if (
            result.returncode != 0
            or result.stderr
            or result.stdout != (planner.BUILD_IMAGE + "\n").encode("ascii")
        ):
            raise ExecutionError("pinned build image is unavailable or mismatched")

    def _docker_command(
        self,
        request: BuildRequest,
        container_name: str,
        nested_cargo_wrapper: Path,
        container_id_file: Path,
    ) -> list[str]:
        for path in (
            request.source_snapshot,
            request.target_directory,
            request.output_directory,
            self._toolchain,
            self._extension,
            self._registry,
            nested_cargo_wrapper,
            container_id_file.parent,
        ):
            _require_safe_mount_path(path)
        if container_id_file.exists() or container_id_file.is_symlink():
            raise ExecutionError("container ID file must begin absent")
        return [
            str(self._docker),
            "run",
            "--name",
            container_name,
            "--cidfile",
            str(container_id_file),
            "--network",
            "none",
            "--read-only",
            "--cap-drop",
            "ALL",
            "--security-opt",
            "no-new-privileges",
            "--pids-limit",
            "512",
            "--cpus",
            str(planner.BUILD_CPUS),
            "--memory",
            str(planner.BUILD_MEMORY_BYTES),
            "--memory-swap",
            str(planner.BUILD_MEMORY_BYTES),
            "--user",
            f"{os.getuid()}:{os.getgid()}",
            "--hostname",
            "zrpf-v6-candidate-build",
            *_tmpfs_arguments(request),
            *_mount_arguments(request, self._toolchain, self._extension, self._registry),
            "--mount",
            _mount(
                nested_cargo_wrapper,
                NESTED_CARGO_WRAPPER_CONTAINER_PATH,
                readonly=True,
            ),
            "--env",
            "LC_ALL=C",
            "--env",
            f"SOURCE_DATE_EPOCH={_source_commit_epoch(self._repo_root, request.source_commit)}",
            "--env",
            "TZ=UTC",
            "--workdir",
            planner.CANONICAL_SOURCE_ROOT,
            "--entrypoint",
            "/bin/bash",
            planner.BUILD_IMAGE,
            "-p",
            "-ceu",
            _container_script(request),
        ]

    def _require_container_absent(self, container_name: str) -> None:
        try:
            inspected = self._inspect_container(container_name)
        except (OSError, RuntimeError) as exc:
            raise ExecutionError(
                f"container preflight inspection failed: {container_name}"
            ) from exc
        if _inspect_confirms_absent(inspected, container_name):
            return
        if _inspect_reports_one_id(inspected):
            raise ExecutionError(f"container name must begin absent: {container_name}")
        raise ExecutionError(f"container preflight inspection failed: {container_name}")

    def _cleanup_owned_container(
        self,
        container_name: str,
        container_id_file: Path,
    ) -> None:
        container_id = _read_container_id(container_id_file)
        if container_id is None:
            try:
                inspected_name = self._inspect_container(container_name)
            except (OSError, RuntimeError) as exc:
                raise ExecutionError(
                    f"container cleanup inspection failed: {container_name}"
                ) from exc
            if _inspect_confirms_absent(inspected_name, container_name):
                return
            if _inspect_reports_one_id(inspected_name):
                raise ExecutionError(f"container cleanup ownership unavailable: {container_name}")
            raise ExecutionError(f"container cleanup inspection failed: {container_name}")

        try:
            before = self._inspect_container(container_id)
            if _inspect_confirms_absent(before, container_id):
                _require_name_absent_after_cleanup(self, container_name)
                return
            if not _inspect_confirms_exact_id(before, container_id):
                raise ExecutionError(
                    f"owned container pre-cleanup inspection failed: {container_id}"
                )
            removed = process_runner.run_bounded(
                process_runner.ProcessRequest(
                    command=(str(self._docker), "rm", "--force", container_id),
                    cwd=self._risc0_home,
                    env=replay_environment.clean_environment(),
                    timeout_seconds=30,
                    output_limit_bytes=4_096,
                    profile=process_runner.ProcessProfile.TOOL,
                )
            )
            inspected = self._inspect_container(container_id)
        except (OSError, RuntimeError) as exc:
            raise ExecutionError(f"container cleanup command failed: {container_id}") from exc
        if (
            removed.returncode != 0
            or removed.stderr
            or removed.stdout != (container_id + "\n").encode("ascii")
        ):
            raise ExecutionError(f"container removal failed: {container_id}")
        if not _inspect_confirms_absent(inspected, container_id):
            raise ExecutionError(f"container remains after cleanup: {container_id}")
        _require_name_absent_after_cleanup(self, container_name)

    def _inspect_container(self, container_name: str) -> Any:
        return process_runner.run_bounded(
            process_runner.ProcessRequest(
                command=(
                    str(self._docker),
                    "container",
                    "inspect",
                    "--format",
                    "{{.Id}}",
                    container_name,
                ),
                cwd=self._risc0_home,
                env=replay_environment.clean_environment(),
                timeout_seconds=30,
                output_limit_bytes=4_096,
                profile=process_runner.ProcessProfile.TOOL,
            )
        )


def _capture_failure(action: Callable[[], None]) -> BaseException | None:
    try:
        action()
    except BaseException as exc:
        return exc
    return None


def _combine_failures(
    first: BaseException | None,
    second: BaseException | None,
) -> BaseException | None:
    if first is None:
        return second
    _add_failure_note(first, second)
    return first


def _add_failure_note(
    primary: BaseException,
    secondary: BaseException | None,
) -> None:
    if secondary is not None:
        primary.add_note(str(secondary))


def _require_wrapper_unchanged(
    wrapper: Path,
    expected: StableFileIdentity,
    pass_id: str,
) -> None:
    actual = capture_pinned_tool(
        wrapper,
        "nested Cargo wrapper",
        NESTED_CARGO_WRAPPER_SHA256,
    )
    if actual != expected:
        raise ExecutionError(f"nested Cargo wrapper identity changed after {pass_id}")


def _tmpfs_arguments(_request: BuildRequest) -> list[str]:
    return runner_resources.auxiliary_tmpfs_arguments()


_tmpfs = runner_resources.tmpfs


def _mount_arguments(
    request: BuildRequest,
    toolchain: Path,
    extension: Path,
    registry: Path,
) -> list[str]:
    return [
        "--mount",
        _mount(request.source_snapshot, planner.CANONICAL_SOURCE_ROOT, readonly=True),
        "--mount",
        _mount(
            toolchain,
            f"/risc0/toolchains/{RISC0_TOOLCHAIN_DIRECTORY}",
            readonly=True,
        ),
        "--mount",
        _mount(extension, "/risc0/bin", readonly=True),
        "--mount",
        _mount(registry, "/opt/cargo-registry", readonly=True),
        "--tmpfs",
        _tmpfs(
            request.container_target_directory,
            TARGET_TMPFS_QUOTA_BYTES,
            mode="0700",
            uid=os.getuid(),
            gid=os.getgid(),
            noexec=False,
        ),
        "--tmpfs",
        _tmpfs(
            request.container_output_directory,
            OUTPUT_TMPFS_QUOTA_BYTES,
            mode="0700",
            uid=os.getuid(),
            gid=os.getgid(),
            noexec=True,
        ),
    ]


def _container_script(request: BuildRequest) -> str:
    command = shlex.join(request.command)
    source = shlex.quote(request.extraction_source)
    destination = shlex.quote(f"{request.container_output_directory}/{request.artifact_file}")
    artifact_mode = "0555" if request.kind is BuildKind.HOST_VERIFIER else "0444"
    magic_check, identity = _guest_specific_checks(request.kind)
    archive = _archive_script(request)
    companion, expected_names = _companion_script(request)
    names = " ".join(shlex.quote(name) for name in sorted(expected_names))
    maximum_bytes = (
        planner.MAX_PROGRAM_BINARY_BYTES
        if request.kind is BuildKind.GUEST
        else planner.MAX_HOST_BINARY_BYTES
    )
    return f"""
set -euo pipefail
umask 077
export PATH=/pinned-bin:/risc0/toolchains/{RISC0_TOOLCHAIN_DIRECTORY}/bin:/usr/bin:/bin
export HOME=/sandbox-home CARGO_HOME=/cargo CARGO_NET_OFFLINE=true
export RISC0_BUILD_LOCKED=1 RISC0_HOME=/risc0
export CARGO_BUILD_JOBS={planner.BUILD_JOBS} RAYON_NUM_THREADS={planner.BUILD_JOBS}
unset CARGO_ENCODED_RUSTFLAGS RISC0_SKIP_BUILD RUSTFLAGS RUSTUP_TOOLCHAIN
install -d -m 0700 /cargo /sandbox-home
ln -s /opt/cargo-registry /cargo/registry
ln -s /cargo /sandbox-home/.cargo
ln -s /risc0 /sandbox-home/.risc0
printf '%s\n' '[build]' 'jobs = 2' '' '[net]' 'offline = true' '' \
  '[target.x86_64-unknown-linux-gnu]' 'linker = "/usr/bin/cc"' > /cargo/config.toml
printf '%s\n' '[default_versions]' 'rust = "1.94.1"' > /risc0/settings.toml
[[ "$(pwd -P)" == {planner.CANONICAL_SOURCE_ROOT} ]]
[[ -f {NESTED_CARGO_WRAPPER_CONTAINER_PATH} && -x {NESTED_CARGO_WRAPPER_CONTAINER_PATH} ]]
[[ $(sha256sum -- {NESTED_CARGO_WRAPPER_CONTAINER_PATH} | cut -d' ' -f1) == {NESTED_CARGO_WRAPPER_SHA256} ]]
[[ $CARGO_BUILD_JOBS == {planner.BUILD_JOBS} ]]
[[ $RAYON_NUM_THREADS == {planner.BUILD_JOBS} ]]
[[ -z "$(find {shlex.quote(request.container_target_directory)} -mindepth 1 -print -quit)" ]]
[[ -z "$(find {shlex.quote(request.container_output_directory)} -mindepth 1 -print -quit)" ]]
{command} 1>&2
{archive}
artifact_source={source}
[[ -f $artifact_source && ! -L $artifact_source ]]
install -m {artifact_mode} -- "$artifact_source" {destination}
artifact={destination}
[[ -f $artifact && ! -L $artifact ]]
artifact_bytes=$(stat -c %s -- "$artifact")
[[ $artifact_bytes -gt 0 && $artifact_bytes -le {maximum_bytes} ]]
{magic_check}
artifact_sha256=$(sha256sum -- "$artifact" | cut -d' ' -f1)
{companion}
expected_names=$(printf '%s\n' {names})
actual_names=$(find {shlex.quote(request.container_output_directory)} \
  -mindepth 1 -maxdepth 1 -printf '%f\n' | sort)
[[ $actual_names == "$expected_names" ]]
{identity}
artifact_base64_bytes=$(( (artifact_bytes + 2) / 3 * 4 ))
companion_base64_bytes=$(( (companion_bytes + 2) / 3 * 4 ))
printf 'ZRPF_BUILD_RESULT_V2 {request.kind.value} %s %s %s %s %s %s %s\n' \
  "$artifact_bytes" "$artifact_sha256" "$image_id" "$artifact_base64_bytes" \
  "$companion_bytes" "$companion_sha256" "$companion_base64_bytes"
base64 -w0 -- "$artifact"
printf '\n'
if [[ $companion != '-' ]]; then base64 -w0 -- "$companion"; fi
printf '\nZRPF_END\n'
"""


def _archive_script(request: BuildRequest) -> str:
    if request.kind is not BuildKind.ARCHIVE:
        return ""
    staging = f"{request.container_target_directory}/.zrpf-archive-staging"
    lines = [
        f"archive_staging={shlex.quote(staging)}",
        '[[ ! -e "$archive_staging" ]]',
        'install -d -m 0700 -- "$archive_staging"',
    ]
    names: list[str] = []
    for member in request.archive_members:
        source = shlex.quote(member.source)
        destination = shlex.quote(f"{staging}/{member.name}")
        mode = "0555" if member.executable else "0444"
        lines.extend(
            (
                f"member_source={source}",
                '[[ -f "$member_source" && ! -L "$member_source" ]]',
                'member_bytes=$(stat -c %s -- "$member_source")',
                f"[[ $member_bytes -gt 0 && $member_bytes -le {planner.MAX_HOST_BINARY_BYTES} ]]",
                f'install -m {mode} -- "$member_source" {destination}',
            )
        )
        if member.executable:
            lines.append(f"[[ -x {destination} ]]")
        else:
            lines.extend(
                (
                    f"member_magic=$(od -An -tx1 -N4 -- {destination} | tr -d ' \\n')",
                    "[[ $member_magic == 52304246 ]]",
                )
            )
        names.append(member.name)
    ordered_names = " ".join(shlex.quote(name) for name in sorted(names))
    archive = shlex.quote(request.extraction_source)
    lines.extend(
        (
            f"expected_archive_names=$(printf '%s\\n' {ordered_names})",
            "actual_archive_names=$(find \"$archive_staging\" -mindepth 1 -maxdepth 1 -printf '%f\\n' | sort)",
            '[[ "$actual_archive_names" == "$expected_archive_names" ]]',
            (
                "/usr/bin/tar --create --format=ustar --sort=name --mtime=@0 "
                "--owner=0 --group=0 --numeric-owner --file=- "
                f'--directory="$archive_staging" -- {ordered_names} '
                f"| /usr/bin/gzip -n -9 > {archive}"
            ),
            f"[[ -s {archive} ]]",
        )
    )
    return "\n".join(lines)


def _guest_specific_checks(kind: BuildKind) -> tuple[str, str]:
    if kind is BuildKind.GUEST:
        return (
            "magic=$(od -An -tx1 -N4 -- \"$artifact\" | tr -d ' \\n'); [[ $magic == 52304246 ]];",
            'image_id=$(/risc0/bin/r0vm --elf "$artifact" --id); [[ $image_id =~ ^[0-9a-f]{64}$ ]]',
        )
    return "", "image_id='-'"


def _companion_script(request: BuildRequest) -> tuple[str, list[str]]:
    names = [request.artifact_file]
    if request.companion_artifact_file is None:
        return (
            "companion='-'; companion_bytes=0; companion_sha256='-'",
            names,
        )
    if request.companion_extraction_source is None:
        raise ExecutionError("companion extraction source is absent")
    names.append(request.companion_artifact_file)
    source = shlex.quote(request.companion_extraction_source)
    destination = shlex.quote(
        f"{request.container_output_directory}/{request.companion_artifact_file}"
    )
    return (
        f"companion_source={source}; "
        "[[ -f $companion_source && ! -L $companion_source ]]; "
        f'install -m 0555 -- "$companion_source" {destination}; '
        f"companion={destination}; "
        'companion_bytes=$(stat -c %s -- "$companion"); '
        f"[[ $companion_bytes -gt 0 && $companion_bytes -le {planner.MAX_HOST_BINARY_BYTES} ]]; "
        "companion_sha256=$(sha256sum -- \"$companion\" | cut -d' ' -f1)",
        names,
    )


_parse_runner_payload = runner_protocol.parse_runner_payload
_parse_runner_result = runner_protocol.parse_runner_result
_materialize_runner_payload = runner_protocol.materialize_runner_payload
_write_new_output = runner_protocol.write_new_file
_require_output_name = runner_protocol.require_output_name

_validate_resource_policy = runner_resources.validate_resource_policy
_validate_build_request_resources = runner_resources.validate_build_request


def _inspect_confirms_absent(
    result: Any,
    container_name: str,
) -> bool:
    # Docker releases differ on whether a failed formatted inspect emits no
    # stdout or the format template's terminating newline.  Accept only those
    # two exact empty representations alongside the exact missing-container
    # diagnostic.
    if result.returncode == 0 or result.stdout not in (b"", b"\n"):
        return False
    expected = {
        f"Error: No such container: {container_name}\n".encode("ascii"),
        f"Error response from daemon: No such container: {container_name}\n".encode("ascii"),
    }
    return result.returncode == 1 and result.stderr in expected


def _inspect_confirms_exact_id(result: Any, container_id: str) -> bool:
    return (
        result.returncode == 0
        and not result.stderr
        and result.stdout == (container_id + "\n").encode("ascii")
    )


def _inspect_reports_one_id(result: Any) -> bool:
    return (
        result.returncode == 0
        and not result.stderr
        and re.fullmatch(rb"[0-9a-f]{64}\n", result.stdout) is not None
    )


def _require_name_absent_after_cleanup(
    runner: DockerBuildRunner,
    container_name: str,
) -> None:
    try:
        inspected = runner._inspect_container(container_name)
    except (OSError, RuntimeError) as exc:
        raise ExecutionError(f"container post-cleanup inspection failed: {container_name}") from exc
    if not _inspect_confirms_absent(inspected, container_name):
        raise ExecutionError(f"container name rebound during cleanup: {container_name}")


def _read_container_id(path: Path) -> str | None:
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        descriptor = os.open(path, flags)
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise ExecutionError("container ID file is unavailable") from exc
    try:
        before = os.fstat(descriptor)
        if (
            not stat.S_ISREG(before.st_mode)
            or before.st_uid != os.getuid()
            or before.st_nlink != 1
            or before.st_size != 64
            or stat.S_IMODE(before.st_mode) & (stat.S_IWGRP | stat.S_IWOTH)
        ):
            raise ExecutionError("container ID file identity rejected")
        raw = os.read(descriptor, 65)
        after = os.fstat(descriptor)
        path_after = path.lstat()
    except OSError as exc:
        raise ExecutionError("container ID file read failed") from exc
    finally:
        os.close(descriptor)
    if (
        _stable_container_id_file_facts(before) != _stable_container_id_file_facts(after)
        or _stable_container_id_file_facts(before) != _stable_container_id_file_facts(path_after)
        or re.fullmatch(rb"[0-9a-f]{64}", raw) is None
    ):
        raise ExecutionError("container ID file changed or is malformed")
    return raw.decode("ascii")


def _stable_container_id_file_facts(facts: os.stat_result) -> tuple[int, ...]:
    return (
        facts.st_dev,
        facts.st_ino,
        facts.st_mode,
        facts.st_uid,
        facts.st_gid,
        facts.st_nlink,
        facts.st_size,
        facts.st_mtime_ns,
        facts.st_ctime_ns,
    )


def _canonical_directory(path: Path, label: str) -> Path:
    try:
        resolved = path.resolve(strict=True)
        facts = path.lstat()
    except OSError as exc:
        raise ExecutionError(f"{label} is unavailable") from exc
    if resolved != path or stat.S_ISLNK(facts.st_mode) or not stat.S_ISDIR(facts.st_mode):
        raise ExecutionError(f"{label} must be a canonical real directory")
    return path


def _canonical_executable(path: Path, label: str) -> Path:
    try:
        resolved = path.resolve(strict=True)
        facts = path.lstat()
    except OSError as exc:
        raise ExecutionError(f"{label} is unavailable") from exc
    if (
        resolved != path
        or stat.S_ISLNK(facts.st_mode)
        or not stat.S_ISREG(facts.st_mode)
        or not os.access(path, os.X_OK)
    ):
        raise ExecutionError(f"{label} must be a canonical regular executable")
    return path


def _create_private_directory(path: Path) -> None:
    if path.exists() or path.is_symlink():
        raise ExecutionError("runner directory must begin absent")
    path.mkdir(mode=0o700)
    facts = path.lstat()
    if not stat.S_ISDIR(facts.st_mode) or stat.S_IMODE(facts.st_mode) != 0o700:
        raise ExecutionError("runner directory creation rejected")


def _require_safe_mount_path(path: Path) -> None:
    if any(character in path.as_posix() for character in ",:\n\r\0"):
        raise ExecutionError("mount path contains a forbidden character")


def _mount(source: Path, target: str, *, readonly: bool) -> str:
    suffix = ",readonly" if readonly else ""
    return f"type=bind,source={source},target={target}{suffix}"


def _source_commit_epoch(repo_root: Path, source_commit: str) -> str:
    result = planner._run_git(
        repo_root,
        ["show", "-s", "--format=%ct", source_commit],
        maximum_stdout=128,
    )
    try:
        value = result.stdout.decode("ascii", errors="strict").strip()
    except UnicodeDecodeError as exc:
        raise ExecutionError("source commit epoch is malformed") from exc
    if re.fullmatch(r"[0-9]{1,20}", value) is None:
        raise ExecutionError("source commit epoch is malformed")
    return value


def _container_name(request: BuildRequest) -> str:
    digest = hashlib.sha256(
        f"{request.source_commit}:{request.pass_id}:{request.target_directory}".encode()
    ).hexdigest()[:20]
    return f"zrpf-v6-{digest}"
