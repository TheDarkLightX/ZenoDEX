"""Pinned no-network Docker runner for the Spot V6 identity rebuild."""

from __future__ import annotations

import hashlib
import os
import re
import shlex
import stat
from pathlib import Path

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner
from tools import zrpf_v3_replay_environment as replay_environment
from tools import zrpf_v3_replay_process as process_runner
from tools.zrpf_v6_identity_executor_types import (
    BuildKind,
    BuildRequest,
    BuildResult,
    ExecutionError,
)
from tools.zrpf_v6_identity_source_snapshot import read_bounded_regular

MAX_BUILD_OUTPUT_BYTES = 32 * 1024 * 1024
BUILD_TIMEOUT_SECONDS = 4 * 60 * 60
RISC0_TOOLCHAIN_DIRECTORY = "v1.94.1-rust-x86_64-unknown-linux-gnu"
RISC0_EXTENSION_DIRECTORY = "v3.0.5-cargo-risczero-x86_64-unknown-linux-gnu"


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
        self._validate_toolchain()
        self._validate_image()

    def run(self, request: BuildRequest) -> BuildResult:
        if request.target_directory.exists() or request.output_directory.exists():
            raise ExecutionError("runner target and output must begin absent")
        _create_private_directory(request.target_directory)
        _create_private_directory(request.output_directory)
        container_name = _container_name(request)
        command = self._docker_command(request, container_name)
        completed = False
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
            parsed = _parse_runner_result(result.stdout, request.kind)
            completed = True
            return parsed
        except (OSError, RuntimeError) as exc:
            raise ExecutionError(f"{request.pass_id} container build failed") from exc
        finally:
            if not completed:
                self._force_remove_container(container_name)

    def _validate_toolchain(self) -> None:
        expected = {
            self._toolchain / "bin/cargo": planner.TOOLCHAIN["outer_cargo_sha256"],
            self._toolchain / "bin/rustc": planner.TOOLCHAIN["rustc_sha256"],
            self._extension / "r0vm": planner.TOOLCHAIN["r0vm_sha256"],
            self._extension / "cargo-risczero": planner.TOOLCHAIN[
                "cargo_risczero_sha256"
            ],
        }
        for path, digest in expected.items():
            raw = read_bounded_regular(path, f"pinned tool {path.name}", 256 << 20)
            if hashlib.sha256(raw).hexdigest() != digest:
                raise ExecutionError(f"pinned tool SHA-256 mismatch: {path.name}")
        for component in ("cache", "index", "src"):
            _canonical_directory(self._registry / component, f"Cargo registry {component}")

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
        if result.returncode != 0 or result.stderr or result.stdout != (
            planner.BUILD_IMAGE + "\n"
        ).encode("ascii"):
            raise ExecutionError("pinned build image is unavailable or mismatched")

    def _docker_command(self, request: BuildRequest, container_name: str) -> list[str]:
        for path in (
            request.source_snapshot,
            request.target_directory,
            request.output_directory,
            self._toolchain,
            self._extension,
            self._registry,
        ):
            _require_safe_mount_path(path)
        return [
            str(self._docker),
            "run",
            "--rm",
            "--name",
            container_name,
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
            *_tmpfs_arguments(),
            *_mount_arguments(request, self._toolchain, self._extension, self._registry),
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

    def _force_remove_container(self, container_name: str) -> None:
        try:
            process_runner.run_bounded(
                process_runner.ProcessRequest(
                    command=(str(self._docker), "rm", "--force", container_name),
                    cwd=self._risc0_home,
                    env=replay_environment.clean_environment(),
                    timeout_seconds=30,
                    output_limit_bytes=4_096,
                    profile=process_runner.ProcessProfile.TOOL,
                )
            )
        except (OSError, RuntimeError):
            pass


def _tmpfs_arguments() -> list[str]:
    uid = os.getuid()
    gid = os.getgid()
    return [
        "--tmpfs",
        f"/tmp:rw,nosuid,nodev,noexec,size=256m,mode=1777,uid={uid},gid={gid}",
        "--tmpfs",
        f"/cargo:rw,nosuid,nodev,noexec,size=512m,mode=0700,uid={uid},gid={gid}",
        "--tmpfs",
        f"/sandbox-home:rw,nosuid,nodev,noexec,size=4m,mode=0700,uid={uid},gid={gid}",
        "--tmpfs",
        f"/risc0:rw,nosuid,nodev,noexec,size=4m,mode=0700,uid={uid},gid={gid}",
    ]


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
        "--mount",
        _mount(
            request.target_directory,
            request.container_target_directory,
            readonly=False,
        ),
        "--mount",
        _mount(
            request.output_directory,
            request.container_output_directory,
            readonly=False,
        ),
    ]


def _container_script(request: BuildRequest) -> str:
    command = shlex.join(request.command)
    source = shlex.quote(request.extraction_source)
    destination = shlex.quote(
        f"{request.container_output_directory}/{request.artifact_file}"
    )
    artifact_mode = "0444" if request.kind is BuildKind.GUEST else "0555"
    magic_check, identity = _guest_specific_checks(request.kind)
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
export PATH=/risc0/toolchains/{RISC0_TOOLCHAIN_DIRECTORY}/bin:/usr/bin:/bin
export HOME=/sandbox-home CARGO_HOME=/cargo CARGO_NET_OFFLINE=true
export RISC0_BUILD_LOCKED=1 RISC0_HOME=/risc0
unset CARGO_ENCODED_RUSTFLAGS RISC0_SKIP_BUILD RUSTFLAGS RUSTUP_TOOLCHAIN
install -d -m 0700 /cargo /sandbox-home
ln -s /opt/cargo-registry /cargo/registry
ln -s /cargo /sandbox-home/.cargo
ln -s /risc0 /sandbox-home/.risc0
printf '%s\n' '[build]' 'jobs = 2' '' '[net]' 'offline = true' '' \
  '[target.x86_64-unknown-linux-gnu]' 'linker = "/usr/bin/cc"' > /cargo/config.toml
printf '%s\n' '[default_versions]' 'rust = "1.94.1"' > /risc0/settings.toml
[[ "$(pwd -P)" == {planner.CANONICAL_SOURCE_ROOT} ]]
[[ -z "$(find {shlex.quote(request.container_target_directory)} -mindepth 1 -print -quit)" ]]
[[ -z "$(find {shlex.quote(request.container_output_directory)} -mindepth 1 -print -quit)" ]]
{command} 1>&2
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
printf '%s %s %s\n' "$artifact_bytes" "$artifact_sha256" "$image_id"
"""


def _guest_specific_checks(kind: BuildKind) -> tuple[str, str]:
    if kind is BuildKind.GUEST:
        return (
            "magic=$(od -An -tx1 -N4 -- \"$artifact\" | tr -d ' \\n'); "
            "[[ $magic == 52304246 ]];",
            "image_id=$(/risc0/bin/r0vm --elf \"$artifact\" --id); "
            "[[ $image_id =~ ^[0-9a-f]{64}$ ]]",
        )
    return "", "image_id='-'"


def _companion_script(request: BuildRequest) -> tuple[str, list[str]]:
    names = [request.artifact_file]
    if request.companion_artifact_file is None:
        return "", names
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
        f"install -m 0555 -- \"$companion_source\" {destination};",
        names,
    )


def _parse_runner_result(raw: bytes, kind: BuildKind) -> BuildResult:
    pattern = rb"([1-9][0-9]{0,19}) ([0-9a-f]{64}) ([0-9a-f]{64}|-)\n"
    match = re.fullmatch(pattern, raw)
    if match is None:
        raise ExecutionError("container runner result framing rejected")
    size = int(match.group(1))
    image = match.group(3).decode("ascii")
    if kind is BuildKind.GUEST and image == "-":
        raise ExecutionError("guest runner omitted image ID")
    if kind is BuildKind.HOST_VERIFIER and image != "-":
        raise ExecutionError("host runner returned an image ID")
    return BuildResult(
        artifact_bytes=size,
        artifact_sha256=match.group(2).decode("ascii"),
        image_id=None if image == "-" else image,
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
