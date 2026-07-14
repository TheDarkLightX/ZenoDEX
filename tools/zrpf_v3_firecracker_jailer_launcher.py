"""Candidate one-shot Firecracker jailer control with granular non-claims.

The control binds pinned executable and namespace handles to one exact,
precreated cgroup-v2 leaf before invoking the jailer. Artifact staging,
namespace creation, output validation, and live privileged evidence remain
separate obligations. Jailer still reopens governed paths; immutable root-owned
staging and descriptor-bound execution handoff are required before promotion.
The V2 finish document binds its reported teardown to the exact canonical
launch document, cgroup identity, jailer PID, and observed process count.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Protocol

from tools import zrpf_v3_firecracker_cgroup_v2 as cgroup_v2
from tools.zrpf_v3_firecracker_jail_staging import PreparedJailRootV2
from tools.zrpf_v3_firecracker_netns import (
    PinnedNetworkNamespaceV1,
    open_pinned_network_namespace,
)
from tools.zrpf_v3_firecracker_trusted_runtime import (
    ExecutableExpectationV1,
    JailerLauncherReject,
    PinnedExecutableV1,
    open_pinned_executable,
    verify_fresh_chroot_target,
)

__all__ = [
    "ExecutableExpectationV1",
    "CompletedPreparedJailerRunV2",
    "JailerLaunchSpecV1",
    "PreparedJailerLaunchSpecV2",
    "JailerLauncherReject",
    "PinnedExecutableV1",
    "PinnedNetworkNamespaceV1",
    "open_pinned_executable",
    "open_pinned_network_namespace",
    "run_candidate_jailer_process_control",
    "run_prepared_jailer_process_control_v2",
    "verify_fresh_chroot_target",
]

OUTPUT_SIZE_BYTES = 16_777_216
DEFAULT_NOFILE_LIMIT = 64
FIRECRACKER_SHA256 = "2fd0171309af7e24cf8dafc8a6f921c1434c49b5f9349bb996b7ed0a4deb8aa7"
FIRECRACKER_SIZE_BYTES = 3_527_456
JAILER_SHA256 = "1f3a0c1fe86212d0001819bfe0819071c01208b3ccc9398c3b3bc1b84cf21edd"
JAILER_SIZE_BYTES = 2_181_264
_JAIL_ID = re.compile(r"[a-z0-9][a-z0-9-]{7,63}\Z")


class ProcessHandle(Protocol):
    pid: int

    def poll(self) -> int | None: ...

    def wait(self, timeout: float | None = None) -> int: ...

    def kill(self) -> None: ...


class ExecutableControl(Protocol):
    path: Path

    def reverify(self) -> None: ...


class CgroupIdentity(Protocol):
    @property
    def relative_path(self) -> str: ...


class CgroupLeafControl(Protocol):
    @property
    def identity(self) -> CgroupIdentity: ...

    def verify_prelaunch(self) -> None: ...

    def verify_active_descendant_set(self, supervisor_pid: int) -> frozenset[int]: ...

    def terminate_and_remove(self, *, timeout_ns: int) -> None: ...


class NetworkNamespaceControl(Protocol):
    path: Path

    def reverify_path(self) -> None: ...

    def verify_empty(self) -> None: ...

    def verify_exact_process_set(self, pids: frozenset[int]) -> None: ...


class LaunchSpecControl(Protocol):
    @property
    def jail_id(self) -> str: ...

    @property
    def uid(self) -> int: ...

    @property
    def gid(self) -> int: ...

    @property
    def chroot_base_dir(self) -> Path: ...

    def argv(
        self,
        *,
        jailer: ExecutableControl,
        firecracker: ExecutableControl,
        cgroup_leaf: CgroupLeafControl,
        network_namespace: NetworkNamespaceControl,
    ) -> tuple[str, ...]: ...


class PreparedJailControl(Protocol):
    def verify_prelaunch(self) -> None: ...

    def read_validated_output_after_exit(self) -> bytes: ...

    def cleanup_after_teardown(self) -> None: ...

    def abandon_before_launch(self) -> None: ...


@dataclass(frozen=True, slots=True)
class JailerLaunchSpecV1:
    """Exact jailer invocation parameters; no caller-supplied option list."""

    jail_id: str
    uid: int
    gid: int
    chroot_base_dir: Path
    config_path_in_jail: str = "/config.json"
    nofile_limit: int = DEFAULT_NOFILE_LIMIT

    def __post_init__(self) -> None:
        if _JAIL_ID.fullmatch(self.jail_id) is None:
            raise JailerLauncherReject("jailer_id_invalid")
        if any(
            type(value) is not int or not 1 <= value <= (1 << 31) - 1
            for value in (self.uid, self.gid)
        ):
            raise JailerLauncherReject("jailer_uid_gid_invalid")
        if not self.chroot_base_dir.is_absolute():
            raise JailerLauncherReject("jailer_chroot_base_not_absolute")
        if self.config_path_in_jail != "/config.json":
            raise JailerLauncherReject("jailer_config_path_invalid")
        if not 32 <= self.nofile_limit <= 1024:
            raise JailerLauncherReject("jailer_nofile_limit_invalid")

    def argv(
        self,
        *,
        jailer: ExecutableControl,
        firecracker: ExecutableControl,
        cgroup_leaf: CgroupLeafControl,
        network_namespace: NetworkNamespaceControl,
    ) -> tuple[str, ...]:
        relative_cgroup = cgroup_leaf.identity.relative_path.removeprefix("/")
        arguments = (
            jailer.path.as_posix(),
            "--id",
            self.jail_id,
            "--exec-file",
            firecracker.path.as_posix(),
            "--uid",
            str(self.uid),
            "--gid",
            str(self.gid),
            "--cgroup-version=2",
            "--parent-cgroup",
            relative_cgroup,
            "--chroot-base-dir",
            self.chroot_base_dir.as_posix(),
            "--netns",
            network_namespace.path.as_posix(),
            "--new-pid-ns",
            "--resource-limit",
            f"fsize={OUTPUT_SIZE_BYTES}",
            "--resource-limit",
            f"no-file={self.nofile_limit}",
            "--",
            "--no-api",
            "--config-file",
            self.config_path_in_jail,
        )
        cgroup_v2.validate_jailer_cgroup_arguments(list(arguments))
        if "--daemonize" in arguments or "--no-seccomp" in arguments:
            raise JailerLauncherReject("jailer_forbidden_option_constructed")
        return arguments


@dataclass(frozen=True, slots=True)
class PreparedJailerLaunchSpecV2:
    """Exact Jailer invocation for a supervisor-prepared resource directory."""

    jail_id: str
    uid: int
    gid: int
    chroot_base_dir: Path
    nofile_limit: int = DEFAULT_NOFILE_LIMIT

    def __post_init__(self) -> None:
        if _JAIL_ID.fullmatch(self.jail_id) is None:
            raise JailerLauncherReject("jailer_id_invalid")
        if any(
            type(value) is not int or not 1 <= value <= (1 << 31) - 1
            for value in (self.uid, self.gid)
        ):
            raise JailerLauncherReject("jailer_uid_gid_invalid")
        if not self.chroot_base_dir.is_absolute():
            raise JailerLauncherReject("jailer_chroot_base_not_absolute")
        if not 32 <= self.nofile_limit <= 1024:
            raise JailerLauncherReject("jailer_nofile_limit_invalid")

    def argv(
        self,
        *,
        jailer: ExecutableControl,
        firecracker: ExecutableControl,
        cgroup_leaf: CgroupLeafControl,
        network_namespace: NetworkNamespaceControl,
    ) -> tuple[str, ...]:
        relative_cgroup = cgroup_leaf.identity.relative_path.removeprefix("/")
        arguments = (
            jailer.path.as_posix(),
            "--id",
            self.jail_id,
            "--exec-file",
            firecracker.path.as_posix(),
            "--uid",
            str(self.uid),
            "--gid",
            str(self.gid),
            "--cgroup-version=2",
            "--parent-cgroup",
            relative_cgroup,
            "--chroot-base-dir",
            self.chroot_base_dir.as_posix(),
            "--netns",
            network_namespace.path.as_posix(),
            "--new-pid-ns",
            "--resource-limit",
            f"fsize={OUTPUT_SIZE_BYTES}",
            "--resource-limit",
            f"no-file={self.nofile_limit}",
            "--",
            "--no-api",
            "--config-file",
            "/resources/config.json",
        )
        cgroup_v2.validate_jailer_cgroup_arguments(list(arguments))
        if "--daemonize" in arguments or "--no-seccomp" in arguments:
            raise JailerLauncherReject("jailer_forbidden_option_constructed")
        return arguments


@dataclass(frozen=True, slots=True)
class CompletedPreparedJailerRunV2:
    """Ordinary output and lifecycle data; never an authority capability."""

    launch_observation: dict[str, Any]
    finish_observation: dict[str, Any]
    output_device_bytes: bytes


@dataclass(frozen=True, slots=True)
class _JailerLaunchObservationV1:
    """Observed process-placement facts; output authority remains external."""

    jailer_pid: int
    process_set: frozenset[int]
    cgroup_relative_path: str

    def to_document(self) -> dict[str, Any]:
        return {
            "authority": dict(cgroup_v2.authority_nonclaims()),
            "cgroup_relative_path": self.cgroup_relative_path,
            "control_facts": {
                "cgroup_descendant_set_verified": True,
                "executable_bytes_reverified_after_spawn": True,
                "network_namespace_membership_verified": True,
            },
            "jailer_pid": self.jailer_pid,
            "observed_process_count": len(self.process_set),
            "schema": "zenodex/zrpf_firecracker_jailer_launch_observation/v1",
            "scope": "live_process_placement_control_only",
        }


def run_candidate_jailer_process_control(
    *,
    spec: JailerLaunchSpecV1,
    jailer: PinnedExecutableV1,
    firecracker: PinnedExecutableV1,
    cgroup_leaf: cgroup_v2.CgroupLeafV1,
    network_namespace: PinnedNetworkNamespaceV1,
    process_timeout_seconds: float,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Own one candidate Jailer lifecycle using only concrete OS controls."""

    if (
        type(jailer) is not PinnedExecutableV1
        or type(firecracker) is not PinnedExecutableV1
        or type(cgroup_leaf) is not cgroup_v2.CgroupLeafV1
        or type(network_namespace) is not PinnedNetworkNamespaceV1
    ):
        raise JailerLauncherReject("jailer_candidate_control_type_invalid")
    if (
        jailer.trusted_uid != 0
        or firecracker.trusted_uid != 0
        or cgroup_leaf.trusted_uid != 0
        or network_namespace.trusted_uid != 0
    ):
        raise JailerLauncherReject("jailer_candidate_control_not_root_owned")
    try:
        verify_fresh_chroot_target(
            chroot_base_dir=spec.chroot_base_dir,
            exec_file_path=firecracker.path,
            jail_id=spec.jail_id,
        )
    except BaseException:
        _cleanup_failed_launch(cgroup_leaf, None)
        raise
    process, observation = _launch_jailer_process_control_for_test(
        spec=spec,
        jailer=jailer,
        firecracker=firecracker,
        cgroup_leaf=cgroup_leaf,
        network_namespace=network_namespace,
    )
    report = _finish_jailer_process_control_for_test(
        process=process,
        cgroup_leaf=cgroup_leaf,
        network_namespace=network_namespace,
        observation=observation,
        process_timeout_seconds=process_timeout_seconds,
    )
    return observation.to_document(), report


def run_prepared_jailer_process_control_v2(
    *,
    spec: PreparedJailerLaunchSpecV2,
    prepared_jail: PreparedJailRootV2,
    jailer: PinnedExecutableV1,
    firecracker: PinnedExecutableV1,
    cgroup_leaf: cgroup_v2.CgroupLeafV1,
    network_namespace: PinnedNetworkNamespaceV1,
    process_timeout_seconds: float,
) -> CompletedPreparedJailerRunV2:
    """Run one exact prepared jail and validate its committed outer output.

    This function closes the supervisor-prepared path handoff.  It does not
    authenticate a Spot V7 payload and cannot mint any integration capability.
    A failed or uncertain process teardown leaves the jail quarantined instead
    of deleting files that a surviving process might still use.
    """

    if (
        type(spec) is not PreparedJailerLaunchSpecV2
        or type(prepared_jail) is not PreparedJailRootV2
        or type(jailer) is not PinnedExecutableV1
        or type(firecracker) is not PinnedExecutableV1
        or type(cgroup_leaf) is not cgroup_v2.CgroupLeafV1
        or type(network_namespace) is not PinnedNetworkNamespaceV1
    ):
        raise JailerLauncherReject("jailer_prepared_control_type_invalid")
    if (
        os.geteuid() != 0
        or jailer.trusted_uid != 0
        or firecracker.trusted_uid != 0
        or cgroup_leaf.trusted_uid != 0
        or network_namespace.trusted_uid != 0
        or prepared_jail.spec.trusted_uid != 0
    ):
        raise JailerLauncherReject("jailer_prepared_control_not_root_owned")
    _require_prepared_jail_matches_launch(spec, prepared_jail, firecracker)
    return _complete_prepared_jailer_lifecycle_for_test(
        prepared_jail=prepared_jail,
        launch=lambda: _launch_jailer_process_control_for_test(
            spec=spec,
            jailer=jailer,
            firecracker=firecracker,
            cgroup_leaf=cgroup_leaf,
            network_namespace=network_namespace,
        ),
        finish=lambda process, observation: _finish_jailer_process_control_for_test(
            process=process,
            cgroup_leaf=cgroup_leaf,
            network_namespace=network_namespace,
            observation=observation,
            process_timeout_seconds=process_timeout_seconds,
        ),
    )


def _complete_prepared_jailer_lifecycle_for_test(
    *,
    prepared_jail: PreparedJailControl,
    launch: Callable[[], tuple[ProcessHandle, _JailerLaunchObservationV1]],
    finish: Callable[[ProcessHandle, _JailerLaunchObservationV1], dict[str, Any]],
) -> CompletedPreparedJailerRunV2:
    """Complete the data-only lifecycle; injected controls remain test-only."""

    try:
        prepared_jail.verify_prelaunch()
    except BaseException:
        prepared_jail.abandon_before_launch()
        raise
    # After launch begins, any uncertain launch or teardown leaves the jail in
    # quarantine. Deleting it could race a surviving process.
    process, observation = launch()
    report = finish(process, observation)
    try:
        output = prepared_jail.read_validated_output_after_exit()
    finally:
        prepared_jail.cleanup_after_teardown()
    return CompletedPreparedJailerRunV2(
        launch_observation=observation.to_document(),
        finish_observation=report,
        output_device_bytes=output,
    )


def _require_prepared_jail_matches_launch(
    spec: PreparedJailerLaunchSpecV2,
    prepared_jail: PreparedJailRootV2,
    firecracker: PinnedExecutableV1,
) -> None:
    staged = prepared_jail.spec
    if (
        staged.jail_id,
        staged.firecracker_file_name,
        staged.chroot_base_dir,
        staged.runtime_uid,
        staged.runtime_gid,
        staged.config_path_in_jail,
    ) != (
        spec.jail_id,
        firecracker.path.name,
        spec.chroot_base_dir,
        spec.uid,
        spec.gid,
        "/resources/config.json",
    ):
        raise JailerLauncherReject("jailer_prepared_stage_binding_mismatch")


def _launch_jailer_process_control_for_test(
    *,
    spec: LaunchSpecControl,
    jailer: ExecutableControl,
    firecracker: ExecutableControl,
    cgroup_leaf: CgroupLeafControl,
    network_namespace: NetworkNamespaceControl,
    spawn: Callable[[tuple[str, ...]], ProcessHandle] | None = None,
    membership_timeout_ns: int = 2_000_000_000,
    monotonic_ns: Callable[[], int] = time.monotonic_ns,
    wait_once: Callable[[], None] | None = None,
) -> tuple[ProcessHandle, _JailerLaunchObservationV1]:
    """Spawn the exact jailer command and verify its live placement boundary."""

    if not 1_000_000 <= membership_timeout_ns <= 30_000_000_000:
        raise JailerLauncherReject("jailer_membership_timeout_invalid")
    process: ProcessHandle | None = None
    try:
        arguments = spec.argv(
            jailer=jailer,
            firecracker=firecracker,
            cgroup_leaf=cgroup_leaf,
            network_namespace=network_namespace,
        )
        _verify_prelaunch_boundaries(jailer, firecracker, cgroup_leaf, network_namespace)
        process = (spawn if spawn is not None else _spawn_no_output)(arguments)
        if type(process.pid) is not int or process.pid <= 0:
            raise JailerLauncherReject("jailer_spawn_pid_invalid")
        jailer.reverify()
        firecracker.reverify()
        network_namespace.reverify_path()
        process_set = _wait_for_process_placement(
            process=process,
            cgroup_leaf=cgroup_leaf,
            membership_timeout_ns=membership_timeout_ns,
            monotonic_ns=monotonic_ns,
            wait_once=wait_once,
        )
        network_namespace.verify_exact_process_set(process_set)
    except BaseException:
        _cleanup_failed_launch(cgroup_leaf, process)
        raise
    return process, _JailerLaunchObservationV1(
        jailer_pid=process.pid,
        process_set=process_set,
        cgroup_relative_path=cgroup_leaf.identity.relative_path,
    )


def _finish_jailer_process_control_for_test(
    *,
    process: ProcessHandle,
    cgroup_leaf: CgroupLeafControl,
    network_namespace: NetworkNamespaceControl,
    observation: _JailerLaunchObservationV1,
    process_timeout_seconds: float,
    teardown_timeout_ns: int = 5_000_000_000,
) -> dict[str, Any]:
    """Wait once, kill the complete cgroup, and report control facts only."""

    if not 0.1 <= process_timeout_seconds <= 300.0:
        raise JailerLauncherReject("jailer_process_timeout_invalid")
    if (
        type(observation) is not _JailerLaunchObservationV1
        or process.pid != observation.jailer_pid
        or process.pid not in observation.process_set
        or cgroup_leaf.identity.relative_path != observation.cgroup_relative_path
    ):
        _cleanup_failed_launch(cgroup_leaf, process)
        raise JailerLauncherReject("jailer_finish_launch_observation_mismatch")
    timed_out = False
    wait_failed = False
    exit_code: int | None = None
    try:
        try:
            exit_code = process.wait(timeout=process_timeout_seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
        except OSError:
            wait_failed = True
    finally:
        try:
            cgroup_leaf.terminate_and_remove(timeout_ns=teardown_timeout_ns)
        except (cgroup_v2.CgroupV2Reject, OSError) as exc:
            _fallback_kill_and_reap(process)
            raise JailerLauncherReject("jailer_cgroup_teardown_failed") from exc
    network_namespace.reverify_path()
    network_namespace.verify_empty()
    if timed_out:
        _reap_after_cgroup_kill(process)
        raise JailerLauncherReject("jailer_process_timeout")
    if wait_failed:
        _reap_after_cgroup_kill(process)
        raise JailerLauncherReject("jailer_process_wait_failed")
    if type(exit_code) is not int:
        raise JailerLauncherReject("jailer_exit_status_invalid")
    return _finish_observation_document_v2(
        observation=observation,
        exit_code=exit_code,
    )


def _finish_observation_document_v2(
    *,
    observation: _JailerLaunchObservationV1,
    exit_code: int,
) -> dict[str, Any]:
    """Derive the canonical-data finish document bound to one launch record."""

    if type(observation) is not _JailerLaunchObservationV1:
        raise TypeError("observation must be exact _JailerLaunchObservationV1")
    if type(exit_code) is not int or not -(1 << 31) <= exit_code <= (1 << 31) - 1:
        raise JailerLauncherReject("jailer_exit_status_invalid")
    launch_document = observation.to_document()
    launch_observation_sha256 = hashlib.sha256(
        _canonical_observation_bytes_v1(launch_document)
    ).hexdigest()
    return {
        "authority": launch_document["authority"],
        "cgroup_relative_path": observation.cgroup_relative_path,
        "control_facts": {
            "cgroup_populated_zero_verified": True,
            "cgroup_removed_after_kill": True,
            "network_namespace_path_identity_preserved": True,
            "process_exit_observed": True,
        },
        "exit_code": exit_code,
        "jailer_pid": observation.jailer_pid,
        "launch_observation_sha256": launch_observation_sha256,
        "observed_process_count": len(observation.process_set),
        "schema": "zenodex/zrpf_firecracker_jailer_finish_observation/v2",
        "scope": "live_process_exit_and_exact_launch_teardown_control_only",
    }


def _canonical_observation_bytes_v1(document: object) -> bytes:
    return (
        json.dumps(
            document,
            ensure_ascii=True,
            separators=(",", ":"),
            sort_keys=True,
        )
        + "\n"
    ).encode("ascii")


def _verify_prelaunch_boundaries(
    jailer: ExecutableControl,
    firecracker: ExecutableControl,
    cgroup_leaf: CgroupLeafControl,
    network_namespace: NetworkNamespaceControl,
) -> None:
    jailer.reverify()
    firecracker.reverify()
    network_namespace.reverify_path()
    network_namespace.verify_empty()
    cgroup_leaf.verify_prelaunch()


def _wait_for_process_placement(
    *,
    process: ProcessHandle,
    cgroup_leaf: CgroupLeafControl,
    membership_timeout_ns: int,
    monotonic_ns: Callable[[], int],
    wait_once: Callable[[], None] | None,
) -> frozenset[int]:
    deadline = monotonic_ns() + membership_timeout_ns
    pause = wait_once if wait_once is not None else lambda: time.sleep(0.005)
    transient = {
        "cgroup_active_populated_mismatch",
        "cgroup_active_process_set_mismatch",
        "cgroup_boundary_file_open_failed",
    }
    while True:
        try:
            return cgroup_leaf.verify_active_descendant_set(process.pid)
        except cgroup_v2.CgroupV2Reject as exc:
            if (
                exc.code not in transient
                or process.poll() is not None
                or monotonic_ns() >= deadline
            ):
                raise JailerLauncherReject("jailer_cgroup_membership_not_established") from exc
            pause()


def _cleanup_failed_launch(
    cgroup_leaf: CgroupLeafControl,
    process: ProcessHandle | None,
) -> None:
    failed = False
    try:
        cgroup_leaf.terminate_and_remove(timeout_ns=5_000_000_000)
    except (cgroup_v2.CgroupV2Reject, OSError):
        failed = True
    if process is not None:
        if failed and process.poll() is None:
            try:
                process.kill()
            except OSError:
                failed = True
        try:
            process.wait(timeout=5.0)
        except (subprocess.TimeoutExpired, OSError):
            failed = True
    if failed:
        raise JailerLauncherReject("jailer_failed_launch_cleanup_failed")


def _reap_after_cgroup_kill(process: ProcessHandle) -> None:
    try:
        process.wait(timeout=5.0)
    except (subprocess.TimeoutExpired, OSError) as exc:
        raise JailerLauncherReject("jailer_process_not_reaped_after_cgroup_kill") from exc


def _fallback_kill_and_reap(process: ProcessHandle) -> None:
    """Best-effort parent cleanup when whole-cgroup teardown itself rejects."""

    try:
        running = process.poll() is None
    except OSError as exc:
        raise JailerLauncherReject("jailer_parent_fallback_status_failed") from exc
    if running:
        try:
            process.kill()
        except OSError as exc:
            raise JailerLauncherReject("jailer_parent_fallback_kill_failed") from exc
    try:
        process.wait(timeout=5.0)
    except (subprocess.TimeoutExpired, OSError) as exc:
        raise JailerLauncherReject("jailer_parent_fallback_reap_failed") from exc


def _spawn_no_output(arguments: tuple[str, ...]) -> subprocess.Popen[bytes]:
    try:
        return subprocess.Popen(
            arguments,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            close_fds=True,
            cwd="/",
            env={},
        )
    except OSError as exc:
        raise JailerLauncherReject("jailer_spawn_failed") from exc
