"""Executable cgroup-v2 leaf lifecycle for the ZRPF Firecracker jailer.

The privileged supervisor creates one fresh domain leaf, installs an exact
finite resource envelope, verifies the jailer process tree, and kills the
complete leaf before removal. This control carries no replay or production
authority by itself.
"""

from __future__ import annotations

import os
import stat
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

from tools import zrpf_v3_firecracker_cgroup_io as cgroup_io
from tools.zrpf_v3_firecracker_cgroup_contract import (
    LIMIT_FILE_ORDER,
    REQUIRED_CONTROLLERS,
    CgroupLimitsV1,
    CgroupV2Reject,
    authority_nonclaims,
    parse_cpu_set,
    relative_components,
    require_leaf_name,
    validate_jailer_cgroup_arguments,
)

__all__ = [
    "LIMIT_FILE_ORDER",
    "CgroupCreateRequestV1",
    "CgroupLeafIdentityV1",
    "CgroupLeafV1",
    "CgroupLimitsV1",
    "CgroupV2Reject",
    "authority_nonclaims",
    "create_cgroup_leaf",
    "create_cgroup_leaf_from_request",
    "validate_jailer_cgroup_arguments",
]


@dataclass(frozen=True, slots=True)
class CgroupLeafIdentityV1:
    relative_path: str
    device: int
    inode: int


@dataclass(frozen=True, slots=True)
class CgroupCreateRequestV1:
    cgroup_mount: Path
    parent_relative_path: str
    leaf_name: str
    limits: CgroupLimitsV1
    mountinfo_path: Path = Path("/proc/self/mountinfo")
    proc_root: Path = Path("/proc")
    trusted_uid: int = 0


class CgroupLeafV1:
    """Opened fresh leaf whose descriptor remains the path-race authority."""

    def __init__(
        self,
        *,
        parent_fd: int,
        leaf_fd: int,
        leaf_name: str,
        identity: CgroupLeafIdentityV1,
        limits: CgroupLimitsV1,
        proc_root: Path,
        trusted_uid: int,
    ) -> None:
        self._parent_fd = parent_fd
        self._leaf_fd = leaf_fd
        self._leaf_name = leaf_name
        self._identity = identity
        self._limits = limits
        self._proc_root = proc_root
        self._trusted_uid = trusted_uid
        self._closed = False

    @property
    def identity(self) -> CgroupLeafIdentityV1:
        return self._identity

    @property
    def trusted_uid(self) -> int:
        return self._trusted_uid

    def verify_prelaunch(self) -> None:
        self._require_open_identity()
        if cgroup_io.read_value(self._leaf_fd, "cgroup.type") != "domain":
            raise CgroupV2Reject("cgroup_leaf_not_domain")
        if cgroup_io.read_value(self._leaf_fd, "cgroup.subtree_control"):
            raise CgroupV2Reject("cgroup_leaf_subtree_control_not_empty")
        if cgroup_io.read_pids(self._leaf_fd):
            raise CgroupV2Reject("cgroup_leaf_processes_not_empty")
        if cgroup_io.keyed_integer(self._leaf_fd, "cgroup.events", "populated") != 0:
            raise CgroupV2Reject("cgroup_leaf_populated_before_launch")
        if cgroup_io.keyed_integer(self._leaf_fd, "cgroup.stat", "nr_descendants") != 0:
            raise CgroupV2Reject("cgroup_leaf_descendants_before_launch")
        self._verify_limits()

    def verify_active_membership(self, expected_pids: frozenset[int]) -> None:
        """Require the exact expected host process set in the exact leaf."""

        if not expected_pids or any(type(pid) is not int or pid <= 0 for pid in expected_pids):
            raise CgroupV2Reject("cgroup_expected_process_set_invalid")
        self._require_open_identity()
        self._require_no_descendant_cgroups("cgroup_active_descendants_present")
        if cgroup_io.read_pids(self._leaf_fd) != expected_pids:
            raise CgroupV2Reject("cgroup_active_process_set_mismatch")
        if cgroup_io.keyed_integer(self._leaf_fd, "cgroup.events", "populated") != 1:
            raise CgroupV2Reject("cgroup_active_populated_mismatch")
        for pid in sorted(expected_pids):
            if cgroup_io.read_process_cgroup(self._proc_root, pid) != self._identity.relative_path:
                raise CgroupV2Reject("cgroup_process_membership_mismatch")
        self._verify_limits()
        self._require_no_descendant_cgroups("cgroup_active_descendants_present")

    def verify_active_descendant_set(self, supervisor_pid: int) -> frozenset[int]:
        """Verify a stable leaf process set rooted at the spawned jailer PID."""

        if type(supervisor_pid) is not int or supervisor_pid <= 0:
            raise CgroupV2Reject("cgroup_supervisor_pid_invalid")
        self._require_open_identity()
        first = cgroup_io.read_pids(self._leaf_fd)
        if supervisor_pid not in first or len(first) > self._limits.pids_max:
            raise CgroupV2Reject("cgroup_active_process_set_mismatch")
        first_identities = cgroup_io.read_process_identities(self._proc_root, first)
        for pid in sorted(first - {supervisor_pid}):
            if not cgroup_io.is_descendant(pid, supervisor_pid, first, first_identities):
                raise CgroupV2Reject("cgroup_active_non_descendant_process")
        self.verify_active_membership(first)
        if cgroup_io.read_pids(self._leaf_fd) != first:
            raise CgroupV2Reject("cgroup_active_process_set_unstable")
        if cgroup_io.read_process_identities(self._proc_root, first) != first_identities:
            raise CgroupV2Reject("cgroup_active_process_identity_unstable")
        self._require_no_descendant_cgroups("cgroup_active_descendants_present")
        return first

    def terminate_and_remove(
        self,
        *,
        timeout_ns: int,
        monotonic_ns: Callable[[], int] = time.monotonic_ns,
        wait_once: Callable[[], None] | None = None,
    ) -> None:
        """Kill the complete domain leaf and remove it only after populated=0."""

        if not 1_000_000 <= timeout_ns <= 300_000_000_000:
            raise CgroupV2Reject("cgroup_teardown_timeout_invalid")
        self._require_open_identity()
        if cgroup_io.read_value(self._leaf_fd, "cgroup.type") != "domain":
            raise CgroupV2Reject("cgroup_teardown_not_domain")
        cgroup_io.write_control(self._leaf_fd, "cgroup.kill", b"1\n")
        deadline = monotonic_ns() + timeout_ns
        pause = wait_once if wait_once is not None else lambda: time.sleep(0.01)
        while cgroup_io.keyed_integer(self._leaf_fd, "cgroup.events", "populated") != 0:
            if monotonic_ns() >= deadline:
                raise CgroupV2Reject("cgroup_teardown_timeout")
            pause()
        self._verify_empty_before_removal(
            process_code="cgroup_teardown_processes_remain",
            descendant_code="cgroup_teardown_descendants_remain",
        )
        self._verify_limits()
        self._require_open_identity()
        self._remove_empty_leaf()

    def wait_until_empty_and_remove(
        self,
        *,
        timeout_ns: int,
        monotonic_ns: Callable[[], int] = time.monotonic_ns,
        wait_once: Callable[[], None] | None = None,
    ) -> None:
        """Wait for natural process completion and remove without ``cgroup.kill``."""

        if not 1_000_000 <= timeout_ns <= 300_000_000_000:
            raise CgroupV2Reject("cgroup_natural_completion_timeout_invalid")
        self._require_open_identity()
        if cgroup_io.read_value(self._leaf_fd, "cgroup.type") != "domain":
            raise CgroupV2Reject("cgroup_natural_completion_not_domain")
        deadline = monotonic_ns() + timeout_ns
        pause = wait_once if wait_once is not None else lambda: time.sleep(0.01)
        while cgroup_io.keyed_integer(self._leaf_fd, "cgroup.events", "populated") != 0:
            self._require_open_identity()
            self._verify_limits()
            self._require_no_descendant_cgroups("cgroup_natural_completion_descendants_present")
            if monotonic_ns() >= deadline:
                raise CgroupV2Reject("cgroup_natural_completion_timeout")
            pause()
        self._verify_empty_before_removal(
            process_code="cgroup_natural_completion_processes_remain",
            descendant_code="cgroup_natural_completion_descendants_present",
        )
        self._verify_limits()
        self._require_open_identity()
        self._remove_empty_leaf()

    def close_without_removal(self) -> None:
        """Close descriptors without asserting teardown; used only after rejection."""

        if self._leaf_fd >= 0:
            os.close(self._leaf_fd)
            self._leaf_fd = -1
        if self._parent_fd >= 0:
            os.close(self._parent_fd)
            self._parent_fd = -1
        self._closed = True

    def _verify_empty_before_removal(
        self,
        *,
        process_code: str,
        descendant_code: str,
    ) -> None:
        if cgroup_io.read_pids(self._leaf_fd):
            raise CgroupV2Reject(process_code)
        self._require_no_descendant_cgroups(descendant_code)

    def _remove_empty_leaf(self) -> None:
        os.close(self._leaf_fd)
        self._leaf_fd = -1
        _remove_and_require_absent(self._parent_fd, self._leaf_name)
        os.close(self._parent_fd)
        self._parent_fd = -1
        self._closed = True

    def _require_no_descendant_cgroups(self, code: str) -> None:
        if cgroup_io.keyed_integer(self._leaf_fd, "cgroup.stat", "nr_descendants") != 0:
            raise CgroupV2Reject(code)

    def _require_open_identity(self) -> None:
        if self._closed or self._leaf_fd < 0:
            raise CgroupV2Reject("cgroup_leaf_closed")
        opened = os.fstat(self._leaf_fd)
        try:
            current = os.stat(self._leaf_name, dir_fd=self._parent_fd, follow_symlinks=False)
        except OSError as exc:
            raise CgroupV2Reject("cgroup_leaf_path_identity_changed") from exc
        expected = (self._identity.device, self._identity.inode)
        if (opened.st_dev, opened.st_ino) != expected:
            raise CgroupV2Reject("cgroup_leaf_identity_changed")
        if (current.st_dev, current.st_ino) != expected or not stat.S_ISDIR(current.st_mode):
            raise CgroupV2Reject("cgroup_leaf_path_identity_changed")

    def _verify_limits(self) -> None:
        for name, expected in self._limits.file_values().items():
            if cgroup_io.read_value(self._leaf_fd, name) != expected:
                raise CgroupV2Reject("cgroup_numeric_limit_mismatch")


def create_cgroup_leaf(
    *,
    cgroup_mount: Path,
    parent_relative_path: str,
    leaf_name: str,
    limits: CgroupLimitsV1,
    mountinfo_path: Path = Path("/proc/self/mountinfo"),
    proc_root: Path = Path("/proc"),
    trusted_uid: int = 0,
) -> CgroupLeafV1:
    """Compatibility entry point over the typed creation request."""

    return create_cgroup_leaf_from_request(
        CgroupCreateRequestV1(
            cgroup_mount=cgroup_mount,
            parent_relative_path=parent_relative_path,
            leaf_name=leaf_name,
            limits=limits,
            mountinfo_path=mountinfo_path,
            proc_root=proc_root,
            trusted_uid=trusted_uid,
        )
    )


def create_cgroup_leaf_from_request(request: CgroupCreateRequestV1) -> CgroupLeafV1:
    """Create and verify one exact fresh leaf under a prepared cgroup-v2 parent."""

    require_leaf_name(request.leaf_name)
    components = relative_components(request.parent_relative_path)
    mount_fd = cgroup_io.open_trusted_directory(
        request.cgroup_mount,
        trusted_uid=request.trusted_uid,
    )
    try:
        cgroup_io.require_cgroup2_mount(
            request.cgroup_mount,
            mount_fd,
            os.fstat(mount_fd),
            request.mountinfo_path,
        )
        parent_fd = cgroup_io.walk_directories(
            mount_fd,
            components,
            trusted_uid=request.trusted_uid,
        )
        return _create_leaf_under_parent(parent_fd, components, request)
    finally:
        os.close(mount_fd)


def _create_leaf_under_parent(
    parent_fd: int,
    components: tuple[str, ...],
    request: CgroupCreateRequestV1,
) -> CgroupLeafV1:
    leaf_fd = -1
    created = False
    try:
        _verify_parent_controller_contract(parent_fd, request.limits)
        try:
            os.mkdir(request.leaf_name, 0o755, dir_fd=parent_fd)
        except FileExistsError as exc:
            raise CgroupV2Reject("cgroup_leaf_not_fresh") from exc
        except OSError as exc:
            raise CgroupV2Reject("cgroup_leaf_create_failed") from exc
        created = True
        leaf_fd = cgroup_io.open_directory_at(
            parent_fd,
            request.leaf_name,
            trusted_uid=request.trusted_uid,
        )
        opened = os.fstat(leaf_fd)
        identity = CgroupLeafIdentityV1(
            relative_path="/" + "/".join((*components, request.leaf_name)),
            device=opened.st_dev,
            inode=opened.st_ino,
        )
        _install_limits(leaf_fd, request.limits)
        leaf = CgroupLeafV1(
            parent_fd=parent_fd,
            leaf_fd=leaf_fd,
            leaf_name=request.leaf_name,
            identity=identity,
            limits=request.limits,
            proc_root=request.proc_root,
            trusted_uid=request.trusted_uid,
        )
        leaf.verify_prelaunch()
        return leaf
    except BaseException as original:
        if leaf_fd >= 0:
            os.close(leaf_fd)
        cleanup_failed = False
        if created:
            try:
                os.rmdir(request.leaf_name, dir_fd=parent_fd)
            except OSError:
                cleanup_failed = True
        os.close(parent_fd)
        if cleanup_failed:
            raise CgroupV2Reject("cgroup_partial_leaf_cleanup_failed") from original
        raise


def _install_limits(leaf_fd: int, limits: CgroupLimitsV1) -> None:
    values = limits.file_values()
    for name in LIMIT_FILE_ORDER:
        cgroup_io.write_control(leaf_fd, name, values[name].encode("ascii") + b"\n")
        if cgroup_io.read_value(leaf_fd, name) != values[name]:
            raise CgroupV2Reject("cgroup_numeric_limit_write_mismatch")


def _verify_parent_controller_contract(parent_fd: int, limits: CgroupLimitsV1) -> None:
    controllers = frozenset(cgroup_io.read_value(parent_fd, "cgroup.controllers").split())
    enabled = frozenset(cgroup_io.read_value(parent_fd, "cgroup.subtree_control").split())
    if not REQUIRED_CONTROLLERS.issubset(controllers):
        raise CgroupV2Reject("cgroup_parent_controllers_missing")
    if not REQUIRED_CONTROLLERS.issubset(enabled):
        raise CgroupV2Reject("cgroup_parent_controllers_not_enabled")
    effective_cpus = parse_cpu_set(
        cgroup_io.read_value(parent_fd, "cpuset.cpus.effective"),
        "cgroup_parent_cpuset_cpus_invalid",
    )
    effective_mems = parse_cpu_set(
        cgroup_io.read_value(parent_fd, "cpuset.mems.effective"),
        "cgroup_parent_cpuset_mems_invalid",
    )
    if not parse_cpu_set(limits.cpuset_cpus, "cgroup_cpuset_cpus_invalid").issubset(effective_cpus):
        raise CgroupV2Reject("cgroup_cpuset_cpus_outside_parent")
    if not parse_cpu_set(limits.cpuset_mems, "cgroup_cpuset_mems_invalid").issubset(effective_mems):
        raise CgroupV2Reject("cgroup_cpuset_mems_outside_parent")


def _remove_and_require_absent(parent_fd: int, leaf_name: str) -> None:
    try:
        os.rmdir(leaf_name, dir_fd=parent_fd)
    except OSError as exc:
        raise CgroupV2Reject("cgroup_leaf_remove_failed") from exc
    try:
        os.stat(leaf_name, dir_fd=parent_fd, follow_symlinks=False)
    except FileNotFoundError:
        return
    except OSError as exc:
        raise CgroupV2Reject("cgroup_leaf_absence_check_failed") from exc
    raise CgroupV2Reject("cgroup_leaf_still_exists")
