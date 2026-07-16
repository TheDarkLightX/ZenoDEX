"""Concrete authority-false Linux composition for the Spot V7 supervisor.

The adapter uses the existing descriptor-safe cgroup and prepared-Jailer
implementations. Persistent network-namespace creation and inspection remain a
narrow injected privileged-kernel seam because deterministic unit tests cannot
establish that a live kernel performed those operations.
"""

from __future__ import annotations

import os
from pathlib import Path
from typing import NoReturn, SupportsIndex, final

from tools._zrpf_spot_v7_firecracker_descriptor_handoff import (
    _DescriptorBoundSpotV7LifecycleHandoffV1,
)
from tools.zrpf_spot_v7_firecracker_jailer_lifecycle import (
    CompletedPreparedSpotV7JailerRunV1,
    run_prepared_spot_v7_jailer_process_control_v1,
)
from tools.zrpf_spot_v7_firecracker_linux_namespace import (
    LinuxSpotV7NetworkNamespaceKernelPortV1,
    _LinuxSpotV7NetworkNamespaceControlV1,
)
from tools.zrpf_spot_v7_firecracker_root_supervisor import (
    SpotV7RootSupervisorRejectV1,
)
from tools.zrpf_v3_firecracker_cgroup_contract import CgroupV2Reject
from tools.zrpf_v3_firecracker_cgroup_v2 import (
    CgroupCreateRequestV1,
    CgroupLeafV1,
    create_cgroup_leaf_from_request,
    require_cgroup_leaf_absent_from_request,
    snapshot_cgroup_create_request_v1,
)
from tools.zrpf_v3_firecracker_netns import PinnedNetworkNamespaceV1
from tools.zrpf_v3_firecracker_trusted_runtime import JailerLauncherReject

LINUX_PORT_LIVE_EXECUTION_VERIFIED_V1 = False
LINUX_PORT_LIVE_OWNERSHIP_VERIFIED_V1 = False
LINUX_PORT_RUNTIME_AUTHORITY_V1 = False
LINUX_PORT_SETTLEMENT_AUTHORITY_V1 = False
LINUX_PORT_RELEASE_AUTHORITY_V1 = False
LINUX_PORT_PRODUCTION_AUTHORITY_V1 = False


@final
class LinuxSpotV7RootSupervisorOsPortV1:
    """Single-run Linux adapter for exact cgroup, namespace, and Jailer types."""

    __slots__ = (
        "_cgroup",
        "_cgroup_absent",
        "_cgroup_request",
        "_lifecycle_started",
        "_namespace_control",
        "_prelaunch_verified",
    )

    def __init__(
        self,
        network_namespace_kernel: LinuxSpotV7NetworkNamespaceKernelPortV1,
    ) -> None:
        self._namespace_control = _LinuxSpotV7NetworkNamespaceControlV1(network_namespace_kernel)
        self._cgroup_request: CgroupCreateRequestV1 | None = None
        self._cgroup: CgroupLeafV1 | None = None
        self._prelaunch_verified = False
        self._lifecycle_started = False
        self._cgroup_absent = False

    def __copy__(self) -> NoReturn:
        raise TypeError("Linux Spot V7 OS port is non-copyable")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("Linux Spot V7 OS port is non-copyable")

    def __reduce__(self) -> NoReturn:
        raise TypeError("Linux Spot V7 OS port is non-serializable")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("Linux Spot V7 OS port is non-serializable")

    @property
    def live_execution_verified(self) -> bool:
        return LINUX_PORT_LIVE_EXECUTION_VERIFIED_V1

    @property
    def live_ownership_verified(self) -> bool:
        return LINUX_PORT_LIVE_OWNERSHIP_VERIFIED_V1

    @property
    def runtime_authority(self) -> bool:
        return LINUX_PORT_RUNTIME_AUTHORITY_V1

    @property
    def settlement_authority(self) -> bool:
        return LINUX_PORT_SETTLEMENT_AUTHORITY_V1

    @property
    def release_authority(self) -> bool:
        return LINUX_PORT_RELEASE_AUTHORITY_V1

    @property
    def production_authority(self) -> bool:
        return LINUX_PORT_PRODUCTION_AUTHORITY_V1

    def create_cgroup_leaf(self, request: CgroupCreateRequestV1) -> CgroupLeafV1:
        """Create one exact root-owned leaf and retain its full request."""

        if self._cgroup_request is not None:
            raise SpotV7RootSupervisorRejectV1("linux_port_already_used")
        try:
            request = snapshot_cgroup_create_request_v1(request)
        except CgroupV2Reject as exc:
            raise SpotV7RootSupervisorRejectV1("linux_port_cgroup_request_invalid") from exc
        _require_root_effective_uid()
        if type(request.trusted_uid) is not int or request.trusted_uid != 0:
            raise SpotV7RootSupervisorRejectV1("linux_port_trusted_uid_not_root")
        try:
            leaf = create_cgroup_leaf_from_request(request)
        except (CgroupV2Reject, OSError) as exc:
            raise SpotV7RootSupervisorRejectV1("linux_port_cgroup_create_rejected") from exc
        if type(leaf) is not CgroupLeafV1:
            raise SpotV7RootSupervisorRejectV1("linux_port_cgroup_type_invalid")
        self._cgroup_request = request
        self._cgroup = leaf
        expected_path = _expected_cgroup_relative_path(request)
        if leaf.identity.relative_path != expected_path or leaf.trusted_uid != request.trusted_uid:
            self._cleanup_new_cgroup_after_reject()
            raise SpotV7RootSupervisorRejectV1("linux_port_cgroup_binding_mismatch")
        return leaf

    def create_network_namespace(
        self,
        *,
        namespace_root: Path,
        namespace_name: str,
        trusted_uid: int,
    ) -> PinnedNetworkNamespaceV1:
        """Create, pin, and initially verify one exact empty namespace."""

        _require_root_effective_uid()
        request = self._require_cgroup_request()
        if type(trusted_uid) is not int or trusted_uid != 0 or trusted_uid != request.trusted_uid:
            raise SpotV7RootSupervisorRejectV1("linux_port_trusted_uid_not_root")
        return self._namespace_control.create_and_verify(
            namespace_root=namespace_root,
            namespace_name=namespace_name,
            expected_name=request.leaf_name,
            trusted_uid=trusted_uid,
        )

    def require_prelaunch_controls(
        self,
        *,
        cgroup: object,
        network_namespace: object,
        expected_cgroup_relative_path: str,
        expected_network_namespace_path: Path,
        expected_trusted_uid: int,
    ) -> None:
        """Recheck exact identities, limits, emptiness, addresses, and routes."""

        _require_root_effective_uid()
        leaf = self._require_exact_cgroup(cgroup)
        namespace = self._namespace_control.require_exact(network_namespace)
        request = self._require_cgroup_request()
        if (
            type(expected_trusted_uid) is not int
            or expected_trusted_uid != 0
            or expected_trusted_uid != request.trusted_uid
            or expected_cgroup_relative_path != _expected_cgroup_relative_path(request)
            or leaf.identity.relative_path != expected_cgroup_relative_path
        ):
            raise SpotV7RootSupervisorRejectV1("linux_port_cgroup_binding_mismatch")
        try:
            leaf.verify_prelaunch()
        except (CgroupV2Reject, OSError) as exc:
            raise SpotV7RootSupervisorRejectV1("linux_port_cgroup_prelaunch_rejected") from exc
        self._namespace_control.require_binding(
            namespace,
            expected_path=expected_network_namespace_path,
            expected_trusted_uid=expected_trusted_uid,
        )
        self._namespace_control.require_empty(namespace)
        self._prelaunch_verified = True

    def run_exact_prepared_lifecycle(
        self,
        *,
        handoff: _DescriptorBoundSpotV7LifecycleHandoffV1,
        cgroup: object,
        network_namespace: object,
        process_timeout_ns: int,
        exact_request_bytes: bytes,
    ) -> CompletedPreparedSpotV7JailerRunV1:
        """Execute only the exact retained handoff through the prepared runner."""

        _require_root_effective_uid()
        if not self._prelaunch_verified or self._lifecycle_started:
            raise SpotV7RootSupervisorRejectV1("linux_port_lifecycle_order_invalid")
        if type(handoff) is not _DescriptorBoundSpotV7LifecycleHandoffV1:
            raise SpotV7RootSupervisorRejectV1("linux_port_handoff_type_invalid")
        leaf = self._require_exact_cgroup(cgroup)
        namespace = self._namespace_control.require_exact(network_namespace)
        _require_timeout_ns(process_timeout_ns)
        if type(exact_request_bytes) is not bytes:
            raise SpotV7RootSupervisorRejectV1("linux_port_request_type_invalid")
        try:
            retained_request = handoff._exact_request_bytes_for_supervisor_v1()
        except Exception as exc:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_handoff_reverification_rejected"
            ) from exc
        if retained_request != exact_request_bytes:
            raise SpotV7RootSupervisorRejectV1("linux_port_request_binding_mismatch")
        self._lifecycle_started = True
        try:
            self._namespace_control.require_inventory(namespace)
            completed = run_prepared_spot_v7_jailer_process_control_v1(
                spec=handoff.launch_spec,
                prepared_jail=handoff.prepared_jail,
                jailer=handoff.jailer,
                firecracker=handoff.firecracker,
                cgroup_leaf=leaf,
                network_namespace=namespace,
                process_timeout_seconds=process_timeout_ns / 1_000_000_000,
            )
        except SpotV7RootSupervisorRejectV1:
            raise
        except (CgroupV2Reject, JailerLauncherReject, OSError, RuntimeError) as exc:
            raise SpotV7RootSupervisorRejectV1("linux_port_lifecycle_rejected") from exc
        if type(completed) is not CompletedPreparedSpotV7JailerRunV1:
            raise SpotV7RootSupervisorRejectV1("linux_port_lifecycle_result_invalid")
        return completed

    def terminate_cgroup(self, cgroup: object, *, timeout_ns: int) -> None:
        """Kill/remove the exact leaf or prove the lifecycle already removed it."""

        leaf = self._require_exact_cgroup(cgroup)
        request = self._require_cgroup_request()
        _require_timeout_ns(timeout_ns, maximum=30_000_000_000)
        if not self._cgroup_absent:
            try:
                leaf.terminate_and_remove(timeout_ns=timeout_ns)
            except CgroupV2Reject as exc:
                if exc.code != "cgroup_leaf_closed":
                    raise SpotV7RootSupervisorRejectV1(
                        "linux_port_cgroup_termination_rejected"
                    ) from exc
            except OSError as exc:
                raise SpotV7RootSupervisorRejectV1(
                    "linux_port_cgroup_termination_rejected"
                ) from exc
        self._require_cgroup_absence(request)
        self._cgroup_absent = True

    def require_cgroup_absent(self, cgroup: object) -> None:
        self._require_exact_cgroup(cgroup)
        self._require_cgroup_absence(self._require_cgroup_request())
        self._cgroup_absent = True

    def require_network_namespace_empty(self, network_namespace: object) -> None:
        self._namespace_control.require_empty_before_destroy(network_namespace)

    def destroy_network_namespace(self, network_namespace: object) -> None:
        self._namespace_control.destroy(
            network_namespace,
            cgroup_absent=self._cgroup_absent,
        )

    def require_network_namespace_absent(self, network_namespace: object) -> None:
        self._namespace_control.require_absent(network_namespace)

    def _require_cgroup_request(self) -> CgroupCreateRequestV1:
        if self._cgroup_request is None:
            raise SpotV7RootSupervisorRejectV1("linux_port_cgroup_not_created")
        return self._cgroup_request

    def _require_exact_cgroup(self, value: object) -> CgroupLeafV1:
        if type(value) is not CgroupLeafV1 or value is not self._cgroup:
            raise SpotV7RootSupervisorRejectV1("linux_port_cgroup_object_substituted")
        return value

    def _require_cgroup_absence(self, request: CgroupCreateRequestV1) -> None:
        try:
            require_cgroup_leaf_absent_from_request(request)
        except (CgroupV2Reject, OSError) as exc:
            raise SpotV7RootSupervisorRejectV1("linux_port_cgroup_absence_unverified") from exc

    def _cleanup_new_cgroup_after_reject(self) -> None:
        leaf = self._cgroup
        request = self._cgroup_request
        if leaf is None or request is None:
            return
        try:
            leaf.terminate_and_remove(timeout_ns=5_000_000_000)
            require_cgroup_leaf_absent_from_request(request)
        except Exception as exc:
            raise SpotV7RootSupervisorRejectV1("linux_port_cgroup_partial_cleanup_failed") from exc
        self._cgroup_absent = True


def _expected_cgroup_relative_path(request: CgroupCreateRequestV1) -> str:
    parent = request.parent_relative_path.strip("/")
    return f"/{parent}/{request.leaf_name}"


def _require_root_effective_uid() -> None:
    if os.geteuid() != 0:
        raise SpotV7RootSupervisorRejectV1("linux_port_root_required")


def _require_timeout_ns(
    value: int,
    *,
    maximum: int = 300_000_000_000,
) -> None:
    if type(value) is not int or not 1_000_000 <= value <= maximum:
        raise SpotV7RootSupervisorRejectV1("linux_port_timeout_invalid")
