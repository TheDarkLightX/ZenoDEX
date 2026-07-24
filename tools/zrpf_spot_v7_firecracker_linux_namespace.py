"""Authority-false network-namespace ownership for the Spot V7 Linux port."""

from __future__ import annotations

from pathlib import Path
from typing import NoReturn, Protocol, SupportsIndex, final

from tools.zrpf_spot_v7_firecracker_root_supervisor import (
    SpotV7RootSupervisorRejectV1,
)
from tools.zrpf_v3_firecracker_netns import (
    PinnedNetworkNamespaceV1,
    open_pinned_network_namespace,
)
from tools.zrpf_v3_firecracker_trusted_runtime import JailerLauncherReject


class LinuxSpotV7NetworkNamespaceKernelPortV1(Protocol):
    """Small privileged seam for persistent namespace mount operations."""

    def create_fresh_namespace_mount(
        self,
        *,
        namespace_root: Path,
        namespace_name: str,
        trusted_uid: int,
    ) -> None: ...

    def require_empty_network_inventory(
        self,
        namespace: PinnedNetworkNamespaceV1,
    ) -> None: ...

    def destroy_exact_namespace_mount(
        self,
        namespace: PinnedNetworkNamespaceV1,
    ) -> None: ...

    def cleanup_unopened_namespace_mount(
        self,
        *,
        namespace_path: Path,
        trusted_uid: int,
    ) -> None: ...

    def require_namespace_mount_absent(
        self,
        *,
        namespace_path: Path,
        trusted_uid: int,
    ) -> None: ...


@final
class _LinuxSpotV7NetworkNamespaceControlV1:
    """Single-allocation namespace state owned by one outer Linux port."""

    __slots__ = ("_destroyed", "_kernel", "_namespace", "_path")

    def __init__(
        self,
        kernel: LinuxSpotV7NetworkNamespaceKernelPortV1,
    ) -> None:
        self._kernel = kernel
        self._namespace: PinnedNetworkNamespaceV1 | None = None
        self._path: Path | None = None
        self._destroyed = False

    def __copy__(self) -> NoReturn:
        raise TypeError("Linux Spot V7 namespace control is non-copyable")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("Linux Spot V7 namespace control is non-copyable")

    def __reduce__(self) -> NoReturn:
        raise TypeError("Linux Spot V7 namespace control is non-serializable")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("Linux Spot V7 namespace control is non-serializable")

    def create_and_verify(
        self,
        *,
        namespace_root: Path,
        namespace_name: str,
        expected_name: str,
        trusted_uid: int,
    ) -> PinnedNetworkNamespaceV1:
        self._validate_creation_request(
            namespace_root=namespace_root,
            namespace_name=namespace_name,
            expected_name=expected_name,
            trusted_uid=trusted_uid,
        )
        path = namespace_root / namespace_name
        self._path = path
        self._create_mount(namespace_root, namespace_name, trusted_uid)
        namespace = self._open_created(path, namespace_root, trusted_uid)
        self._namespace = namespace
        try:
            self.require_binding(
                namespace,
                expected_path=path,
                expected_trusted_uid=trusted_uid,
            )
            self.require_empty(namespace)
        except SpotV7RootSupervisorRejectV1:
            self._cleanup_opened(namespace)
            raise
        return namespace

    def require_exact(self, value: object) -> PinnedNetworkNamespaceV1:
        if type(value) is not PinnedNetworkNamespaceV1 or value is not self._namespace:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_object_substituted"
            )
        return value

    def require_binding(
        self,
        namespace: PinnedNetworkNamespaceV1,
        *,
        expected_path: Path,
        expected_trusted_uid: int,
    ) -> None:
        if (
            namespace.path != expected_path
            or self._path != expected_path
            or namespace.trusted_uid != expected_trusted_uid
            or expected_trusted_uid != 0
        ):
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_binding_mismatch"
            )
        try:
            namespace.reverify_path()
        except (JailerLauncherReject, OSError, RuntimeError) as exc:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_binding_mismatch"
            ) from exc

    def require_empty(self, namespace: PinnedNetworkNamespaceV1) -> None:
        try:
            namespace.verify_empty()
        except (JailerLauncherReject, OSError, RuntimeError) as exc:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_prelaunch_rejected"
            ) from exc
        self.require_inventory(namespace)

    def require_inventory(self, namespace: PinnedNetworkNamespaceV1) -> None:
        try:
            self._kernel.require_empty_network_inventory(namespace)
        except Exception as exc:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_inventory_rejected"
            ) from exc

    def require_empty_before_destroy(
        self,
        value: object,
    ) -> None:
        namespace = self.require_exact(value)
        try:
            namespace.reverify_path()
            namespace.verify_empty()
        except (JailerLauncherReject, OSError, RuntimeError) as exc:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_not_empty"
            ) from exc
        self.require_inventory(namespace)

    def destroy(self, value: object, *, cgroup_absent: bool) -> None:
        namespace = self.require_exact(value)
        if not cgroup_absent:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_destroy_before_cgroup_absence"
            )
        if self._destroyed:
            return
        try:
            self._kernel.destroy_exact_namespace_mount(namespace)
        except Exception as exc:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_destroy_rejected"
            ) from exc
        namespace.close()
        self._destroyed = True

    def require_absent(self, value: object) -> None:
        self.require_exact(value)
        if not self._destroyed:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_absence_before_destroy"
            )
        path = self._require_path()
        try:
            self._kernel.require_namespace_mount_absent(
                namespace_path=path,
                trusted_uid=0,
            )
        except Exception as exc:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_absence_unverified"
            ) from exc

    def _validate_creation_request(
        self,
        *,
        namespace_root: Path,
        namespace_name: str,
        expected_name: str,
        trusted_uid: int,
    ) -> None:
        if self._namespace is not None or self._path is not None:
            raise SpotV7RootSupervisorRejectV1("linux_port_namespace_already_created")
        if trusted_uid != 0:
            raise SpotV7RootSupervisorRejectV1("linux_port_trusted_uid_not_root")
        if (
            not isinstance(namespace_root, Path)
            or not namespace_root.is_absolute()
            or type(namespace_name) is not str
            or namespace_name != expected_name
        ):
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_request_invalid"
            )

    def _create_mount(
        self,
        namespace_root: Path,
        namespace_name: str,
        trusted_uid: int,
    ) -> None:
        try:
            self._kernel.create_fresh_namespace_mount(
                namespace_root=namespace_root,
                namespace_name=namespace_name,
                trusted_uid=trusted_uid,
            )
        except Exception as exc:
            self._cleanup_unopened()
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_create_rejected"
            ) from exc

    def _open_created(
        self,
        path: Path,
        namespace_root: Path,
        trusted_uid: int,
    ) -> PinnedNetworkNamespaceV1:
        try:
            namespace = open_pinned_network_namespace(
                path=path,
                trusted_root=namespace_root,
                trusted_uid=trusted_uid,
            )
        except Exception as exc:
            self._cleanup_unopened()
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_open_rejected"
            ) from exc
        if type(namespace) is not PinnedNetworkNamespaceV1:
            self._cleanup_unopened()
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_type_invalid"
            )
        return namespace

    def _cleanup_opened(self, namespace: PinnedNetworkNamespaceV1) -> None:
        try:
            self._kernel.destroy_exact_namespace_mount(namespace)
            namespace.close()
            self._kernel.require_namespace_mount_absent(
                namespace_path=self._require_path(),
                trusted_uid=0,
            )
        except Exception as exc:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_partial_cleanup_failed"
            ) from exc
        self._destroyed = True

    def _cleanup_unopened(self) -> None:
        path = self._require_path()
        try:
            self._kernel.cleanup_unopened_namespace_mount(
                namespace_path=path,
                trusted_uid=0,
            )
            self._kernel.require_namespace_mount_absent(
                namespace_path=path,
                trusted_uid=0,
            )
        except Exception as cleanup_error:
            raise SpotV7RootSupervisorRejectV1(
                "linux_port_namespace_partial_cleanup_failed"
            ) from cleanup_error

    def _require_path(self) -> Path:
        if self._path is None:
            raise SpotV7RootSupervisorRejectV1("linux_port_namespace_not_created")
        return self._path
