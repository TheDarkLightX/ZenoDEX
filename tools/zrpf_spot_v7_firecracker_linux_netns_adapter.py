"""Pinned authority-false adapter for the privileged Linux netns helper."""

from __future__ import annotations

import os
from pathlib import Path
from typing import NoReturn, SupportsIndex, final

from tools.zrpf_firecracker_linux_netns_process import execute_pinned_helper_once
from tools.zrpf_firecracker_linux_netns_protocol import (
    NETNS_HELPER_REQUEST_BYTES_V1 as _NETNS_HELPER_REQUEST_BYTES_V1,
)
from tools.zrpf_firecracker_linux_netns_protocol import (
    NETNS_HELPER_RESPONSE_BYTES_V1 as _NETNS_HELPER_RESPONSE_BYTES_V1,
)
from tools.zrpf_firecracker_linux_netns_protocol import (
    LinuxNetnsAdapterRejectedV1,
    LinuxNetnsAdapterRejectV1,
    NetnsHelperOperationV1,
    ParsedNetnsHelperResponseV1,
)
from tools.zrpf_firecracker_linux_netns_protocol import (
    canonical_name_bytes as _canonical_name_bytes,
)
from tools.zrpf_firecracker_linux_netns_protocol import (
    canonical_root_bytes as _canonical_root_bytes,
)
from tools.zrpf_firecracker_linux_netns_protocol import (
    encode_request_v1 as _encode_request_v1,
)
from tools.zrpf_firecracker_linux_netns_protocol import (
    parse_response_v1 as _parse_response_v1,
)
from tools.zrpf_v3_firecracker_cgroup_v2 import is_canonical_absolute_path_v1
from tools.zrpf_v3_firecracker_netns import PinnedNetworkNamespaceV1

LINUX_NETNS_HELPER_LIVE_EXECUTION_VERIFIED_V1 = False
LINUX_NETNS_HELPER_RUNTIME_AUTHORITY_V1 = False
LINUX_NETNS_HELPER_RELEASE_AUTHORITY_V1 = False
LINUX_NETNS_HELPER_SETTLEMENT_AUTHORITY_V1 = False
LINUX_NETNS_HELPER_PRODUCTION_AUTHORITY_V1 = False
NETNS_HELPER_REQUEST_BYTES_V1 = _NETNS_HELPER_REQUEST_BYTES_V1
NETNS_HELPER_RESPONSE_BYTES_V1 = _NETNS_HELPER_RESPONSE_BYTES_V1


@final
class PinnedLinuxSpotV7NetworkNamespaceKernelV1:
    """Execute the exact sealed helper once for each bounded kernel operation."""

    __slots__ = ("_executable", "_expected_sha256", "_identities")

    def __init__(self, *, executable: Path, expected_sha256: str) -> None:
        if not is_canonical_absolute_path_v1(executable):
            raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.EXECUTABLE_INVALID)
        _require_sha256_hex(expected_sha256)
        self._executable = executable
        self._expected_sha256 = expected_sha256
        self._identities: dict[Path, tuple[int, int]] = {}

    def __copy__(self) -> NoReturn:
        raise TypeError("pinned Linux netns adapter is non-copyable")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("pinned Linux netns adapter is non-copyable")

    def __reduce__(self) -> NoReturn:
        raise TypeError("pinned Linux netns adapter is non-serializable")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("pinned Linux netns adapter is non-serializable")

    def create_fresh_namespace_mount(
        self,
        *,
        namespace_root: Path,
        namespace_name: str,
        trusted_uid: int,
    ) -> None:
        _require_root(trusted_uid)
        path = _namespace_path(namespace_root, namespace_name)
        if path in self._identities:
            raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.BINDING_MISMATCH)
        result = self._execute(
            operation=NetnsHelperOperationV1.CREATE,
            namespace_root=namespace_root,
            namespace_name=namespace_name,
            expected_device=0,
            expected_inode=0,
        )
        if result.device <= 0 or result.inode <= 0:
            raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.RESPONSE_INVALID)
        self._identities[path] = (result.device, result.inode)

    def require_empty_network_inventory(
        self,
        namespace: PinnedNetworkNamespaceV1,
    ) -> None:
        _require_running_as_root()
        path, device, inode = _namespace_identity(namespace)
        self._require_tracked_identity(path, device, inode)
        self._execute(
            operation=NetnsHelperOperationV1.INSPECT,
            namespace_root=path.parent,
            namespace_name=path.name,
            expected_device=device,
            expected_inode=inode,
        )

    def destroy_exact_namespace_mount(
        self,
        namespace: PinnedNetworkNamespaceV1,
    ) -> None:
        _require_running_as_root()
        path, device, inode = _namespace_identity(namespace)
        self._require_tracked_identity(path, device, inode)
        self._execute(
            operation=NetnsHelperOperationV1.DESTROY,
            namespace_root=path.parent,
            namespace_name=path.name,
            expected_device=device,
            expected_inode=inode,
        )
        self._identities[path] = (device, inode)

    def cleanup_unopened_namespace_mount(
        self,
        *,
        namespace_path: Path,
        trusted_uid: int,
    ) -> None:
        _require_root(trusted_uid)
        _namespace_path(namespace_path.parent, namespace_path.name)
        if namespace_path in self._identities:
            raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.BINDING_MISMATCH)
        self._execute(
            operation=NetnsHelperOperationV1.CLEANUP,
            namespace_root=namespace_path.parent,
            namespace_name=namespace_path.name,
            expected_device=0,
            expected_inode=0,
        )
        self._identities.pop(namespace_path, None)

    def require_namespace_mount_absent(
        self,
        *,
        namespace_path: Path,
        trusted_uid: int,
    ) -> None:
        _require_root(trusted_uid)
        _namespace_path(namespace_path.parent, namespace_path.name)
        expected_device, expected_inode = self._identities.get(namespace_path, (0, 0))
        self._execute(
            operation=NetnsHelperOperationV1.ABSENCE,
            namespace_root=namespace_path.parent,
            namespace_name=namespace_path.name,
            expected_device=expected_device,
            expected_inode=expected_inode,
        )
        self._identities.pop(namespace_path, None)

    @property
    def live_execution_verified(self) -> bool:
        return LINUX_NETNS_HELPER_LIVE_EXECUTION_VERIFIED_V1

    @property
    def runtime_authority(self) -> bool:
        return LINUX_NETNS_HELPER_RUNTIME_AUTHORITY_V1

    @property
    def release_authority(self) -> bool:
        return LINUX_NETNS_HELPER_RELEASE_AUTHORITY_V1

    @property
    def settlement_authority(self) -> bool:
        return LINUX_NETNS_HELPER_SETTLEMENT_AUTHORITY_V1

    @property
    def production_authority(self) -> bool:
        return LINUX_NETNS_HELPER_PRODUCTION_AUTHORITY_V1

    def _require_tracked_identity(self, path: Path, device: int, inode: int) -> None:
        if self._identities.get(path) != (device, inode):
            raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.BINDING_MISMATCH)

    def _execute(
        self,
        *,
        operation: NetnsHelperOperationV1,
        namespace_root: Path,
        namespace_name: str,
        expected_device: int,
        expected_inode: int,
    ) -> ParsedNetnsHelperResponseV1:
        _require_running_as_root()
        try:
            request = _encode_request_v1(
                operation=operation,
                namespace_root=namespace_root,
                namespace_name=namespace_name,
                expected_device=expected_device,
                expected_inode=expected_inode,
            )
            response = execute_pinned_helper_once(
                executable=self._executable,
                expected_sha256=self._expected_sha256,
                request=request,
            )
            return _parse_response_v1(
                response,
                request=request,
                expected_operation=operation,
                expected_device=expected_device,
                expected_inode=expected_inode,
            )
        except LinuxNetnsAdapterRejectedV1:
            raise
        except (OSError, TypeError, ValueError) as exc:
            raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.PROCESS_FAILED) from exc


def _namespace_identity(namespace: PinnedNetworkNamespaceV1) -> tuple[Path, int, int]:
    if type(namespace) is not PinnedNetworkNamespaceV1 or namespace.trusted_uid != 0:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.BINDING_MISMATCH)
    device, inode = namespace.pinned_device_and_inode
    return namespace.path, device, inode


def _namespace_path(root: Path, name: str) -> Path:
    _canonical_root_bytes(root)
    _canonical_name_bytes(name)
    return root / name


def _require_root(trusted_uid: int) -> None:
    if type(trusted_uid) is not int or trusted_uid != 0:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.NOT_ROOT)
    _require_running_as_root()


def _require_running_as_root() -> None:
    if os.geteuid() != 0:
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.NOT_ROOT)


def _require_sha256_hex(value: str) -> None:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise LinuxNetnsAdapterRejectedV1(LinuxNetnsAdapterRejectV1.EXECUTABLE_HASH_MISMATCH)


__all__ = [
    "LinuxNetnsAdapterRejectV1",
    "LinuxNetnsAdapterRejectedV1",
    "NetnsHelperOperationV1",
    "PinnedLinuxSpotV7NetworkNamespaceKernelV1",
]
