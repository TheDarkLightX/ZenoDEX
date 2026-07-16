"""Adversarial tests for the authority-false concrete Linux supervisor port."""

from __future__ import annotations

import copy
import pickle
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from tools import zrpf_spot_v7_firecracker_linux_namespace as linux_namespace
from tools import zrpf_spot_v7_firecracker_linux_port as linux_port
from tools import zrpf_v3_firecracker_cgroup_v2 as cgroup_v2
from tools._zrpf_spot_v7_firecracker_descriptor_handoff import (
    _LIFECYCLE_HANDOFF_SEAL_V1,
    _DescriptorBoundSpotV7LifecycleHandoffV1,
)
from tools.zrpf_spot_v7_firecracker_jailer_lifecycle import (
    CompletedPreparedSpotV7JailerRunV1,
)
from tools.zrpf_spot_v7_firecracker_root_supervisor import (
    SpotV7RootSupervisorRejectV1,
)
from tools.zrpf_v3_firecracker_cgroup_contract import CgroupLimitsV1, CgroupV2Reject
from tools.zrpf_v3_firecracker_netns import PinnedNetworkNamespaceV1
from tools.zrpf_v3_firecracker_trusted_runtime import _OpenedIdentityV1


class _FakeNamespaceKernel:
    def __init__(self, *, failure: str | None = None) -> None:
        self.events: list[str] = []
        self.failure = failure

    def create_fresh_namespace_mount(
        self,
        *,
        namespace_root: Path,
        namespace_name: str,
        trusted_uid: int,
    ) -> None:
        self.events.append("create_namespace_mount")
        if self.failure == "create":
            raise OSError("create failed")

    def require_empty_network_inventory(
        self,
        namespace: PinnedNetworkNamespaceV1,
    ) -> None:
        self.events.append("require_empty_inventory")
        if self.failure == "inventory":
            raise OSError("route remains")

    def destroy_exact_namespace_mount(
        self,
        namespace: PinnedNetworkNamespaceV1,
    ) -> None:
        self.events.append("destroy_namespace_mount")
        if self.failure == "destroy":
            raise OSError("destroy failed")

    def cleanup_unopened_namespace_mount(
        self,
        *,
        namespace_path: Path,
        trusted_uid: int,
    ) -> None:
        self.events.append("cleanup_unopened_namespace_mount")
        if self.failure == "cleanup_unopened":
            raise OSError("cleanup failed")

    def require_namespace_mount_absent(
        self,
        *,
        namespace_path: Path,
        trusted_uid: int,
    ) -> None:
        self.events.append("require_namespace_absent")
        if self.failure == "absence":
            raise OSError("path remains")


def _limits() -> CgroupLimitsV1:
    return CgroupLimitsV1(
        cpu_quota_us=100_000,
        cpu_period_us=100_000,
        cpuset_cpus="0",
        cpuset_mems="0",
        io_max="8:0 rbps=1048576 wbps=1048576 riops=1024 wiops=1024",
        memory_high_bytes=256 * 1024 * 1024,
        memory_max_bytes=512 * 1024 * 1024,
        memory_swap_max_bytes=0,
        pids_max=64,
    )


def _request(tmp_path: Path, *, trusted_uid: int = 0) -> cgroup_v2.CgroupCreateRequestV1:
    return cgroup_v2.CgroupCreateRequestV1(
        cgroup_mount=tmp_path / "cgroup2",
        parent_relative_path="zenodex01/zrpf0001",
        leaf_name="run00001",
        limits=_limits(),
        trusted_uid=trusted_uid,
    )


def test_boolean_root_uid_cannot_cross_the_linux_port_boundary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = _request(tmp_path)
    object.__setattr__(request, "trusted_uid", False)
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(_FakeNamespaceKernel())
    monkeypatch.setattr(linux_port.os, "geteuid", lambda: 0)
    monkeypatch.setattr(
        linux_port,
        "create_cgroup_leaf_from_request",
        lambda _request: pytest.fail("invalid UID reached cgroup creation"),
    )

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        port.create_cgroup_leaf(request)

    assert captured.value.code == "linux_port_cgroup_request_invalid"


def _leaf(
    request: cgroup_v2.CgroupCreateRequestV1,
    events: list[str],
    *,
    relative_path: str = "/zenodex01/zrpf0001/run00001",
    prelaunch_reject: str | None = None,
    already_removed: bool = False,
    terminate_reject: str | None = None,
) -> cgroup_v2.CgroupLeafV1:
    value = cgroup_v2.CgroupLeafV1(
        parent_fd=-1,
        leaf_fd=-1,
        leaf_name=request.leaf_name,
        identity=cgroup_v2.CgroupLeafIdentityV1(
            relative_path=relative_path,
            device=71,
            inode=73,
        ),
        limits=request.limits,
        proc_root=request.proc_root,
        trusted_uid=request.trusted_uid,
    )

    def verify_prelaunch() -> None:
        events.append("cgroup_prelaunch")
        if prelaunch_reject is not None:
            raise CgroupV2Reject(prelaunch_reject)

    def terminate_and_remove(*, timeout_ns: int) -> None:
        events.append(f"terminate_cgroup:{timeout_ns}")
        if already_removed:
            raise CgroupV2Reject("cgroup_leaf_closed")
        if terminate_reject is not None:
            raise CgroupV2Reject(terminate_reject)

    value.verify_prelaunch = verify_prelaunch  # type: ignore[method-assign]
    value.terminate_and_remove = terminate_and_remove  # type: ignore[assignment]
    return value


def _namespace(
    tmp_path: Path,
    events: list[str],
    *,
    path: Path | None = None,
    trusted_uid: int = 0,
    empty_reject: bool = False,
) -> PinnedNetworkNamespaceV1:
    value = PinnedNetworkNamespaceV1(
        path=path or tmp_path / "netns" / "run00001",
        identity=_OpenedIdentityV1(
            parent_fd=-1,
            file_fd=-1,
            file_name="run00001",
            device=79,
            inode=83,
        ),
        proc_root=Path("/proc"),
        trusted_uid=trusted_uid,
    )

    def reverify_path() -> None:
        events.append("namespace_reverify")

    def verify_empty() -> None:
        events.append("namespace_processes_empty")
        if empty_reject:
            raise RuntimeError("process remains")

    def close() -> None:
        events.append("namespace_close")

    value.reverify_path = reverify_path
    value.verify_empty = verify_empty
    value.close = close
    return value


def _handoff(exact_request: bytes) -> _DescriptorBoundSpotV7LifecycleHandoffV1:
    value = object.__new__(_DescriptorBoundSpotV7LifecycleHandoffV1)
    object.__setattr__(value, "_closed", False)
    object.__setattr__(value, "_seal", _LIFECYCLE_HANDOFF_SEAL_V1)
    object.__setattr__(
        value,
        "_resources",
        SimpleNamespace(
            prepared_jail=object(),
            jailer=object(),
            firecracker=object(),
            launch_spec=object(),
            exact_request=exact_request,
        ),
    )
    return value


def _patch_handoff_request(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        _DescriptorBoundSpotV7LifecycleHandoffV1,
        "_exact_request_bytes_for_supervisor_v1",
        lambda self: self._resources.exact_request,
    )


def _install_linux_dependencies(
    monkeypatch: pytest.MonkeyPatch,
    *,
    request: cgroup_v2.CgroupCreateRequestV1,
    leaf: cgroup_v2.CgroupLeafV1,
    namespace: PinnedNetworkNamespaceV1,
    events: list[str],
) -> CompletedPreparedSpotV7JailerRunV1:
    completed = CompletedPreparedSpotV7JailerRunV1(
        prepare_observation={"authority": {"production_authority": False}},
        launch_observation={"authority": {"production_authority": False}},
        finish_observation={"authority": {"production_authority": False}},
        output_device_bytes=b"bounded-output",
    )

    def create(
        observed: cgroup_v2.CgroupCreateRequestV1,
    ) -> cgroup_v2.CgroupLeafV1:
        events.append("create_cgroup")
        assert observed == request
        assert observed is not request
        assert observed.limits is not request.limits
        return leaf

    def open_namespace(**kwargs: Any) -> PinnedNetworkNamespaceV1:
        events.append("open_namespace")
        assert kwargs["path"] == request.cgroup_mount.parent / "netns" / "run00001"
        assert kwargs["trusted_root"] == request.cgroup_mount.parent / "netns"
        assert kwargs["trusted_uid"] == 0
        return namespace

    def run_lifecycle(**kwargs: Any) -> CompletedPreparedSpotV7JailerRunV1:
        events.append("run_lifecycle")
        assert kwargs["cgroup_leaf"] is leaf
        assert kwargs["network_namespace"] is namespace
        assert kwargs["process_timeout_seconds"] == 2.0
        return completed

    def require_absent(observed: cgroup_v2.CgroupCreateRequestV1) -> None:
        assert observed == request
        assert observed is not request
        assert observed.limits is not request.limits
        events.append("require_cgroup_absent")

    monkeypatch.setattr(linux_port.os, "geteuid", lambda: 0)
    monkeypatch.setattr(linux_port, "create_cgroup_leaf_from_request", create)
    monkeypatch.setattr(
        linux_namespace,
        "open_pinned_network_namespace",
        open_namespace,
    )
    monkeypatch.setattr(
        linux_port,
        "run_prepared_spot_v7_jailer_process_control_v1",
        run_lifecycle,
    )
    monkeypatch.setattr(
        linux_port,
        "require_cgroup_leaf_absent_from_request",
        require_absent,
    )
    _patch_handoff_request(monkeypatch)
    return completed


def test_exact_linux_composition_is_single_use_and_authority_false(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    events: list[str] = []
    request = _request(tmp_path)
    leaf = _leaf(request, events, already_removed=True)
    namespace = _namespace(tmp_path, events)
    completed = _install_linux_dependencies(
        monkeypatch,
        request=request,
        leaf=leaf,
        namespace=namespace,
        events=events,
    )
    kernel = _FakeNamespaceKernel()
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(kernel)
    handoff = _handoff(b"exact-request")

    assert port.create_cgroup_leaf(request) is leaf
    assert (
        port.create_network_namespace(
            namespace_root=tmp_path / "netns",
            namespace_name="run00001",
            trusted_uid=0,
        )
        is namespace
    )
    port.require_prelaunch_controls(
        cgroup=leaf,
        network_namespace=namespace,
        expected_cgroup_relative_path="/zenodex01/zrpf0001/run00001",
        expected_network_namespace_path=tmp_path / "netns" / "run00001",
        expected_trusted_uid=0,
    )
    assert (
        port.run_exact_prepared_lifecycle(
            handoff=handoff,
            cgroup=leaf,
            network_namespace=namespace,
            process_timeout_ns=2_000_000_000,
            exact_request_bytes=b"exact-request",
        )
        is completed
    )
    port.terminate_cgroup(leaf, timeout_ns=5_000_000_000)
    port.require_cgroup_absent(leaf)
    port.require_network_namespace_empty(namespace)
    port.destroy_network_namespace(namespace)
    port.require_network_namespace_absent(namespace)

    assert port.live_execution_verified is False
    assert port.live_ownership_verified is False
    assert port.runtime_authority is False
    assert port.settlement_authority is False
    assert port.release_authority is False
    assert port.production_authority is False
    assert events == [
        "create_cgroup",
        "open_namespace",
        "namespace_reverify",
        "namespace_processes_empty",
        "cgroup_prelaunch",
        "namespace_reverify",
        "namespace_processes_empty",
        "run_lifecycle",
        "terminate_cgroup:5000000000",
        "require_cgroup_absent",
        "require_cgroup_absent",
        "namespace_reverify",
        "namespace_processes_empty",
        "namespace_close",
    ]
    assert kernel.events == [
        "create_namespace_mount",
        "require_empty_inventory",
        "require_empty_inventory",
        "require_empty_inventory",
        "require_empty_inventory",
        "destroy_namespace_mount",
        "require_namespace_absent",
    ]

    with pytest.raises(SpotV7RootSupervisorRejectV1) as reused:
        port.create_cgroup_leaf(request)
    assert reused.value.code == "linux_port_already_used"


def test_one_shot_port_rejects_copy_deepcopy_and_serialization() -> None:
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(_FakeNamespaceKernel())

    with pytest.raises(TypeError, match="non-copyable"):
        copy.copy(port)
    with pytest.raises(TypeError, match="non-copyable"):
        copy.deepcopy(port)
    with pytest.raises(TypeError, match="non-serializable"):
        pickle.dumps(port)


@pytest.mark.parametrize(
    ("effective_uid", "trusted_uid", "code"),
    (
        (1000, 0, "linux_port_root_required"),
        (0, 1000, "linux_port_trusted_uid_not_root"),
    ),
)
def test_root_ownership_rejects_before_cgroup_creation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    effective_uid: int,
    trusted_uid: int,
    code: str,
) -> None:
    called = False

    def unexpected(_request: cgroup_v2.CgroupCreateRequestV1) -> None:
        nonlocal called
        called = True

    monkeypatch.setattr(linux_port.os, "geteuid", lambda: effective_uid)
    monkeypatch.setattr(linux_port, "create_cgroup_leaf_from_request", unexpected)
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(_FakeNamespaceKernel())

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        port.create_cgroup_leaf(_request(tmp_path, trusted_uid=trusted_uid))

    assert captured.value.code == code
    assert called is False


@pytest.mark.parametrize(
    ("drift", "code"),
    (
        ("cgroup_path", "linux_port_cgroup_binding_mismatch"),
        ("cgroup_limit", "linux_port_cgroup_prelaunch_rejected"),
        ("namespace_path", "linux_port_namespace_binding_mismatch"),
        ("namespace_process", "linux_port_namespace_prelaunch_rejected"),
        ("namespace_inventory", "linux_port_namespace_inventory_rejected"),
    ),
)
def test_prelaunch_distinguishing_witnesses_reject_exact_drift(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    drift: str,
    code: str,
) -> None:
    events: list[str] = []
    request = _request(tmp_path)
    leaf = _leaf(
        request,
        events,
        relative_path=(
            "/zenodex01/zrpf0001/other001"
            if drift == "cgroup_path"
            else "/zenodex01/zrpf0001/run00001"
        ),
        prelaunch_reject=("cgroup_numeric_limit_mismatch" if drift == "cgroup_limit" else None),
    )
    namespace = _namespace(
        tmp_path,
        events,
        path=(tmp_path / "netns" / "other001" if drift == "namespace_path" else None),
        empty_reject=drift == "namespace_process",
    )
    _install_linux_dependencies(
        monkeypatch,
        request=request,
        leaf=leaf,
        namespace=namespace,
        events=events,
    )
    kernel = _FakeNamespaceKernel(failure="inventory" if drift == "namespace_inventory" else None)
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(kernel)
    if drift == "cgroup_path":
        with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
            port.create_cgroup_leaf(request)
        assert captured.value.code == code
        return
    port.create_cgroup_leaf(request)
    if drift.startswith("namespace_"):
        with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
            port.create_network_namespace(
                namespace_root=tmp_path / "netns",
                namespace_name="run00001",
                trusted_uid=0,
            )
        assert captured.value.code == code
        return
    created_namespace = port.create_network_namespace(
        namespace_root=tmp_path / "netns",
        namespace_name="run00001",
        trusted_uid=0,
    )

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        port.require_prelaunch_controls(
            cgroup=leaf,
            network_namespace=created_namespace,
            expected_cgroup_relative_path="/zenodex01/zrpf0001/run00001",
            expected_network_namespace_path=tmp_path / "netns" / "run00001",
            expected_trusted_uid=0,
        )

    assert captured.value.code == code


def test_request_substitution_rejects_before_lifecycle(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    events: list[str] = []
    request = _request(tmp_path)
    leaf = _leaf(request, events)
    namespace = _namespace(tmp_path, events)
    _install_linux_dependencies(
        monkeypatch,
        request=request,
        leaf=leaf,
        namespace=namespace,
        events=events,
    )
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(_FakeNamespaceKernel())
    port.create_cgroup_leaf(request)
    port.create_network_namespace(
        namespace_root=tmp_path / "netns",
        namespace_name="run00001",
        trusted_uid=0,
    )
    port.require_prelaunch_controls(
        cgroup=leaf,
        network_namespace=namespace,
        expected_cgroup_relative_path="/zenodex01/zrpf0001/run00001",
        expected_network_namespace_path=tmp_path / "netns" / "run00001",
        expected_trusted_uid=0,
    )

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        port.run_exact_prepared_lifecycle(
            handoff=_handoff(b"retained-request"),
            cgroup=leaf,
            network_namespace=namespace,
            process_timeout_ns=2_000_000_000,
            exact_request_bytes=b"substituted-request",
        )

    assert captured.value.code == "linux_port_request_binding_mismatch"
    assert "run_lifecycle" not in events


@pytest.mark.parametrize("substitution", ("cgroup", "namespace"))
def test_same_value_control_object_substitution_rejects(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    substitution: str,
) -> None:
    events: list[str] = []
    request = _request(tmp_path)
    leaf = _leaf(request, events)
    namespace = _namespace(tmp_path, events)
    _install_linux_dependencies(
        monkeypatch,
        request=request,
        leaf=leaf,
        namespace=namespace,
        events=events,
    )
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(_FakeNamespaceKernel())
    port.create_cgroup_leaf(request)
    port.create_network_namespace(
        namespace_root=tmp_path / "netns",
        namespace_name="run00001",
        trusted_uid=0,
    )
    supplied_cgroup: object = leaf
    supplied_namespace: object = namespace
    expected_code = "linux_port_cgroup_object_substituted"
    if substitution == "cgroup":
        supplied_cgroup = _leaf(request, [])
    else:
        supplied_namespace = _namespace(tmp_path, [])
        expected_code = "linux_port_namespace_object_substituted"

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        port.require_prelaunch_controls(
            cgroup=supplied_cgroup,
            network_namespace=supplied_namespace,
            expected_cgroup_relative_path="/zenodex01/zrpf0001/run00001",
            expected_network_namespace_path=tmp_path / "netns" / "run00001",
            expected_trusted_uid=0,
        )

    assert captured.value.code == expected_code


@pytest.mark.parametrize("timeout", (True, 999_999, 300_000_000_001))
def test_process_timeout_representation_and_bounds_reject_before_lifecycle(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    timeout: int,
) -> None:
    events: list[str] = []
    request = _request(tmp_path)
    leaf = _leaf(request, events)
    namespace = _namespace(tmp_path, events)
    _install_linux_dependencies(
        monkeypatch,
        request=request,
        leaf=leaf,
        namespace=namespace,
        events=events,
    )
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(_FakeNamespaceKernel())
    port.create_cgroup_leaf(request)
    port.create_network_namespace(
        namespace_root=tmp_path / "netns",
        namespace_name="run00001",
        trusted_uid=0,
    )
    port.require_prelaunch_controls(
        cgroup=leaf,
        network_namespace=namespace,
        expected_cgroup_relative_path="/zenodex01/zrpf0001/run00001",
        expected_network_namespace_path=tmp_path / "netns" / "run00001",
        expected_trusted_uid=0,
    )

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        port.run_exact_prepared_lifecycle(
            handoff=_handoff(b"position-distinct-request"),
            cgroup=leaf,
            network_namespace=namespace,
            process_timeout_ns=timeout,
            exact_request_bytes=b"position-distinct-request",
        )

    assert captured.value.code == "linux_port_timeout_invalid"
    assert "run_lifecycle" not in events


def test_lifecycle_rejection_is_typed_and_cannot_be_retried(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    events: list[str] = []
    request = _request(tmp_path)
    leaf = _leaf(request, events)
    namespace = _namespace(tmp_path, events)
    _install_linux_dependencies(
        monkeypatch,
        request=request,
        leaf=leaf,
        namespace=namespace,
        events=events,
    )
    monkeypatch.setattr(
        linux_port,
        "run_prepared_spot_v7_jailer_process_control_v1",
        lambda **_kwargs: (_ for _ in ()).throw(RuntimeError("lifecycle failed")),
    )
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(_FakeNamespaceKernel())
    port.create_cgroup_leaf(request)
    port.create_network_namespace(
        namespace_root=tmp_path / "netns",
        namespace_name="run00001",
        trusted_uid=0,
    )
    port.require_prelaunch_controls(
        cgroup=leaf,
        network_namespace=namespace,
        expected_cgroup_relative_path="/zenodex01/zrpf0001/run00001",
        expected_network_namespace_path=tmp_path / "netns" / "run00001",
        expected_trusted_uid=0,
    )

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        port.run_exact_prepared_lifecycle(
            handoff=_handoff(b"position-distinct-request"),
            cgroup=leaf,
            network_namespace=namespace,
            process_timeout_ns=2_000_000_000,
            exact_request_bytes=b"position-distinct-request",
        )

    assert captured.value.code == "linux_port_lifecycle_rejected"
    with pytest.raises(SpotV7RootSupervisorRejectV1) as retried:
        port.run_exact_prepared_lifecycle(
            handoff=_handoff(b"position-distinct-request"),
            cgroup=leaf,
            network_namespace=namespace,
            process_timeout_ns=2_000_000_000,
            exact_request_bytes=b"position-distinct-request",
        )
    assert retried.value.code == "linux_port_lifecycle_order_invalid"


def test_cgroup_termination_failure_is_typed_and_blocks_namespace_destroy(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    events: list[str] = []
    request = _request(tmp_path)
    leaf = _leaf(request, events, terminate_reject="cgroup_kill_failed")
    namespace = _namespace(tmp_path, events)
    _install_linux_dependencies(
        monkeypatch,
        request=request,
        leaf=leaf,
        namespace=namespace,
        events=events,
    )
    kernel = _FakeNamespaceKernel()
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(kernel)
    port.create_cgroup_leaf(request)
    port.create_network_namespace(
        namespace_root=tmp_path / "netns",
        namespace_name="run00001",
        trusted_uid=0,
    )

    with pytest.raises(SpotV7RootSupervisorRejectV1) as termination:
        port.terminate_cgroup(leaf, timeout_ns=5_000_000_000)
    assert termination.value.code == "linux_port_cgroup_termination_rejected"

    with pytest.raises(SpotV7RootSupervisorRejectV1) as destroy:
        port.destroy_network_namespace(namespace)
    assert destroy.value.code == "linux_port_namespace_destroy_before_cgroup_absence"
    assert "destroy_namespace_mount" not in kernel.events


@pytest.mark.parametrize(
    ("failure", "operation", "code"),
    (
        ("destroy", "destroy", "linux_port_namespace_destroy_rejected"),
        ("absence", "absence", "linux_port_namespace_absence_unverified"),
    ),
)
def test_namespace_teardown_failures_are_typed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    failure: str,
    operation: str,
    code: str,
) -> None:
    events: list[str] = []
    request = _request(tmp_path)
    leaf = _leaf(request, events)
    namespace = _namespace(tmp_path, events)
    _install_linux_dependencies(
        monkeypatch,
        request=request,
        leaf=leaf,
        namespace=namespace,
        events=events,
    )
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(_FakeNamespaceKernel(failure=failure))
    port.create_cgroup_leaf(request)
    port.create_network_namespace(
        namespace_root=tmp_path / "netns",
        namespace_name="run00001",
        trusted_uid=0,
    )

    port.terminate_cgroup(leaf, timeout_ns=5_000_000_000)
    port.require_cgroup_absent(leaf)
    if operation == "absence":
        port.destroy_network_namespace(namespace)

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        if operation == "destroy":
            port.destroy_network_namespace(namespace)
        else:
            port.require_network_namespace_absent(namespace)

    assert captured.value.code == code


def test_namespace_open_failure_requires_cleanup_and_absence(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    kernel = _FakeNamespaceKernel()
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(kernel)
    request = _request(tmp_path)
    monkeypatch.setattr(linux_port.os, "geteuid", lambda: 0)
    monkeypatch.setattr(
        linux_port,
        "create_cgroup_leaf_from_request",
        lambda observed: _leaf(observed, []),
    )
    monkeypatch.setattr(
        linux_namespace,
        "open_pinned_network_namespace",
        lambda **_kwargs: (_ for _ in ()).throw(OSError("open failed")),
    )
    port.create_cgroup_leaf(request)

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        port.create_network_namespace(
            namespace_root=tmp_path / "netns",
            namespace_name="run00001",
            trusted_uid=0,
        )

    assert captured.value.code == "linux_port_namespace_open_rejected"
    assert kernel.events == [
        "create_namespace_mount",
        "cleanup_unopened_namespace_mount",
        "require_namespace_absent",
    ]


def test_namespace_create_failure_requires_cleanup_and_absence(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    events: list[str] = []
    request = _request(tmp_path)
    leaf = _leaf(request, events)
    namespace = _namespace(tmp_path, events)
    _install_linux_dependencies(
        monkeypatch,
        request=request,
        leaf=leaf,
        namespace=namespace,
        events=events,
    )
    kernel = _FakeNamespaceKernel(failure="create")
    port = linux_port.LinuxSpotV7RootSupervisorOsPortV1(kernel)
    port.create_cgroup_leaf(request)

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        port.create_network_namespace(
            namespace_root=tmp_path / "netns",
            namespace_name="run00001",
            trusted_uid=0,
        )

    assert captured.value.code == "linux_port_namespace_create_rejected"
    assert kernel.events == [
        "create_namespace_mount",
        "cleanup_unopened_namespace_mount",
        "require_namespace_absent",
    ]
