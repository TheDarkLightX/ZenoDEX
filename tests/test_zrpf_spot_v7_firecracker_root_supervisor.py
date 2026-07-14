"""Adversarial contract tests for the authority-false root supervisor."""

from __future__ import annotations

import copy
import hashlib
import pickle
from pathlib import Path

import pytest

from tests.test_zrpf_spot_v7_firecracker_descriptor_staging import (
    _Fixture as DescriptorFixture,
)
from tests.test_zrpf_spot_v7_firecracker_descriptor_staging import (
    _fixture as descriptor_fixture,
)
from tests.test_zrpf_spot_v7_firecracker_runtime_protocol import _valid_v7_payload
from tools import zrpf_spot_v7_firecracker_root_supervisor as supervisor
from tools._zrpf_spot_v7_firecracker_descriptor_handoff import (
    _DescriptorBoundSpotV7LifecycleHandoffV1,
    _PreparedDescriptorBoundSpotV7LaunchV1,
)
from tools.zrpf_spot_v7_firecracker_jailer_lifecycle import (
    CompletedPreparedSpotV7JailerRunV1,
)
from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SpotV7FirecrackerRequestV1,
    build_data_only_committed_output_v1,
)
from tools.zrpf_v3_firecracker_cgroup_v2 import (
    CgroupCreateRequestV1,
    CgroupLimitsV1,
)


class _FakeRootSupervisorPort:
    """Deterministic OS-port double; its claims never create authority."""

    def __init__(
        self,
        *,
        failure: str | None = None,
        output_mode: str = "valid",
        teardown_failure: str | None = None,
    ) -> None:
        self.events: list[str] = []
        self.failure = failure
        self.output_mode = output_mode
        self.teardown_failure = teardown_failure
        self.cgroup_token = object()
        self.namespace_token = object()

    def create_cgroup_leaf(self, request: CgroupCreateRequestV1) -> object:
        self.events.append("create_cgroup")
        if self.failure == "cgroup_absent":
            raise supervisor.SpotV7RootSupervisorRejectV1(
                "root_supervisor_cgroup_absent"
            )
        return self.cgroup_token

    def create_network_namespace(
        self,
        *,
        namespace_root: Path,
        namespace_name: str,
        trusted_uid: int,
    ) -> object:
        self.events.append("create_namespace")
        return self.namespace_token

    def require_prelaunch_controls(
        self,
        *,
        cgroup: object,
        network_namespace: object,
        expected_cgroup_relative_path: str,
        expected_network_namespace_path: Path,
        expected_trusted_uid: int,
    ) -> None:
        self.events.append("require_prelaunch")
        codes = {
            "cgroup_moved": "root_supervisor_cgroup_identity_changed",
            "limit_altered": "root_supervisor_cgroup_limit_changed",
            "namespace_mismatch": "root_supervisor_namespace_identity_changed",
            "namespace_route": "root_supervisor_namespace_route_present",
        }
        if self.failure in codes:
            raise supervisor.SpotV7RootSupervisorRejectV1(codes[self.failure])

    def run_exact_prepared_lifecycle(
        self,
        *,
        handoff: _DescriptorBoundSpotV7LifecycleHandoffV1,
        cgroup: object,
        network_namespace: object,
        process_timeout_ns: int,
        exact_request_bytes: bytes,
    ) -> CompletedPreparedSpotV7JailerRunV1:
        self.events.append("run_lifecycle")
        if self.failure == "timeout":
            raise supervisor.SpotV7RootSupervisorRejectV1(
                "root_supervisor_lifecycle_timeout"
            )
        if self.failure == "process_remains":
            raise supervisor.SpotV7RootSupervisorRejectV1(
                "root_supervisor_processes_remain"
            )
        request = supervisor.decode_exact_request_v1(exact_request_bytes)
        output = self._output(request)
        prepared_jail = handoff.prepared_jail
        prepared_jail.cleanup_after_teardown()
        prepare_observation: dict[str, object] = {
            "authority": {"production_authority": False}
        }
        if self.output_mode == "invalid_observation":
            prepare_observation = {"unencodable": object()}
        return CompletedPreparedSpotV7JailerRunV1(
            prepare_observation=prepare_observation,
            launch_observation={"authority": {"production_authority": False}},
            finish_observation={"authority": {"production_authority": False}},
            output_device_bytes=output,
        )

    def terminate_cgroup(self, cgroup: object, *, timeout_ns: int) -> None:
        self.events.append("terminate_cgroup")
        if self.teardown_failure == "cgroup":
            raise supervisor.SpotV7RootSupervisorRejectV1(
                "root_supervisor_cgroup_teardown_failed"
            )

    def require_cgroup_absent(self, cgroup: object) -> None:
        self.events.append("require_cgroup_absent")
        if self.teardown_failure == "cgroup_absence":
            raise supervisor.SpotV7RootSupervisorRejectV1(
                "root_supervisor_cgroup_absence_unverified"
            )

    def require_network_namespace_empty(self, network_namespace: object) -> None:
        self.events.append("require_namespace_empty")

    def destroy_network_namespace(self, network_namespace: object) -> None:
        self.events.append("destroy_namespace")
        if self.teardown_failure == "namespace":
            raise supervisor.SpotV7RootSupervisorRejectV1(
                "root_supervisor_namespace_teardown_failed"
            )

    def require_network_namespace_absent(self, network_namespace: object) -> None:
        self.events.append("require_namespace_absent")
        if self.teardown_failure in ("namespace", "namespace_absence"):
            raise supervisor.SpotV7RootSupervisorRejectV1(
                "root_supervisor_namespace_absence_unverified"
            )

    def _output(self, request: SpotV7FirecrackerRequestV1) -> bytes:
        selected = request
        if self.output_mode == "stale_nonce":
            selected = SpotV7FirecrackerRequestV1.validated(
                run_nonce_256=hashlib.sha256(b"stale-nonce").digest(),
                runtime_manifest_sha256=request.runtime_manifest_sha256,
                machine_config_sha256=request.machine_config_sha256,
                input_drive_sha256=request.input_drive_sha256,
                settlement_intent_sha256=request.settlement_intent_sha256,
            )
        output = bytearray(
            build_data_only_committed_output_v1(
                selected,
                observed_input_drive_sha256=selected.input_drive_sha256,
                payload=_valid_v7_payload(),
            )
        )
        if self.output_mode == "forged_commit":
            output[-1] ^= 1
        return bytes(output)


def _plan(tmp_path: Path, *, trusted_uid: int) -> supervisor.SpotV7RootSupervisorPlanV1:
    return supervisor.SpotV7RootSupervisorPlanV1(
        cgroup_request=CgroupCreateRequestV1(
            cgroup_mount=tmp_path / "cgroup2",
            parent_relative_path="zenodex01/zrpf0001",
            leaf_name="run00001",
            limits=CgroupLimitsV1(
                cpu_quota_us=100_000,
                cpu_period_us=100_000,
                cpuset_cpus="0",
                cpuset_mems="0",
                io_max="8:0 rbps=1048576 wbps=1048576 riops=1024 wiops=1024",
                memory_high_bytes=256 * 1024 * 1024,
                memory_max_bytes=512 * 1024 * 1024,
                memory_swap_max_bytes=0,
                pids_max=64,
            ),
            trusted_uid=trusted_uid,
        ),
        network_namespace_root=tmp_path / "netns",
        network_namespace_name="run00001",
        process_timeout_ns=30_000_000_000,
        teardown_timeout_ns=5_000_000_000,
    )


def _prepared(
    tmp_path: Path,
) -> tuple[DescriptorFixture, _PreparedDescriptorBoundSpotV7LaunchV1]:
    fixture = descriptor_fixture(tmp_path)
    return fixture, fixture.prepare(fixture.open_bound())


def test_success_consumes_handoff_validates_output_and_destroys_controls(
    tmp_path: Path,
) -> None:
    fixture, prepared = _prepared(tmp_path)
    port = _FakeRootSupervisorPort()

    result = supervisor.run_spot_v7_root_supervisor_contract_v1(
        prepared_launch=prepared,
        plan=_plan(tmp_path, trusted_uid=fixture.trusted_uid),
        os_port=port,
    )

    assert result.payload_bytes == _valid_v7_payload()
    assert result.payload_sha256 == hashlib.sha256(result.payload_bytes).digest()
    assert result.cgroup_relative_path == "/zenodex01/zrpf0001/run00001"
    assert result.network_namespace_path == tmp_path / "netns" / "run00001"
    assert result.live_execution_verified is False
    assert result.live_ownership_verified is False
    assert result.governed_cgroup_parent_verified is False
    assert result.governed_cgroup_resource_policy_verified is False
    assert result.governed_network_namespace_root_verified is False
    assert result.runtime_authority is False
    assert result.settlement_authority is False
    assert result.release_authority is False
    assert result.production_authority is False
    assert port.events == [
        "create_cgroup",
        "create_namespace",
        "require_prelaunch",
        "run_lifecycle",
        "terminate_cgroup",
        "require_cgroup_absent",
        "require_namespace_empty",
        "destroy_namespace",
        "require_namespace_absent",
    ]
    assert not prepared.snapshot_root_path.exists()

    with pytest.raises(supervisor.SpotV7RootSupervisorRejectV1) as reused:
        supervisor.run_spot_v7_root_supervisor_contract_v1(
            prepared_launch=prepared,
            plan=_plan(tmp_path, trusted_uid=fixture.trusted_uid),
            os_port=_FakeRootSupervisorPort(),
        )
    assert reused.value.code == "root_supervisor_handoff_rejected"


@pytest.mark.parametrize(
    ("failure", "code"),
    (
        ("cgroup_absent", "root_supervisor_cgroup_absent"),
        ("cgroup_moved", "root_supervisor_cgroup_identity_changed"),
        ("limit_altered", "root_supervisor_cgroup_limit_changed"),
        ("namespace_mismatch", "root_supervisor_namespace_identity_changed"),
        ("namespace_route", "root_supervisor_namespace_route_present"),
    ),
)
def test_prelaunch_control_failures_reject_and_remove_unlaunched_stage(
    tmp_path: Path,
    failure: str,
    code: str,
) -> None:
    fixture, prepared = _prepared(tmp_path)
    port = _FakeRootSupervisorPort(failure=failure)

    with pytest.raises(supervisor.SpotV7RootSupervisorRejectV1) as captured:
        supervisor.run_spot_v7_root_supervisor_contract_v1(
            prepared_launch=prepared,
            plan=_plan(tmp_path, trusted_uid=fixture.trusted_uid),
            os_port=port,
        )

    assert captured.value.code == code
    assert not prepared.snapshot_root_path.exists()
    assert "run_lifecycle" not in port.events


@pytest.mark.parametrize(
    "failure",
    ("timeout", "process_remains"),
)
def test_started_failure_kills_cgroup_and_waits_for_empty_teardown(
    tmp_path: Path,
    failure: str,
) -> None:
    fixture, prepared = _prepared(tmp_path)
    port = _FakeRootSupervisorPort(failure=failure)

    with pytest.raises(supervisor.SpotV7RootSupervisorRejectV1) as captured:
        supervisor.run_spot_v7_root_supervisor_contract_v1(
            prepared_launch=prepared,
            plan=_plan(tmp_path, trusted_uid=fixture.trusted_uid),
            os_port=port,
        )

    expected = (
        "root_supervisor_lifecycle_timeout"
        if failure == "timeout"
        else "root_supervisor_processes_remain"
    )
    assert captured.value.code == expected
    assert port.events[-5:] == [
        "terminate_cgroup",
        "require_cgroup_absent",
        "require_namespace_empty",
        "destroy_namespace",
        "require_namespace_absent",
    ]
    assert not prepared.snapshot_root_path.exists()


@pytest.mark.parametrize("output_mode", ("stale_nonce", "forged_commit"))
def test_independent_output_authentication_rejects_stale_or_forged_output(
    tmp_path: Path,
    output_mode: str,
) -> None:
    fixture, prepared = _prepared(tmp_path)
    port = _FakeRootSupervisorPort(output_mode=output_mode)

    with pytest.raises(supervisor.SpotV7RootSupervisorRejectV1) as captured:
        supervisor.run_spot_v7_root_supervisor_contract_v1(
            prepared_launch=prepared,
            plan=_plan(tmp_path, trusted_uid=fixture.trusted_uid),
            os_port=port,
        )

    assert captured.value.code == "root_supervisor_output_rejected"
    assert port.events[-5:] == [
        "terminate_cgroup",
        "require_cgroup_absent",
        "require_namespace_empty",
        "destroy_namespace",
        "require_namespace_absent",
    ]
    assert not prepared.snapshot_root_path.exists()


def test_result_construction_failure_does_not_repeat_verified_teardown(
    tmp_path: Path,
) -> None:
    fixture, prepared = _prepared(tmp_path)
    port = _FakeRootSupervisorPort(output_mode="invalid_observation")

    with pytest.raises(supervisor.SpotV7RootSupervisorRejectV1) as captured:
        supervisor.run_spot_v7_root_supervisor_contract_v1(
            prepared_launch=prepared,
            plan=_plan(tmp_path, trusted_uid=fixture.trusted_uid),
            os_port=port,
        )

    assert captured.value.code == "root_supervisor_observation_invalid"
    assert port.events.count("terminate_cgroup") == 1
    assert port.events.count("require_cgroup_absent") == 1
    assert port.events.count("destroy_namespace") == 1
    assert port.events.count("require_namespace_absent") == 1
    assert not prepared.snapshot_root_path.exists()


def test_descriptor_path_substitution_rejects_before_control_allocation(
    tmp_path: Path,
) -> None:
    fixture, prepared = _prepared(tmp_path)
    kernel = prepared.snapshot_artifact_path("kernel")
    raw = kernel.read_bytes()
    kernel.chmod(0o600)
    kernel.write_bytes(raw + b"substitution")
    kernel.chmod(0o444)
    port = _FakeRootSupervisorPort()

    with pytest.raises(supervisor.SpotV7RootSupervisorRejectV1) as captured:
        supervisor.run_spot_v7_root_supervisor_contract_v1(
            prepared_launch=prepared,
            plan=_plan(tmp_path, trusted_uid=fixture.trusted_uid),
            os_port=port,
        )

    assert captured.value.code == "root_supervisor_handoff_rejected"
    assert port.events == []
    assert not prepared.snapshot_root_path.exists()


def test_plan_rejects_control_name_drift_and_boolean_timeout(tmp_path: Path) -> None:
    valid = _plan(tmp_path, trusted_uid=0)

    with pytest.raises(supervisor.SpotV7RootSupervisorRejectV1) as drift:
        supervisor.SpotV7RootSupervisorPlanV1(
            cgroup_request=valid.cgroup_request,
            network_namespace_root=valid.network_namespace_root,
            network_namespace_name="other001",
            process_timeout_ns=valid.process_timeout_ns,
            teardown_timeout_ns=valid.teardown_timeout_ns,
        )
    assert drift.value.code == "root_supervisor_control_name_mismatch"

    with pytest.raises(supervisor.SpotV7RootSupervisorRejectV1) as boolean:
        supervisor.SpotV7RootSupervisorPlanV1(
            cgroup_request=valid.cgroup_request,
            network_namespace_root=valid.network_namespace_root,
            network_namespace_name=valid.network_namespace_name,
            process_timeout_ns=True,
            teardown_timeout_ns=valid.teardown_timeout_ns,
        )
    assert boolean.value.code == "root_supervisor_process_timeout_invalid"


@pytest.mark.parametrize(
    "teardown_failure",
    ("cgroup", "cgroup_absence", "namespace", "namespace_absence"),
)
def test_teardown_uncertainty_overrides_lifecycle_failure_and_quarantines(
    tmp_path: Path,
    teardown_failure: str,
) -> None:
    fixture, prepared = _prepared(tmp_path)
    port = _FakeRootSupervisorPort(
        failure="timeout",
        teardown_failure=teardown_failure,
    )

    with pytest.raises(supervisor.SpotV7RootSupervisorRejectV1) as captured:
        supervisor.run_spot_v7_root_supervisor_contract_v1(
            prepared_launch=prepared,
            plan=_plan(tmp_path, trusted_uid=fixture.trusted_uid),
            os_port=port,
        )

    assert captured.value.code == "root_supervisor_teardown_uncertain"
    assert prepared.snapshot_root_path.exists()
    with pytest.raises(supervisor.SpotV7RootSupervisorRejectV1) as reused:
        supervisor.run_spot_v7_root_supervisor_contract_v1(
            prepared_launch=prepared,
            plan=_plan(tmp_path, trusted_uid=fixture.trusted_uid),
            os_port=_FakeRootSupervisorPort(),
        )
    assert reused.value.code == "root_supervisor_handoff_rejected"


def test_result_is_sealed_noncopyable_and_nonserializable(tmp_path: Path) -> None:
    fixture, prepared = _prepared(tmp_path)
    result = supervisor.run_spot_v7_root_supervisor_contract_v1(
        prepared_launch=prepared,
        plan=_plan(tmp_path, trusted_uid=fixture.trusted_uid),
        os_port=_FakeRootSupervisorPort(),
    )

    for operation in (
        lambda: copy.copy(result),
        lambda: copy.deepcopy(result),
        lambda: pickle.dumps(result),
    ):
        with pytest.raises(TypeError):
            operation()
    with pytest.raises(TypeError):
        result.payload_bytes = b"forged"  # type: ignore[misc]
