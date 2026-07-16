"""CBC tests for the sealed candidate-bound Linux supervisor entrypoint."""

from __future__ import annotations

import copy
import hashlib
import inspect
import pickle
from pathlib import Path
from typing import Any, cast

import pytest

from tests.test_zrpf_spot_v7_firecracker_descriptor_staging import (
    _fixture as descriptor_fixture,
)
from tests.test_zrpf_spot_v7_firecracker_root_supervisor_candidate_policy_v1 import (
    _canonical,
    _contract_document,
    _release_candidate_for_contract,
)
from tools import zrpf_spot_v7_firecracker_linux_runner as linux_runner
from tools import zrpf_spot_v7_firecracker_root_supervisor as root_supervisor
from tools import zrpf_spot_v7_firecracker_root_supervisor_candidate_policy_v1 as policy
from tools._zrpf_spot_v7_firecracker_descriptor_handoff import (
    _PreparedDescriptorBoundSpotV7LaunchV1,
)
from tools.zrpf_spot_v7_firecracker_linux_netns_adapter import (
    PinnedLinuxSpotV7NetworkNamespaceKernelV1,
)
from tools.zrpf_spot_v7_release_candidate_manifest_v1 import (
    parse_exact_spot_v7_release_candidate_manifest_v1,
)


def _candidate_policy_for_launch(
    prepared_launch: _PreparedDescriptorBoundSpotV7LaunchV1,
    *,
    firecracker_profile_sha256: str | None = None,
) -> policy.PreparedCandidateBoundSpotV7RootSupervisorPolicyV1:
    contract = _contract_document(
        runtime_manifest_sha256=prepared_launch.runtime_manifest_sha256.hex(),
        firecracker_profile_sha256=firecracker_profile_sha256,
    )
    candidate_bytes = _release_candidate_for_contract(
        contract,
        artifact_set_id=prepared_launch.artifact_set_id.hex(),
        machine_config_sha256=(prepared_launch.runtime_manifest.machine_config_sha256.hex()),
        authority_input_profile_sha256=(
            prepared_launch.runtime_manifest.authority_input_profile_sha256.hex()
        ),
    )
    candidate = parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes)
    return policy.prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
        exact_root_supervisor_contract_bytes=_canonical(contract),
        exact_release_candidate_bytes=candidate_bytes,
        expected_candidate_id=candidate.candidate_id,
    )


def _governed_execution_for_test(
    prepared_launch: _PreparedDescriptorBoundSpotV7LaunchV1,
    prepared_policy: policy.PreparedCandidateBoundSpotV7RootSupervisorPolicyV1,
    *,
    helper_path: Path | None = None,
) -> linux_runner._GovernedCandidateBoundSpotV7ExecutionV1:
    candidate_bound_plan = policy.derive_candidate_bound_spot_v7_root_supervisor_plan_v1(
        prepared_launch=prepared_launch,
        prepared_candidate_policy=prepared_policy,
    )
    return linux_runner._GovernedCandidateBoundSpotV7ExecutionV1(
        prepared_launch=prepared_launch,
        candidate_bound_plan=candidate_bound_plan,
        helper_executable_path=(
            helper_path or Path("/usr/libexec/zenodex/zrpf-firecracker-netns-helper")
        ),
        selected_candidate_id=candidate_bound_plan.candidate_id,
        selected_candidate_manifest_sha256=(candidate_bound_plan.candidate_manifest_sha256),
        selected_evidence_inventory_root=(candidate_bound_plan.evidence_inventory_root),
        governed_host_control_policy_sha256=candidate_bound_plan.contract_sha256,
        governed_runtime_manifest_sha256=(candidate_bound_plan.runtime_manifest_sha256),
        governed_firecracker_profile_sha256=(candidate_bound_plan.firecracker_profile_sha256),
        governed_helper_sha256=candidate_bound_plan.netns_helper_sha256,
        seal=linux_runner._GOVERNED_CANDIDATE_EXECUTION_SEAL_V1,
    )


def _completed_run(
    candidate_bound_plan: policy.CandidateBoundSpotV7RootSupervisorPlanV1,
) -> root_supervisor.CompletedSpotV7RootSupervisorRunV1:
    plan = candidate_bound_plan.root_supervisor_plan
    return root_supervisor.CompletedSpotV7RootSupervisorRunV1(
        payload_bytes=b"verified-spot-v7-payload",
        request_sha256=hashlib.sha256(b"request").digest(),
        cgroup_relative_path=plan.expected_cgroup_relative_path,
        network_namespace_path=plan.expected_network_namespace_path,
        prepare_observation_sha256=hashlib.sha256(b"prepare").digest(),
        launch_observation_sha256=hashlib.sha256(b"launch").digest(),
        finish_observation_sha256=hashlib.sha256(b"finish").digest(),
        seal=root_supervisor._COMPLETED_SUPERVISOR_SEAL_V1,
    )


def test_candidate_bound_runner_accepts_only_private_governed_capability() -> None:
    parameters = inspect.signature(
        linux_runner.run_candidate_bound_linux_spot_v7_root_supervisor_v1
    ).parameters

    assert tuple(parameters) == ("governed_execution",)
    assert "prepared_launch" not in parameters
    assert "prepared_candidate_policy" not in parameters
    assert "helper_executable_path" not in parameters
    assert "plan" not in parameters
    assert "network_namespace_kernel" not in parameters
    assert "os_port" not in parameters
    assert "_GovernedCandidateBoundSpotV7ExecutionV1" not in linux_runner.__all__
    with pytest.raises(TypeError):
        cast(Any, linux_runner._GovernedCandidateBoundSpotV7ExecutionV1)()


def test_candidate_bound_plan_retains_candidate_launch_and_helper_identities(
    tmp_path: Path,
) -> None:
    fixture = descriptor_fixture(tmp_path)
    prepared_launch = fixture.prepare(fixture.open_bound())
    prepared_policy = _candidate_policy_for_launch(prepared_launch)
    try:
        candidate_bound_plan = policy.derive_candidate_bound_spot_v7_root_supervisor_plan_v1(
            prepared_launch=prepared_launch,
            prepared_candidate_policy=prepared_policy,
        )

        assert candidate_bound_plan.candidate_id == prepared_policy.candidate_id
        assert (
            candidate_bound_plan.evidence_inventory_root == prepared_policy.evidence_inventory_root
        )
        assert (
            candidate_bound_plan.candidate_manifest_sha256
            == prepared_policy.candidate_manifest_sha256
        )
        assert candidate_bound_plan.contract_sha256 == prepared_policy.contract_sha256
        assert (
            candidate_bound_plan.runtime_manifest_sha256 == prepared_launch.runtime_manifest_sha256
        )
        assert candidate_bound_plan.artifact_set_id == prepared_launch.artifact_set_id
        assert (
            candidate_bound_plan.machine_config_sha256
            == prepared_launch.runtime_manifest.machine_config_sha256
        )
        assert (
            candidate_bound_plan.authority_input_profile_sha256
            == prepared_launch.runtime_manifest.authority_input_profile_sha256
        )
        assert (
            candidate_bound_plan.firecracker_profile_sha256
            == prepared_policy.firecracker_profile_sha256
        )
        assert candidate_bound_plan.netns_helper_sha256 == bytes.fromhex(
            prepared_policy.netns_helper_sha256
        )
        assert candidate_bound_plan.candidate_bound_identity_sha256
        assert candidate_bound_plan.live_execution_verified is False
        assert candidate_bound_plan.release_authority is False
        assert candidate_bound_plan.production_authority is False
    finally:
        cast(_PreparedDescriptorBoundSpotV7LaunchV1, prepared_launch).close_before_launch()


def test_governed_execution_and_typed_plan_are_nontransferable(
    tmp_path: Path,
) -> None:
    fixture = descriptor_fixture(tmp_path)
    prepared_launch = fixture.prepare(fixture.open_bound())
    prepared_policy = _candidate_policy_for_launch(prepared_launch)
    capability = _governed_execution_for_test(prepared_launch, prepared_policy)
    candidate_bound_plan = capability._candidate_bound_plan
    try:
        for value in (candidate_bound_plan, capability):
            with pytest.raises(TypeError):
                copy.copy(value)
            with pytest.raises(TypeError):
                copy.deepcopy(value)
            with pytest.raises(TypeError):
                pickle.dumps(value)
            with pytest.raises(TypeError):
                cast(Any, value)._seal = object()
    finally:
        prepared_launch.close_before_launch()


def test_candidate_bound_runner_uses_only_governed_bound_inputs(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = descriptor_fixture(tmp_path)
    prepared_launch = fixture.prepare(fixture.open_bound())
    prepared_policy = _candidate_policy_for_launch(prepared_launch)
    capability = _governed_execution_for_test(prepared_launch, prepared_policy)
    candidate_bound_plan = capability._candidate_bound_plan
    completed = _completed_run(candidate_bound_plan)
    observed: dict[str, object] = {}

    def capture(**kwargs: object) -> root_supervisor.CompletedSpotV7RootSupervisorRunV1:
        observed.update(kwargs)
        return completed

    monkeypatch.setattr(
        linux_runner,
        "run_spot_v7_root_supervisor_contract_v1",
        capture,
    )
    try:
        result = linux_runner.run_candidate_bound_linux_spot_v7_root_supervisor_v1(
            governed_execution=capability,
        )

        assert result.completed_run is completed
        assert result.candidate_id == candidate_bound_plan.candidate_id
        assert result.evidence_inventory_root == candidate_bound_plan.evidence_inventory_root
        assert result.candidate_manifest_sha256 == candidate_bound_plan.candidate_manifest_sha256
        assert result.contract_sha256 == candidate_bound_plan.contract_sha256
        assert result.runtime_manifest_sha256 == candidate_bound_plan.runtime_manifest_sha256
        assert result.firecracker_profile_sha256 == candidate_bound_plan.firecracker_profile_sha256
        assert result.netns_helper_sha256 == candidate_bound_plan.netns_helper_sha256
        assert (
            result.candidate_bound_identity_sha256
            == candidate_bound_plan.candidate_bound_identity_sha256
        )
        assert result.artifact_set_id == candidate_bound_plan.artifact_set_id
        assert result.machine_config_sha256 == candidate_bound_plan.machine_config_sha256
        assert (
            result.authority_input_profile_sha256
            == candidate_bound_plan.authority_input_profile_sha256
        )
        assert observed["prepared_launch"] is prepared_launch
        assert observed["plan"] is candidate_bound_plan.root_supervisor_plan
        port = cast(
            linux_runner.LinuxSpotV7RootSupervisorOsPortV1,
            observed["os_port"],
        )
        kernel = port._namespace_control._kernel
        assert type(kernel) is PinnedLinuxSpotV7NetworkNamespaceKernelV1
        assert kernel._executable == capability._helper_executable_path
        assert kernel._expected_sha256 == candidate_bound_plan.netns_helper_sha256.hex()
        assert result.live_execution_verified is False
        assert result.runtime_authority is False
        assert result.release_authority is False
        assert result.settlement_authority is False
        assert result.production_authority is False
    finally:
        cast(_PreparedDescriptorBoundSpotV7LaunchV1, prepared_launch).close_before_launch()


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("selected_candidate_id", b"s" * 32),
        ("selected_candidate_manifest_sha256", b"m" * 32),
        ("selected_evidence_inventory_root", b"i" * 32),
        ("governed_host_control_policy_sha256", b"h" * 32),
        ("governed_runtime_manifest_sha256", b"r" * 32),
        ("governed_firecracker_profile_sha256", b"f" * 32),
        ("governed_helper_sha256", b"n" * 32),
    ),
)
def test_governed_capability_rejects_each_independent_identity_substitution(
    tmp_path: Path,
    field: str,
    value: bytes,
) -> None:
    fixture = descriptor_fixture(tmp_path)
    prepared_launch = fixture.prepare(fixture.open_bound())
    prepared_policy = _candidate_policy_for_launch(prepared_launch)
    candidate_bound_plan = policy.derive_candidate_bound_spot_v7_root_supervisor_plan_v1(
        prepared_launch=prepared_launch,
        prepared_candidate_policy=prepared_policy,
    )
    kwargs: dict[str, object] = {
        "prepared_launch": prepared_launch,
        "candidate_bound_plan": candidate_bound_plan,
        "helper_executable_path": Path("/usr/libexec/zenodex/zrpf-firecracker-netns-helper"),
        "selected_candidate_id": candidate_bound_plan.candidate_id,
        "selected_candidate_manifest_sha256": (candidate_bound_plan.candidate_manifest_sha256),
        "selected_evidence_inventory_root": (candidate_bound_plan.evidence_inventory_root),
        "governed_host_control_policy_sha256": candidate_bound_plan.contract_sha256,
        "governed_runtime_manifest_sha256": (candidate_bound_plan.runtime_manifest_sha256),
        "governed_firecracker_profile_sha256": (candidate_bound_plan.firecracker_profile_sha256),
        "governed_helper_sha256": candidate_bound_plan.netns_helper_sha256,
        "seal": linux_runner._GOVERNED_CANDIDATE_EXECUTION_SEAL_V1,
    }
    kwargs[field] = value
    try:
        with pytest.raises(root_supervisor.SpotV7RootSupervisorRejectV1) as captured:
            cast(Any, linux_runner._GovernedCandidateBoundSpotV7ExecutionV1)(**kwargs)
        assert captured.value.code == "linux_runner_governed_identity_mismatch"
        prepared_launch.verify_prelaunch()
    finally:
        cast(_PreparedDescriptorBoundSpotV7LaunchV1, prepared_launch).close_before_launch()


def test_distinct_candidates_with_same_runtime_cannot_collapse_to_same_typed_plan(
    tmp_path: Path,
) -> None:
    fixture = descriptor_fixture(tmp_path)
    prepared_launch = fixture.prepare(fixture.open_bound())
    first = _candidate_policy_for_launch(
        prepared_launch,
        firecracker_profile_sha256=hashlib.sha256(b"profile-a").hexdigest(),
    )
    second = _candidate_policy_for_launch(
        prepared_launch,
        firecracker_profile_sha256=hashlib.sha256(b"profile-b").hexdigest(),
    )
    try:
        first_plan = policy.derive_candidate_bound_spot_v7_root_supervisor_plan_v1(
            prepared_launch=prepared_launch,
            prepared_candidate_policy=first,
        )
        second_plan = policy.derive_candidate_bound_spot_v7_root_supervisor_plan_v1(
            prepared_launch=prepared_launch,
            prepared_candidate_policy=second,
        )

        assert first_plan.root_supervisor_plan == second_plan.root_supervisor_plan
        assert first_plan.candidate_id != second_plan.candidate_id
        assert first_plan.candidate_manifest_sha256 != second_plan.candidate_manifest_sha256
        assert first_plan.firecracker_profile_sha256 != second_plan.firecracker_profile_sha256
        assert (
            first_plan.candidate_bound_identity_sha256
            != second_plan.candidate_bound_identity_sha256
        )
    finally:
        cast(_PreparedDescriptorBoundSpotV7LaunchV1, prepared_launch).close_before_launch()


def test_plan_derivation_uses_fresh_reparsed_policy_snapshot(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fixture = descriptor_fixture(tmp_path)
    prepared_launch = fixture.prepare(fixture.open_bound())
    prepared_policy = _candidate_policy_for_launch(prepared_launch)
    original_revalidate = policy._revalidate_prepared_policy

    def mutate_after_reparse(
        value: object,
    ) -> policy.PreparedCandidateBoundSpotV7RootSupervisorPolicyV1:
        reparsed = original_revalidate(value)
        object.__setattr__(
            prepared_policy,
            "_process_timeout_ns",
            prepared_policy.process_timeout_ns + 1,
        )
        return reparsed

    monkeypatch.setattr(policy, "_revalidate_prepared_policy", mutate_after_reparse)
    try:
        candidate_bound_plan = policy.derive_candidate_bound_spot_v7_root_supervisor_plan_v1(
            prepared_launch=prepared_launch,
            prepared_candidate_policy=prepared_policy,
        )
        assert candidate_bound_plan.root_supervisor_plan.process_timeout_ns == 30_000_000_000
    finally:
        cast(_PreparedDescriptorBoundSpotV7LaunchV1, prepared_launch).close_before_launch()


def test_candidate_bound_runner_rejects_raw_or_forged_capability_before_effects(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        linux_runner,
        "run_spot_v7_root_supervisor_contract_v1",
        lambda **_kwargs: pytest.fail("forged capability reached execution"),
    )

    with pytest.raises(root_supervisor.SpotV7RootSupervisorRejectV1) as captured:
        cast(Any, linux_runner.run_candidate_bound_linux_spot_v7_root_supervisor_v1)(
            governed_execution=object(),
        )
    assert captured.value.code == "linux_runner_governed_execution_invalid"

    forged = object.__new__(linux_runner._GovernedCandidateBoundSpotV7ExecutionV1)
    with pytest.raises(root_supervisor.SpotV7RootSupervisorRejectV1) as forged_error:
        linux_runner.run_candidate_bound_linux_spot_v7_root_supervisor_v1(
            governed_execution=forged,
        )
    assert forged_error.value.code == "linux_runner_governed_execution_invalid"


def test_candidate_bound_runner_claims_remain_false() -> None:
    assert linux_runner.LINUX_RUNNER_LIVE_EXECUTION_VERIFIED_V1 is False
    assert linux_runner.LINUX_RUNNER_LIVE_OWNERSHIP_VERIFIED_V1 is False
    assert linux_runner.LINUX_RUNNER_RUNTIME_AUTHORITY_V1 is False
    assert linux_runner.LINUX_RUNNER_SETTLEMENT_AUTHORITY_V1 is False
    assert linux_runner.LINUX_RUNNER_RELEASE_AUTHORITY_V1 is False
    assert linux_runner.LINUX_RUNNER_PRODUCTION_AUTHORITY_V1 is False
