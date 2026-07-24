"""Exact authority-false Linux entrypoint for one staged Spot V7 launch.

The lower-level root-supervisor contract intentionally accepts a structural
OS-port protocol so its ordering and teardown laws can be tested without root
privileges.  Planning remains authority-neutral.  The effectful
candidate-bound route accepts only a private sealed value that joins an
independently selected candidate, helper identity, and host-control policy.

Successful return is still an authority-false observation.  This module does
not establish that a privileged host executed the path, that the selected
artifacts are release-governed, or that the payload may authorize settlement.
No public mint for the governed execution value exists in this module.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import NoReturn, SupportsIndex, final

from tools._zrpf_spot_v7_firecracker_descriptor_handoff import (
    _PreparedDescriptorBoundSpotV7LaunchV1,
)
from tools.zrpf_spot_v7_firecracker_linux_netns_adapter import (
    PinnedLinuxSpotV7NetworkNamespaceKernelV1,
)
from tools.zrpf_spot_v7_firecracker_linux_port import (
    LinuxSpotV7RootSupervisorOsPortV1,
)
from tools.zrpf_spot_v7_firecracker_root_supervisor import (
    CompletedSpotV7RootSupervisorRunV1,
    SpotV7RootSupervisorPlanV1,
    SpotV7RootSupervisorRejectV1,
    run_spot_v7_root_supervisor_contract_v1,
)
from tools.zrpf_spot_v7_firecracker_root_supervisor_candidate_policy_v1 import (
    CandidateBoundSpotV7RootSupervisorPlanV1,
)
from tools.zrpf_v3_firecracker_cgroup_v2 import is_canonical_absolute_path_v1

LINUX_RUNNER_LIVE_EXECUTION_VERIFIED_V1 = False
LINUX_RUNNER_LIVE_OWNERSHIP_VERIFIED_V1 = False
LINUX_RUNNER_RUNTIME_AUTHORITY_V1 = False
LINUX_RUNNER_SETTLEMENT_AUTHORITY_V1 = False
LINUX_RUNNER_RELEASE_AUTHORITY_V1 = False
LINUX_RUNNER_PRODUCTION_AUTHORITY_V1 = False


class _GovernedCandidateExecutionSealV1:
    __slots__ = ()


_GOVERNED_CANDIDATE_EXECUTION_SEAL_V1 = _GovernedCandidateExecutionSealV1()


class _CandidateBoundResultSealV1:
    __slots__ = ()


_CANDIDATE_BOUND_RESULT_SEAL_V1 = _CandidateBoundResultSealV1()


@dataclass(frozen=True, slots=True)
class _GovernedExecutionSnapshotV1:
    prepared_launch: _PreparedDescriptorBoundSpotV7LaunchV1
    candidate_bound_plan: CandidateBoundSpotV7RootSupervisorPlanV1
    helper_executable_path: Path


@final
class _GovernedCandidateBoundSpotV7ExecutionV1:
    """Private join of selected candidate, helper, and host-control policy.

    There is deliberately no public mint.  A future governance adapter must
    obtain each independently governed identity and compare it with the typed
    authority-neutral plan before using this private construction boundary.
    """

    __slots__ = (
        "_candidate_bound_plan",
        "_governed_firecracker_profile_sha256",
        "_governed_helper_sha256",
        "_governed_host_control_policy_sha256",
        "_governed_runtime_manifest_sha256",
        "_helper_executable_path",
        "_prepared_launch",
        "_seal",
        "_selected_candidate_id",
        "_selected_candidate_manifest_sha256",
        "_selected_evidence_inventory_root",
    )

    _candidate_bound_plan: CandidateBoundSpotV7RootSupervisorPlanV1
    _governed_firecracker_profile_sha256: bytes
    _governed_helper_sha256: bytes
    _governed_host_control_policy_sha256: bytes
    _governed_runtime_manifest_sha256: bytes
    _helper_executable_path: Path
    _prepared_launch: _PreparedDescriptorBoundSpotV7LaunchV1
    _seal: _GovernedCandidateExecutionSealV1
    _selected_candidate_id: bytes
    _selected_candidate_manifest_sha256: bytes
    _selected_evidence_inventory_root: bytes

    def __init__(
        self,
        *,
        prepared_launch: _PreparedDescriptorBoundSpotV7LaunchV1,
        candidate_bound_plan: CandidateBoundSpotV7RootSupervisorPlanV1,
        helper_executable_path: Path,
        selected_candidate_id: bytes,
        selected_candidate_manifest_sha256: bytes,
        selected_evidence_inventory_root: bytes,
        governed_host_control_policy_sha256: bytes,
        governed_runtime_manifest_sha256: bytes,
        governed_firecracker_profile_sha256: bytes,
        governed_helper_sha256: bytes,
        seal: _GovernedCandidateExecutionSealV1,
    ) -> None:
        if seal is not _GOVERNED_CANDIDATE_EXECUTION_SEAL_V1:
            raise TypeError("candidate-bound execution requires the module-private governed seal")
        object.__setattr__(self, "_prepared_launch", prepared_launch)
        object.__setattr__(self, "_candidate_bound_plan", candidate_bound_plan)
        object.__setattr__(self, "_helper_executable_path", helper_executable_path)
        object.__setattr__(self, "_selected_candidate_id", selected_candidate_id)
        object.__setattr__(
            self,
            "_selected_candidate_manifest_sha256",
            selected_candidate_manifest_sha256,
        )
        object.__setattr__(
            self,
            "_selected_evidence_inventory_root",
            selected_evidence_inventory_root,
        )
        object.__setattr__(
            self,
            "_governed_host_control_policy_sha256",
            governed_host_control_policy_sha256,
        )
        object.__setattr__(
            self,
            "_governed_runtime_manifest_sha256",
            governed_runtime_manifest_sha256,
        )
        object.__setattr__(
            self,
            "_governed_firecracker_profile_sha256",
            governed_firecracker_profile_sha256,
        )
        object.__setattr__(self, "_governed_helper_sha256", governed_helper_sha256)
        object.__setattr__(self, "_seal", seal)
        _snapshot_governed_execution(self)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("governed candidate-bound execution cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("governed candidate-bound execution cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("governed candidate-bound execution cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("governed candidate-bound execution cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("governed candidate-bound execution cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("governed candidate-bound execution cannot be serialized")

    def _has_private_governed_seal(self) -> bool:
        return getattr(self, "_seal", None) is _GOVERNED_CANDIDATE_EXECUTION_SEAL_V1


@final
class CandidateBoundSpotV7RootSupervisorRunV1:
    """Bound result observation retaining candidate and helper identities."""

    __slots__ = (
        "_artifact_set_id",
        "_authority_input_profile_sha256",
        "_candidate_bound_identity_sha256",
        "_candidate_id",
        "_candidate_manifest_sha256",
        "_completed_run",
        "_contract_sha256",
        "_evidence_inventory_root",
        "_firecracker_profile_sha256",
        "_machine_config_sha256",
        "_netns_helper_sha256",
        "_runtime_manifest_sha256",
        "_seal",
    )

    _candidate_bound_identity_sha256: bytes
    _artifact_set_id: bytes
    _authority_input_profile_sha256: bytes
    _candidate_id: bytes
    _candidate_manifest_sha256: bytes
    _completed_run: CompletedSpotV7RootSupervisorRunV1
    _contract_sha256: bytes
    _evidence_inventory_root: bytes
    _firecracker_profile_sha256: bytes
    _machine_config_sha256: bytes
    _netns_helper_sha256: bytes
    _runtime_manifest_sha256: bytes
    _seal: _CandidateBoundResultSealV1

    def __new__(cls) -> CandidateBoundSpotV7RootSupervisorRunV1:
        raise TypeError("candidate-bound result requires validated construction")

    @classmethod
    def _from_completed(
        cls,
        *,
        completed_run: CompletedSpotV7RootSupervisorRunV1,
        candidate_bound_plan: CandidateBoundSpotV7RootSupervisorPlanV1,
        seal: _CandidateBoundResultSealV1,
    ) -> CandidateBoundSpotV7RootSupervisorRunV1:
        if seal is not _CANDIDATE_BOUND_RESULT_SEAL_V1:
            raise TypeError("candidate-bound result requires the module-private seal")
        if type(completed_run) is not CompletedSpotV7RootSupervisorRunV1:
            raise TypeError("candidate-bound result requires the exact completed run")
        if (
            type(candidate_bound_plan) is not CandidateBoundSpotV7RootSupervisorPlanV1
            or not candidate_bound_plan._has_private_plan_seal()
        ):
            raise TypeError("candidate-bound result requires the exact sealed plan")
        plan = candidate_bound_plan.root_supervisor_plan
        if (
            completed_run.cgroup_relative_path != plan.expected_cgroup_relative_path
            or completed_run.network_namespace_path != plan.expected_network_namespace_path
        ):
            raise SpotV7RootSupervisorRejectV1("linux_runner_completed_control_binding_mismatch")
        value = object.__new__(cls)
        object.__setattr__(value, "_completed_run", completed_run)
        object.__setattr__(value, "_candidate_id", candidate_bound_plan.candidate_id)
        object.__setattr__(
            value,
            "_evidence_inventory_root",
            candidate_bound_plan.evidence_inventory_root,
        )
        object.__setattr__(
            value,
            "_candidate_manifest_sha256",
            candidate_bound_plan.candidate_manifest_sha256,
        )
        object.__setattr__(value, "_contract_sha256", candidate_bound_plan.contract_sha256)
        object.__setattr__(
            value,
            "_runtime_manifest_sha256",
            candidate_bound_plan.runtime_manifest_sha256,
        )
        object.__setattr__(
            value,
            "_firecracker_profile_sha256",
            candidate_bound_plan.firecracker_profile_sha256,
        )
        object.__setattr__(
            value,
            "_netns_helper_sha256",
            candidate_bound_plan.netns_helper_sha256,
        )
        object.__setattr__(
            value,
            "_candidate_bound_identity_sha256",
            candidate_bound_plan.candidate_bound_identity_sha256,
        )
        object.__setattr__(value, "_artifact_set_id", candidate_bound_plan.artifact_set_id)
        object.__setattr__(
            value,
            "_machine_config_sha256",
            candidate_bound_plan.machine_config_sha256,
        )
        object.__setattr__(
            value,
            "_authority_input_profile_sha256",
            candidate_bound_plan.authority_input_profile_sha256,
        )
        object.__setattr__(value, "_seal", seal)
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("candidate-bound result cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("candidate-bound result cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("candidate-bound result cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("candidate-bound result cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("candidate-bound result cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("candidate-bound result cannot be serialized")

    @property
    def completed_run(self) -> CompletedSpotV7RootSupervisorRunV1:
        return self._completed_run

    @property
    def candidate_id(self) -> bytes:
        return self._candidate_id

    @property
    def evidence_inventory_root(self) -> bytes:
        return self._evidence_inventory_root

    @property
    def candidate_manifest_sha256(self) -> bytes:
        return self._candidate_manifest_sha256

    @property
    def contract_sha256(self) -> bytes:
        return self._contract_sha256

    @property
    def runtime_manifest_sha256(self) -> bytes:
        return self._runtime_manifest_sha256

    @property
    def firecracker_profile_sha256(self) -> bytes:
        return self._firecracker_profile_sha256

    @property
    def netns_helper_sha256(self) -> bytes:
        return self._netns_helper_sha256

    @property
    def candidate_bound_identity_sha256(self) -> bytes:
        return self._candidate_bound_identity_sha256

    @property
    def artifact_set_id(self) -> bytes:
        return self._artifact_set_id

    @property
    def machine_config_sha256(self) -> bytes:
        return self._machine_config_sha256

    @property
    def authority_input_profile_sha256(self) -> bytes:
        return self._authority_input_profile_sha256

    @property
    def live_execution_verified(self) -> bool:
        return False

    @property
    def runtime_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _run_exact_linux_spot_v7_root_supervisor_candidate_v1(
    *,
    prepared_launch: _PreparedDescriptorBoundSpotV7LaunchV1,
    plan: SpotV7RootSupervisorPlanV1,
    network_namespace_kernel: PinnedLinuxSpotV7NetworkNamespaceKernelV1,
) -> CompletedSpotV7RootSupervisorRunV1:
    """Run the candidate route with no caller-supplied OS-port implementation.

    Exact-type checks happen before constructing the effectful Linux port and
    before the staged launch is spent.  The delegated supervisor retains sole
    ownership of execution ordering, output validation, and teardown.  Callers
    should supply a fresh helper instance for each run; this candidate boundary
    does not promote that operational expectation to authority.
    """

    if (
        not isinstance(prepared_launch, _PreparedDescriptorBoundSpotV7LaunchV1)
        or type(prepared_launch) is not _PreparedDescriptorBoundSpotV7LaunchV1
    ):
        raise SpotV7RootSupervisorRejectV1("linux_runner_prepared_launch_invalid")
    if type(plan) is not SpotV7RootSupervisorPlanV1:
        raise SpotV7RootSupervisorRejectV1("linux_runner_plan_invalid")
    if type(network_namespace_kernel) is not PinnedLinuxSpotV7NetworkNamespaceKernelV1:
        raise SpotV7RootSupervisorRejectV1("linux_runner_namespace_kernel_invalid")
    os_port = LinuxSpotV7RootSupervisorOsPortV1(network_namespace_kernel)
    return run_spot_v7_root_supervisor_contract_v1(
        prepared_launch=prepared_launch,
        plan=plan,
        os_port=os_port,
    )


def run_candidate_bound_linux_spot_v7_root_supervisor_v1(
    *,
    governed_execution: _GovernedCandidateBoundSpotV7ExecutionV1,
) -> CandidateBoundSpotV7RootSupervisorRunV1:
    """Run one exact governed join and retain all identities in the result."""

    snapshot = _snapshot_governed_execution(governed_execution)
    plan = snapshot.candidate_bound_plan
    network_namespace_kernel = PinnedLinuxSpotV7NetworkNamespaceKernelV1(
        executable=snapshot.helper_executable_path,
        expected_sha256=plan.netns_helper_sha256.hex(),
    )
    os_port = LinuxSpotV7RootSupervisorOsPortV1(network_namespace_kernel)
    completed = run_spot_v7_root_supervisor_contract_v1(
        prepared_launch=snapshot.prepared_launch,
        plan=plan.root_supervisor_plan,
        os_port=os_port,
    )
    return CandidateBoundSpotV7RootSupervisorRunV1._from_completed(
        completed_run=completed,
        candidate_bound_plan=plan,
        seal=_CANDIDATE_BOUND_RESULT_SEAL_V1,
    )


def _snapshot_governed_execution(
    value: object,
) -> _GovernedExecutionSnapshotV1:
    if (
        not isinstance(value, _GovernedCandidateBoundSpotV7ExecutionV1)
        or type(value) is not _GovernedCandidateBoundSpotV7ExecutionV1
        or getattr(value, "_seal", None) is not _GOVERNED_CANDIDATE_EXECUTION_SEAL_V1
    ):
        raise SpotV7RootSupervisorRejectV1("linux_runner_governed_execution_invalid")
    execution = value
    prepared_launch = execution._prepared_launch
    candidate_bound_plan = execution._candidate_bound_plan
    helper_path = execution._helper_executable_path
    if type(prepared_launch) is not _PreparedDescriptorBoundSpotV7LaunchV1:
        raise SpotV7RootSupervisorRejectV1("linux_runner_governed_execution_invalid")
    if (
        not isinstance(candidate_bound_plan, CandidateBoundSpotV7RootSupervisorPlanV1)
        or type(candidate_bound_plan) is not CandidateBoundSpotV7RootSupervisorPlanV1
    ):
        raise SpotV7RootSupervisorRejectV1("linux_runner_governed_execution_invalid")
    checked_launch = prepared_launch
    checked_plan = candidate_bound_plan
    if not checked_plan._has_private_plan_seal():
        raise SpotV7RootSupervisorRejectV1("linux_runner_governed_execution_invalid")
    if not isinstance(helper_path, Path) or not is_canonical_absolute_path_v1(helper_path):
        raise SpotV7RootSupervisorRejectV1("linux_runner_governed_execution_invalid")
    checked_helper_path = helper_path
    governed_identities = (
        execution._selected_candidate_id,
        execution._selected_candidate_manifest_sha256,
        execution._selected_evidence_inventory_root,
        execution._governed_host_control_policy_sha256,
        execution._governed_runtime_manifest_sha256,
        execution._governed_firecracker_profile_sha256,
        execution._governed_helper_sha256,
    )
    if any(type(identity) is not bytes or len(identity) != 32 for identity in governed_identities):
        raise SpotV7RootSupervisorRejectV1("linux_runner_governed_execution_invalid")
    expected_identities = (
        checked_plan.candidate_id,
        checked_plan.candidate_manifest_sha256,
        checked_plan.evidence_inventory_root,
        checked_plan.contract_sha256,
        checked_plan.runtime_manifest_sha256,
        checked_plan.firecracker_profile_sha256,
        checked_plan.netns_helper_sha256,
    )
    if governed_identities != expected_identities:
        raise SpotV7RootSupervisorRejectV1("linux_runner_governed_identity_mismatch")
    if (
        checked_launch.runtime_manifest_sha256 != checked_plan.runtime_manifest_sha256
        or checked_launch.artifact_set_id != checked_plan.artifact_set_id
        or checked_launch.runtime_manifest.machine_config_sha256
        != checked_plan.machine_config_sha256
        or checked_launch.runtime_manifest.authority_input_profile_sha256
        != checked_plan.authority_input_profile_sha256
        or checked_launch.launch_spec.jail_id
        != checked_plan.root_supervisor_plan.cgroup_request.leaf_name
        or checked_launch.launch_spec.jail_id
        != checked_plan.root_supervisor_plan.network_namespace_name
    ):
        raise SpotV7RootSupervisorRejectV1("linux_runner_governed_launch_binding_mismatch")
    return _GovernedExecutionSnapshotV1(
        prepared_launch=checked_launch,
        candidate_bound_plan=checked_plan,
        helper_executable_path=checked_helper_path,
    )


__all__ = [
    "CandidateBoundSpotV7RootSupervisorRunV1",
    "LINUX_RUNNER_LIVE_EXECUTION_VERIFIED_V1",
    "LINUX_RUNNER_LIVE_OWNERSHIP_VERIFIED_V1",
    "LINUX_RUNNER_PRODUCTION_AUTHORITY_V1",
    "LINUX_RUNNER_RELEASE_AUTHORITY_V1",
    "LINUX_RUNNER_RUNTIME_AUTHORITY_V1",
    "LINUX_RUNNER_SETTLEMENT_AUTHORITY_V1",
    "run_candidate_bound_linux_spot_v7_root_supervisor_v1",
]
