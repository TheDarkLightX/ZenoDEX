"""Candidate-bound, authority-neutral Spot V7 root-supervisor policy.

The exact contract is an inventory artifact of one independently identified
Spot V7 release candidate.  This module reparses both objects, binds the
contract bytes and size to that inventory, and exposes only finite values from
the exact contract.  It neither selects the candidate nor grants execution,
release, settlement, or production authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Final, NoReturn, SupportsIndex, cast, final

from tools._zrpf_spot_v7_firecracker_descriptor_handoff import (
    _PreparedDescriptorBoundSpotV7LaunchV1,
)
from tools.zrpf_spot_v7_firecracker_root_supervisor import (
    SpotV7RootSupervisorPlanV1,
    SpotV7RootSupervisorRejectV1,
)
from tools.zrpf_spot_v7_release_candidate_manifest_v1 import (
    SpotV7ReleaseCandidateRejectV1,
    check_exact_spot_v7_release_candidate_manifest_v1,
)
from tools.zrpf_v3_firecracker_cgroup_contract import (
    CgroupLimitsV1,
    CgroupV2Reject,
    relative_components,
)
from tools.zrpf_v3_firecracker_cgroup_v2 import (
    CgroupCreateRequestV1,
    is_canonical_absolute_path_v1,
)

ROOT_SUPERVISOR_CANDIDATE_CONTRACT_SCHEMA_V1: Final = (
    "zenodex/zrpf_spot_v7_root_supervisor_candidate_contract/v1"
)
ROOT_SUPERVISOR_CANDIDATE_CONTRACT_STATUS_V1: Final = (
    "authority_neutral_release_candidate_bound_contract"
)
MAX_CANDIDATE_CONTRACT_BYTES_V1: Final = 64 * 1024
MAX_CANDIDATE_CONTRACT_JSON_DEPTH_V1: Final = 4
_CANDIDATE_BOUND_PLAN_ID_DOMAIN_V1: Final = (
    b"zenodex.zrpf.spot_v7.candidate_bound_root_supervisor_plan.v1\x00"
)

CANDIDATE_POLICY_AUTHORITY_FIELDS_V1: Final = (
    "candidate_selected",
    "live_execution_verified",
    "production_authority",
    "release_authority",
    "runtime_authority",
    "settlement_authority",
)
CANDIDATE_POLICY_NON_CLAIMS_V1: Final = (
    "the release candidate is parsed and bound but not selected or current",
    "no privileged Jailer or Firecracker execution is established",
    "no live cgroup, network-namespace, process, or teardown fact is established",
    "the netns helper digest is candidate data and has no release authority",
    "no runtime, release, settlement, or production authority",
)

_DOCUMENT_FIELDS_V1: Final = {
    "authority",
    "bindings",
    "cgroup",
    "format_flags",
    "network_namespace",
    "non_claims",
    "reserved_u32",
    "schema",
    "status",
    "timeouts",
}
_BINDING_FIELDS_V1: Final = {
    "firecracker_profile_sha256",
    "runtime_manifest_sha256",
}
_CGROUP_FIELDS_V1: Final = {
    "cgroup_mount",
    "limits",
    "mountinfo_path",
    "parent_relative_path",
    "proc_root",
    "trusted_uid",
}
_LIMIT_FIELDS_V1: Final = {
    "cpu_period_us",
    "cpu_quota_us",
    "cpuset_cpus",
    "cpuset_mems",
    "io_max",
    "memory_high_bytes",
    "memory_max_bytes",
    "memory_swap_max_bytes",
    "pids_max",
}
_NETWORK_NAMESPACE_FIELDS_V1: Final = {"helper_sha256", "root"}
_TIMEOUT_FIELDS_V1: Final = {"process_timeout_ns", "teardown_timeout_ns"}


class SpotV7RootSupervisorCandidatePolicyRejectV1(ValueError):
    """Stable fail-closed rejection at the candidate-policy boundary."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


@dataclass(frozen=True, slots=True)
class _ParsedCandidateContractV1:
    cgroup_mount: Path
    cgroup_parent_relative_path: str
    mountinfo_path: Path
    proc_root: Path
    trusted_uid: int
    cgroup_limits: CgroupLimitsV1
    network_namespace_root: Path
    netns_helper_sha256: str
    process_timeout_ns: int
    teardown_timeout_ns: int
    runtime_manifest_sha256: bytes
    firecracker_profile_sha256: bytes


class _CandidatePolicyConstructionSealV1:
    __slots__ = ()


_CANDIDATE_POLICY_CONSTRUCTION_SEAL_V1 = _CandidatePolicyConstructionSealV1()


@final
class PreparedCandidateBoundSpotV7RootSupervisorPolicyV1:
    """Validated candidate contract with every authority claim fixed false."""

    __slots__ = (
        "_artifact_set_id",
        "_authority_input_profile_sha256",
        "_candidate_id",
        "_candidate_manifest_sha256",
        "_cgroup_limits",
        "_cgroup_mount",
        "_cgroup_parent_relative_path",
        "_contract_sha256",
        "_exact_contract_bytes",
        "_exact_release_candidate_bytes",
        "_evidence_inventory_root",
        "_firecracker_profile_sha256",
        "_machine_config_sha256",
        "_mountinfo_path",
        "_netns_helper_sha256",
        "_network_namespace_root",
        "_proc_root",
        "_process_timeout_ns",
        "_seal",
        "_teardown_timeout_ns",
        "_trusted_uid",
        "_runtime_manifest_sha256",
    )

    _artifact_set_id: bytes
    _authority_input_profile_sha256: bytes
    _candidate_id: bytes
    _candidate_manifest_sha256: bytes
    _cgroup_limits: CgroupLimitsV1
    _cgroup_mount: Path
    _cgroup_parent_relative_path: str
    _contract_sha256: bytes
    _exact_contract_bytes: bytes
    _exact_release_candidate_bytes: bytes
    _evidence_inventory_root: bytes
    _firecracker_profile_sha256: bytes
    _machine_config_sha256: bytes
    _mountinfo_path: Path
    _netns_helper_sha256: str
    _network_namespace_root: Path
    _proc_root: Path
    _process_timeout_ns: int
    _seal: _CandidatePolicyConstructionSealV1
    _teardown_timeout_ns: int
    _trusted_uid: int
    _runtime_manifest_sha256: bytes

    def __new__(cls) -> PreparedCandidateBoundSpotV7RootSupervisorPolicyV1:
        raise TypeError("candidate policy requires validated construction")

    @classmethod
    def _from_validated(
        cls,
        *,
        exact_contract_bytes: bytes,
        exact_release_candidate_bytes: bytes,
        candidate_id: bytes,
        evidence_inventory_root: bytes,
        artifact_set_id: bytes,
        machine_config_sha256: bytes,
        authority_input_profile_sha256: bytes,
        parsed: _ParsedCandidateContractV1,
        seal: _CandidatePolicyConstructionSealV1,
    ) -> PreparedCandidateBoundSpotV7RootSupervisorPolicyV1:
        if seal is not _CANDIDATE_POLICY_CONSTRUCTION_SEAL_V1:
            raise TypeError("candidate policy requires the module-private seal")
        value = object.__new__(cls)
        object.__setattr__(value, "_exact_contract_bytes", exact_contract_bytes)
        object.__setattr__(
            value,
            "_exact_release_candidate_bytes",
            exact_release_candidate_bytes,
        )
        object.__setattr__(
            value,
            "_contract_sha256",
            hashlib.sha256(exact_contract_bytes).digest(),
        )
        object.__setattr__(value, "_candidate_id", candidate_id)
        object.__setattr__(
            value,
            "_candidate_manifest_sha256",
            hashlib.sha256(exact_release_candidate_bytes).digest(),
        )
        object.__setattr__(value, "_evidence_inventory_root", evidence_inventory_root)
        object.__setattr__(value, "_artifact_set_id", artifact_set_id)
        object.__setattr__(value, "_machine_config_sha256", machine_config_sha256)
        object.__setattr__(
            value,
            "_authority_input_profile_sha256",
            authority_input_profile_sha256,
        )
        object.__setattr__(value, "_cgroup_mount", parsed.cgroup_mount)
        object.__setattr__(
            value,
            "_cgroup_parent_relative_path",
            parsed.cgroup_parent_relative_path,
        )
        object.__setattr__(value, "_mountinfo_path", parsed.mountinfo_path)
        object.__setattr__(value, "_proc_root", parsed.proc_root)
        object.__setattr__(value, "_trusted_uid", parsed.trusted_uid)
        object.__setattr__(value, "_cgroup_limits", parsed.cgroup_limits)
        object.__setattr__(
            value,
            "_network_namespace_root",
            parsed.network_namespace_root,
        )
        object.__setattr__(value, "_netns_helper_sha256", parsed.netns_helper_sha256)
        object.__setattr__(value, "_process_timeout_ns", parsed.process_timeout_ns)
        object.__setattr__(value, "_teardown_timeout_ns", parsed.teardown_timeout_ns)
        object.__setattr__(
            value,
            "_runtime_manifest_sha256",
            parsed.runtime_manifest_sha256,
        )
        object.__setattr__(
            value,
            "_firecracker_profile_sha256",
            parsed.firecracker_profile_sha256,
        )
        object.__setattr__(value, "_seal", seal)
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("candidate policy cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("candidate policy cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("candidate policy cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("candidate policy cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("candidate policy cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("candidate policy cannot be serialized")

    @property
    def candidate_id(self) -> bytes:
        return self._candidate_id

    @property
    def candidate_manifest_sha256(self) -> bytes:
        return self._candidate_manifest_sha256

    @property
    def evidence_inventory_root(self) -> bytes:
        return self._evidence_inventory_root

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
    def contract_sha256(self) -> bytes:
        return self._contract_sha256

    @property
    def cgroup_mount(self) -> Path:
        return self._cgroup_mount

    @property
    def cgroup_parent_relative_path(self) -> str:
        return self._cgroup_parent_relative_path

    @property
    def mountinfo_path(self) -> Path:
        return self._mountinfo_path

    @property
    def proc_root(self) -> Path:
        return self._proc_root

    @property
    def trusted_uid(self) -> int:
        return self._trusted_uid

    @property
    def cgroup_limits(self) -> CgroupLimitsV1:
        return self._cgroup_limits

    @property
    def network_namespace_root(self) -> Path:
        return self._network_namespace_root

    @property
    def netns_helper_sha256(self) -> str:
        return self._netns_helper_sha256

    @property
    def process_timeout_ns(self) -> int:
        return self._process_timeout_ns

    @property
    def teardown_timeout_ns(self) -> int:
        return self._teardown_timeout_ns

    @property
    def runtime_manifest_sha256(self) -> bytes:
        return self._runtime_manifest_sha256

    @property
    def firecracker_profile_sha256(self) -> bytes:
        return self._firecracker_profile_sha256

    @property
    def candidate_selected(self) -> bool:
        return False

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


class _CandidateBoundPlanConstructionSealV1:
    __slots__ = ()


_CANDIDATE_BOUND_PLAN_CONSTRUCTION_SEAL_V1 = _CandidateBoundPlanConstructionSealV1()


@final
class CandidateBoundSpotV7RootSupervisorPlanV1:
    """Exact candidate, runtime, helper, and host-control planning identity.

    This value retains the identities that a later governed execution boundary
    must independently select.  It remains authority-neutral and cannot start
    a process by itself.
    """

    __slots__ = (
        "_artifact_set_id",
        "_authority_input_profile_sha256",
        "_candidate_bound_identity_sha256",
        "_candidate_id",
        "_candidate_manifest_sha256",
        "_contract_sha256",
        "_evidence_inventory_root",
        "_firecracker_profile_sha256",
        "_machine_config_sha256",
        "_netns_helper_sha256",
        "_root_supervisor_plan",
        "_runtime_manifest_sha256",
        "_seal",
    )

    _artifact_set_id: bytes
    _authority_input_profile_sha256: bytes
    _candidate_bound_identity_sha256: bytes
    _candidate_id: bytes
    _candidate_manifest_sha256: bytes
    _contract_sha256: bytes
    _evidence_inventory_root: bytes
    _firecracker_profile_sha256: bytes
    _machine_config_sha256: bytes
    _netns_helper_sha256: bytes
    _root_supervisor_plan: SpotV7RootSupervisorPlanV1
    _runtime_manifest_sha256: bytes
    _seal: _CandidateBoundPlanConstructionSealV1

    def __new__(cls) -> CandidateBoundSpotV7RootSupervisorPlanV1:
        raise TypeError("candidate-bound plan requires validated construction")

    @classmethod
    def _from_validated(
        cls,
        *,
        root_supervisor_plan: SpotV7RootSupervisorPlanV1,
        candidate_id: bytes,
        evidence_inventory_root: bytes,
        candidate_manifest_sha256: bytes,
        contract_sha256: bytes,
        runtime_manifest_sha256: bytes,
        artifact_set_id: bytes,
        machine_config_sha256: bytes,
        authority_input_profile_sha256: bytes,
        firecracker_profile_sha256: bytes,
        netns_helper_sha256: bytes,
        seal: _CandidateBoundPlanConstructionSealV1,
    ) -> CandidateBoundSpotV7RootSupervisorPlanV1:
        if seal is not _CANDIDATE_BOUND_PLAN_CONSTRUCTION_SEAL_V1:
            raise TypeError("candidate-bound plan requires the module-private seal")
        if type(root_supervisor_plan) is not SpotV7RootSupervisorPlanV1:
            raise TypeError("candidate-bound plan requires the exact supervisor plan")
        identities = (
            candidate_id,
            evidence_inventory_root,
            candidate_manifest_sha256,
            contract_sha256,
            runtime_manifest_sha256,
            artifact_set_id,
            machine_config_sha256,
            authority_input_profile_sha256,
            firecracker_profile_sha256,
            netns_helper_sha256,
        )
        if any(type(value) is not bytes or len(value) != 32 for value in identities):
            raise TypeError("candidate-bound plan requires exact digest identities")
        value = object.__new__(cls)
        object.__setattr__(value, "_root_supervisor_plan", root_supervisor_plan)
        object.__setattr__(value, "_candidate_id", candidate_id)
        object.__setattr__(value, "_evidence_inventory_root", evidence_inventory_root)
        object.__setattr__(
            value,
            "_candidate_manifest_sha256",
            candidate_manifest_sha256,
        )
        object.__setattr__(value, "_contract_sha256", contract_sha256)
        object.__setattr__(
            value,
            "_runtime_manifest_sha256",
            runtime_manifest_sha256,
        )
        object.__setattr__(value, "_artifact_set_id", artifact_set_id)
        object.__setattr__(value, "_machine_config_sha256", machine_config_sha256)
        object.__setattr__(
            value,
            "_authority_input_profile_sha256",
            authority_input_profile_sha256,
        )
        object.__setattr__(
            value,
            "_firecracker_profile_sha256",
            firecracker_profile_sha256,
        )
        object.__setattr__(value, "_netns_helper_sha256", netns_helper_sha256)
        object.__setattr__(
            value,
            "_candidate_bound_identity_sha256",
            _candidate_bound_plan_identity_sha256(
                candidate_id=candidate_id,
                evidence_inventory_root=evidence_inventory_root,
                candidate_manifest_sha256=candidate_manifest_sha256,
                contract_sha256=contract_sha256,
                runtime_manifest_sha256=runtime_manifest_sha256,
                artifact_set_id=artifact_set_id,
                machine_config_sha256=machine_config_sha256,
                authority_input_profile_sha256=authority_input_profile_sha256,
                firecracker_profile_sha256=firecracker_profile_sha256,
                netns_helper_sha256=netns_helper_sha256,
                jail_id=root_supervisor_plan.cgroup_request.leaf_name,
            ),
        )
        object.__setattr__(value, "_seal", seal)
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("candidate-bound plan cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("candidate-bound plan cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("candidate-bound plan cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("candidate-bound plan cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("candidate-bound plan cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("candidate-bound plan cannot be serialized")

    def _has_private_plan_seal(self) -> bool:
        return getattr(self, "_seal", None) is _CANDIDATE_BOUND_PLAN_CONSTRUCTION_SEAL_V1

    @property
    def root_supervisor_plan(self) -> SpotV7RootSupervisorPlanV1:
        return self._root_supervisor_plan

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
    def artifact_set_id(self) -> bytes:
        return self._artifact_set_id

    @property
    def machine_config_sha256(self) -> bytes:
        return self._machine_config_sha256

    @property
    def authority_input_profile_sha256(self) -> bytes:
        return self._authority_input_profile_sha256

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


def prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
    *,
    exact_root_supervisor_contract_bytes: bytes,
    exact_release_candidate_bytes: bytes,
    expected_candidate_id: bytes,
) -> PreparedCandidateBoundSpotV7RootSupervisorPolicyV1:
    """Reparse and bind one exact candidate and its supervisor contract."""

    contract = _decode_exact_contract(exact_root_supervisor_contract_bytes)
    try:
        candidate = check_exact_spot_v7_release_candidate_manifest_v1(
            exact_release_candidate_bytes,
            expected_candidate_id=expected_candidate_id,
        )
    except (SpotV7ReleaseCandidateRejectV1, TypeError, ValueError) as exc:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_release_candidate"
        ) from exc
    candidate_document = _decode_candidate_document(candidate.canonical_bytes)
    _bind_contract_inventory(
        contract_bytes=exact_root_supervisor_contract_bytes,
        candidate_document=candidate_document,
    )
    parsed = _parse_contract_fields(contract)
    runtime = cast(dict[str, object], candidate_document["runtime"])
    if parsed.runtime_manifest_sha256 != _digest_hex(
        runtime["runtime_manifest_sha256"],
        "candidate_policy_runtime_manifest_binding",
    ):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_runtime_manifest_binding"
        )
    if parsed.firecracker_profile_sha256 != _digest_hex(
        runtime["firecracker_profile_sha256"],
        "candidate_policy_firecracker_profile_binding",
    ):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_firecracker_profile_binding"
        )
    return PreparedCandidateBoundSpotV7RootSupervisorPolicyV1._from_validated(
        exact_contract_bytes=exact_root_supervisor_contract_bytes,
        exact_release_candidate_bytes=exact_release_candidate_bytes,
        candidate_id=candidate.candidate_id,
        evidence_inventory_root=candidate.evidence_inventory_root,
        artifact_set_id=_digest_hex(
            runtime["artifact_set_id"],
            "candidate_policy_artifact_set_id",
        ),
        machine_config_sha256=_digest_hex(
            runtime["machine_config_sha256"],
            "candidate_policy_machine_config",
        ),
        authority_input_profile_sha256=_digest_hex(
            runtime["authority_input_profile_sha256"],
            "candidate_policy_authority_input_profile",
        ),
        parsed=parsed,
        seal=_CANDIDATE_POLICY_CONSTRUCTION_SEAL_V1,
    )


def derive_candidate_bound_spot_v7_root_supervisor_plan_v1(
    *,
    prepared_launch: _PreparedDescriptorBoundSpotV7LaunchV1,
    prepared_candidate_policy: PreparedCandidateBoundSpotV7RootSupervisorPolicyV1,
) -> CandidateBoundSpotV7RootSupervisorPlanV1:
    """Derive the sole per-run control name from the descriptor launch jail ID."""

    if type(prepared_launch) is not _PreparedDescriptorBoundSpotV7LaunchV1:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_prepared_launch")
    checked_policy = _revalidate_prepared_policy(prepared_candidate_policy)
    if prepared_launch.runtime_manifest_sha256 != checked_policy.runtime_manifest_sha256:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_prepared_runtime_manifest"
        )
    if prepared_launch.artifact_set_id != checked_policy.artifact_set_id:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_prepared_artifact_set")
    if (
        prepared_launch.runtime_manifest.machine_config_sha256
        != checked_policy.machine_config_sha256
    ):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_prepared_machine_config"
        )
    if (
        prepared_launch.runtime_manifest.authority_input_profile_sha256
        != checked_policy.authority_input_profile_sha256
    ):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_prepared_authority_input_profile"
        )
    jail_id = prepared_launch.launch_spec.jail_id
    try:
        request = CgroupCreateRequestV1(
            cgroup_mount=checked_policy.cgroup_mount,
            parent_relative_path=(checked_policy.cgroup_parent_relative_path),
            leaf_name=jail_id,
            limits=checked_policy.cgroup_limits,
            mountinfo_path=checked_policy.mountinfo_path,
            proc_root=checked_policy.proc_root,
            trusted_uid=checked_policy.trusted_uid,
        )
        root_supervisor_plan = SpotV7RootSupervisorPlanV1(
            cgroup_request=request,
            network_namespace_root=(checked_policy.network_namespace_root),
            network_namespace_name=jail_id,
            process_timeout_ns=checked_policy.process_timeout_ns,
            teardown_timeout_ns=checked_policy.teardown_timeout_ns,
        )
        return CandidateBoundSpotV7RootSupervisorPlanV1._from_validated(
            root_supervisor_plan=root_supervisor_plan,
            candidate_id=checked_policy.candidate_id,
            evidence_inventory_root=checked_policy.evidence_inventory_root,
            candidate_manifest_sha256=checked_policy.candidate_manifest_sha256,
            contract_sha256=checked_policy.contract_sha256,
            runtime_manifest_sha256=checked_policy.runtime_manifest_sha256,
            artifact_set_id=checked_policy.artifact_set_id,
            machine_config_sha256=checked_policy.machine_config_sha256,
            authority_input_profile_sha256=(checked_policy.authority_input_profile_sha256),
            firecracker_profile_sha256=checked_policy.firecracker_profile_sha256,
            netns_helper_sha256=bytes.fromhex(checked_policy.netns_helper_sha256),
            seal=_CANDIDATE_BOUND_PLAN_CONSTRUCTION_SEAL_V1,
        )
    except (CgroupV2Reject, SpotV7RootSupervisorRejectV1, TypeError, ValueError) as exc:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_plan_derivation"
        ) from exc


def _revalidate_prepared_policy(
    value: object,
) -> PreparedCandidateBoundSpotV7RootSupervisorPolicyV1:
    if type(value) is not PreparedCandidateBoundSpotV7RootSupervisorPolicyV1:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_prepared_policy")
    policy = value
    if getattr(policy, "_seal", None) is not _CANDIDATE_POLICY_CONSTRUCTION_SEAL_V1:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_prepared_policy")
    try:
        reparsed = prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
            exact_root_supervisor_contract_bytes=policy._exact_contract_bytes,
            exact_release_candidate_bytes=policy._exact_release_candidate_bytes,
            expected_candidate_id=policy._candidate_id,
        )
        identities_match = _policy_identity(policy) == _policy_identity(reparsed)
    except AttributeError as exc:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_prepared_policy"
        ) from exc
    if not identities_match:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_prepared_policy_mutated"
        )
    return reparsed


def _policy_identity(
    value: PreparedCandidateBoundSpotV7RootSupervisorPolicyV1,
) -> tuple[object, ...]:
    return (
        _typed_identity_atom(value._exact_contract_bytes),
        _typed_identity_atom(value._exact_release_candidate_bytes),
        _typed_identity_atom(value._candidate_id),
        _typed_identity_atom(value._candidate_manifest_sha256),
        _typed_identity_atom(value._evidence_inventory_root),
        _typed_identity_atom(value._contract_sha256),
        _typed_identity_atom(value._artifact_set_id),
        _typed_identity_atom(value._machine_config_sha256),
        _typed_identity_atom(value._authority_input_profile_sha256),
        _typed_identity_atom(value._cgroup_mount),
        _typed_identity_atom(value._cgroup_parent_relative_path),
        _typed_identity_atom(value._mountinfo_path),
        _typed_identity_atom(value._proc_root),
        _typed_identity_atom(value._trusted_uid),
        _cgroup_limits_identity(value._cgroup_limits),
        _typed_identity_atom(value._network_namespace_root),
        _typed_identity_atom(value._netns_helper_sha256),
        _typed_identity_atom(value._process_timeout_ns),
        _typed_identity_atom(value._teardown_timeout_ns),
        _typed_identity_atom(value._runtime_manifest_sha256),
        _typed_identity_atom(value._firecracker_profile_sha256),
    )


def _typed_identity_atom(value: object) -> tuple[type[object], object]:
    return (type(value), value)


def _cgroup_limits_identity(value: object) -> tuple[object, ...]:
    if type(value) is not CgroupLimitsV1:
        return (_typed_identity_atom(value),)
    limits = cast(CgroupLimitsV1, value)
    return (
        CgroupLimitsV1,
        _typed_identity_atom(limits.cpu_quota_us),
        _typed_identity_atom(limits.cpu_period_us),
        _typed_identity_atom(limits.cpuset_cpus),
        _typed_identity_atom(limits.cpuset_mems),
        _typed_identity_atom(limits.io_max),
        _typed_identity_atom(limits.memory_high_bytes),
        _typed_identity_atom(limits.memory_max_bytes),
        _typed_identity_atom(limits.memory_swap_max_bytes),
        _typed_identity_atom(limits.pids_max),
    )


def _candidate_bound_plan_identity_sha256(
    *,
    candidate_id: bytes,
    evidence_inventory_root: bytes,
    candidate_manifest_sha256: bytes,
    contract_sha256: bytes,
    runtime_manifest_sha256: bytes,
    artifact_set_id: bytes,
    machine_config_sha256: bytes,
    authority_input_profile_sha256: bytes,
    firecracker_profile_sha256: bytes,
    netns_helper_sha256: bytes,
    jail_id: str,
) -> bytes:
    try:
        jail_id_bytes = jail_id.encode("ascii")
    except (AttributeError, UnicodeEncodeError) as exc:
        raise TypeError("candidate-bound plan jail ID must be ASCII") from exc
    if not jail_id_bytes or len(jail_id_bytes) > 64:
        raise TypeError("candidate-bound plan jail ID is outside the bounded profile")
    return hashlib.sha256(
        _CANDIDATE_BOUND_PLAN_ID_DOMAIN_V1
        + candidate_id
        + evidence_inventory_root
        + candidate_manifest_sha256
        + contract_sha256
        + runtime_manifest_sha256
        + artifact_set_id
        + machine_config_sha256
        + authority_input_profile_sha256
        + firecracker_profile_sha256
        + netns_helper_sha256
        + len(jail_id_bytes).to_bytes(2, "big")
        + jail_id_bytes
    ).digest()


def _decode_exact_contract(raw: object) -> dict[str, Any]:
    if type(raw) is not bytes or not 0 < len(raw) <= MAX_CANDIDATE_CONTRACT_BYTES_V1:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_json")
    _require_bounded_json_depth(raw)
    try:
        document = json.loads(
            raw.decode("ascii"),
            object_pairs_hook=_unique_object,
            parse_float=_reject_json_number,
            parse_constant=_reject_json_number,
        )
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_json") from exc
    if type(document) is not dict or _canonical_document_bytes(document) != raw:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_json")
    return cast(dict[str, Any], document)


def _decode_candidate_document(raw: bytes) -> dict[str, Any]:
    try:
        value = json.loads(raw.decode("ascii"))
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError) as exc:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_release_candidate"
        ) from exc
    if type(value) is not dict:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_release_candidate")
    return cast(dict[str, Any], value)


def _bind_contract_inventory(
    *,
    contract_bytes: bytes,
    candidate_document: dict[str, Any],
) -> None:
    inventory = cast(list[dict[str, object]], candidate_document["evidence_inventory"])
    rows = [row for row in inventory if row["role"] == "root_supervisor_contract"]
    if len(rows) != 1:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_contract_inventory")
    row = rows[0]
    observed_digest = hashlib.sha256(contract_bytes).digest()
    if (
        _digest_hex(
            row["artifact_sha256"],
            "candidate_policy_contract_inventory_digest",
        )
        != observed_digest
    ):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_contract_inventory_digest"
        )
    if type(row["size_bytes"]) is not int or row["size_bytes"] != len(contract_bytes):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(
            "candidate_policy_contract_inventory_size"
        )


def _parse_contract_fields(document: dict[str, Any]) -> _ParsedCandidateContractV1:
    _exact_fields(document, _DOCUMENT_FIELDS_V1, "candidate_policy_fields")
    if document["schema"] != ROOT_SUPERVISOR_CANDIDATE_CONTRACT_SCHEMA_V1:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_schema")
    if document["status"] != ROOT_SUPERVISOR_CANDIDATE_CONTRACT_STATUS_V1:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_status")
    if type(document["format_flags"]) is not int or document["format_flags"] != 1:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_format_flags")
    if type(document["reserved_u32"]) is not int or document["reserved_u32"] != 0:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_reserved")
    _validate_authority(document["authority"])
    if document["non_claims"] != list(CANDIDATE_POLICY_NON_CLAIMS_V1):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_non_claims")
    bindings = _mapping(document["bindings"], _BINDING_FIELDS_V1, "candidate_policy_bindings")
    cgroup = _mapping(document["cgroup"], _CGROUP_FIELDS_V1, "candidate_policy_cgroup")
    network = _mapping(
        document["network_namespace"],
        _NETWORK_NAMESPACE_FIELDS_V1,
        "candidate_policy_network_namespace",
    )
    timeouts = _mapping(document["timeouts"], _TIMEOUT_FIELDS_V1, "candidate_policy_timeouts")
    return _ParsedCandidateContractV1(
        cgroup_mount=_path(cgroup["cgroup_mount"], "candidate_policy_cgroup_path"),
        cgroup_parent_relative_path=_parent_path(cgroup["parent_relative_path"]),
        mountinfo_path=_path(cgroup["mountinfo_path"], "candidate_policy_cgroup_path"),
        proc_root=_path(cgroup["proc_root"], "candidate_policy_cgroup_path"),
        trusted_uid=_trusted_uid(cgroup["trusted_uid"]),
        cgroup_limits=_limits(cgroup["limits"]),
        network_namespace_root=_path(
            network["root"],
            "candidate_policy_network_namespace",
        ),
        netns_helper_sha256=_digest_hex(
            network["helper_sha256"],
            "candidate_policy_netns_helper",
        ).hex(),
        process_timeout_ns=_timeout(
            timeouts["process_timeout_ns"],
            maximum=300_000_000_000,
            code="candidate_policy_process_timeout",
        ),
        teardown_timeout_ns=_timeout(
            timeouts["teardown_timeout_ns"],
            maximum=30_000_000_000,
            code="candidate_policy_teardown_timeout",
        ),
        runtime_manifest_sha256=_digest_hex(
            bindings["runtime_manifest_sha256"],
            "candidate_policy_runtime_manifest_binding",
        ),
        firecracker_profile_sha256=_digest_hex(
            bindings["firecracker_profile_sha256"],
            "candidate_policy_firecracker_profile_binding",
        ),
    )


def _limits(value: object) -> CgroupLimitsV1:
    fields = _mapping(value, _LIMIT_FIELDS_V1, "candidate_policy_cgroup_limits")
    try:
        return CgroupLimitsV1(
            cpu_quota_us=fields["cpu_quota_us"],
            cpu_period_us=fields["cpu_period_us"],
            cpuset_cpus=fields["cpuset_cpus"],
            cpuset_mems=fields["cpuset_mems"],
            io_max=fields["io_max"],
            memory_high_bytes=fields["memory_high_bytes"],
            memory_max_bytes=fields["memory_max_bytes"],
            memory_swap_max_bytes=fields["memory_swap_max_bytes"],
            pids_max=fields["pids_max"],
        )
    except (CgroupV2Reject, TypeError, ValueError) as exc:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_cgroup_limits") from exc


def _parent_path(value: object) -> str:
    if type(value) is not str:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_cgroup_parent")
    try:
        relative_components(value)
    except CgroupV2Reject as exc:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_cgroup_parent") from exc
    return value


def _trusted_uid(value: object) -> int:
    if type(value) is not int or value != 0:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_trusted_uid")
    return value


def _path(value: object, code: str) -> Path:
    if type(value) is not str:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(code)
    path = Path(value)
    if path.as_posix() != value or not is_canonical_absolute_path_v1(path):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(code)
    return path


def _timeout(value: object, *, maximum: int, code: str) -> int:
    if type(value) is not int or not 1_000_000 <= value <= maximum:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(code)
    return value


def _digest_hex(value: object, code: str) -> bytes:
    if type(value) is not str or len(value) != 64 or value != value.lower():
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(code)
    try:
        raw = bytes.fromhex(value)
    except ValueError as exc:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(code) from exc
    if len(raw) != 32 or not any(raw):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(code)
    return raw


def _mapping(value: object, fields: set[str], code: str) -> dict[str, Any]:
    _exact_fields(value, fields, code)
    return cast(dict[str, Any], value)


def _exact_fields(value: object, fields: set[str], code: str) -> None:
    if type(value) is not dict or set(value) != fields:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1(code)


def _validate_authority(value: object) -> None:
    if type(value) is not dict or set(value) != set(CANDIDATE_POLICY_AUTHORITY_FIELDS_V1):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_authority")
    authority = cast(dict[str, object], value)
    if any(type(item) is not bool or item is not False for item in authority.values()):
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_authority")


def _canonical_document_bytes(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True) + "\n"
    ).encode("ascii")


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    output: dict[str, object] = {}
    for key, value in pairs:
        if key in output:
            raise ValueError("duplicate key")
        output[key] = value
    return output


def _reject_json_number(_value: str) -> NoReturn:
    raise ValueError("non-integer JSON number")


def _require_bounded_json_depth(raw: bytes) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in raw:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                in_string = False
            continue
        if byte == 0x22:
            in_string = True
        elif byte in {0x5B, 0x7B}:
            depth += 1
            if depth > MAX_CANDIDATE_CONTRACT_JSON_DEPTH_V1:
                raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_depth")
        elif byte in {0x5D, 0x7D}:
            depth -= 1
            if depth < 0:
                raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_json")
    if depth != 0 or in_string or escaped:
        raise SpotV7RootSupervisorCandidatePolicyRejectV1("candidate_policy_json")


__all__ = [
    "CANDIDATE_POLICY_AUTHORITY_FIELDS_V1",
    "CANDIDATE_POLICY_NON_CLAIMS_V1",
    "CandidateBoundSpotV7RootSupervisorPlanV1",
    "MAX_CANDIDATE_CONTRACT_BYTES_V1",
    "MAX_CANDIDATE_CONTRACT_JSON_DEPTH_V1",
    "PreparedCandidateBoundSpotV7RootSupervisorPolicyV1",
    "ROOT_SUPERVISOR_CANDIDATE_CONTRACT_SCHEMA_V1",
    "ROOT_SUPERVISOR_CANDIDATE_CONTRACT_STATUS_V1",
    "SpotV7RootSupervisorCandidatePolicyRejectV1",
    "derive_candidate_bound_spot_v7_root_supervisor_plan_v1",
    "prepare_candidate_bound_spot_v7_root_supervisor_policy_v1",
]
