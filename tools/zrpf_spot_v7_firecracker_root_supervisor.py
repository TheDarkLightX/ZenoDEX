"""Authority-false root-supervisor contract for one Spot V7 microVM run.

The imperative shell spends the descriptor-sourced launch once, owns a fresh
cgroup and network namespace through a narrow OS port, invokes the prepared
Jailer lifecycle, independently checks the exact request-bound output, and
tears down every control.  An injected port is useful for deterministic tests;
its observations cannot mint runtime, settlement, release, or production
authority.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, NoReturn, Protocol, SupportsIndex, final

from tools._zrpf_spot_v7_firecracker_descriptor_handoff import (
    _LIFECYCLE_HANDOFF_REQUEST_SEAL_V1,
    _DescriptorBoundSpotV7LifecycleHandoffV1,
    _PreparedDescriptorBoundSpotV7LaunchV1,
)
from tools.zrpf_spot_v7_firecracker_descriptor_staging import (
    SpotV7DescriptorStagingRejectV1,
)
from tools.zrpf_spot_v7_firecracker_jailer_lifecycle import (
    CompletedPreparedSpotV7JailerRunV1,
)
from tools.zrpf_spot_v7_firecracker_runtime_protocol import (
    SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1,
    SpotV7FirecrackerProtocolRejectV1,
    decode_exact_request_v1,
    validate_exact_committed_output_v1,
)
from tools.zrpf_v3_firecracker_cgroup_contract import (
    CgroupV2Reject,
    relative_components,
    require_leaf_name,
)
from tools.zrpf_v3_firecracker_cgroup_v2 import (
    CgroupCreateRequestV1,
    is_canonical_absolute_path_v1,
    snapshot_cgroup_create_request_v1,
)

ROOT_SUPERVISOR_LIVE_EXECUTION_VERIFIED_V1 = False
ROOT_SUPERVISOR_LIVE_OWNERSHIP_VERIFIED_V1 = False
ROOT_SUPERVISOR_GOVERNED_CGROUP_PARENT_VERIFIED_V1 = False
ROOT_SUPERVISOR_GOVERNED_CGROUP_RESOURCE_POLICY_VERIFIED_V1 = False
ROOT_SUPERVISOR_GOVERNED_NETWORK_NAMESPACE_ROOT_VERIFIED_V1 = False
ROOT_SUPERVISOR_RUNTIME_AUTHORITY_V1 = False
ROOT_SUPERVISOR_SETTLEMENT_AUTHORITY_V1 = False
ROOT_SUPERVISOR_RELEASE_AUTHORITY_V1 = False
ROOT_SUPERVISOR_PRODUCTION_AUTHORITY_V1 = False


class SpotV7RootSupervisorRejectV1(RuntimeError):
    """Stable fail-closed reject at the root-owned orchestration boundary."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(code)


@dataclass(frozen=True, slots=True)
class SpotV7RootSupervisorPlanV1:
    """Finite control allocation and timeout contract for one staged run."""

    cgroup_request: CgroupCreateRequestV1
    network_namespace_root: Path
    network_namespace_name: str
    process_timeout_ns: int
    teardown_timeout_ns: int

    def __post_init__(self) -> None:
        if type(self.cgroup_request) is not CgroupCreateRequestV1:
            raise SpotV7RootSupervisorRejectV1("root_supervisor_cgroup_request_invalid")
        try:
            request = snapshot_cgroup_create_request_v1(self.cgroup_request)
        except CgroupV2Reject as exc:
            raise SpotV7RootSupervisorRejectV1("root_supervisor_cgroup_request_invalid") from exc
        object.__setattr__(self, "cgroup_request", request)
        try:
            require_leaf_name(self.network_namespace_name)
            relative_components(self.cgroup_request.parent_relative_path)
        except (TypeError, ValueError, CgroupV2Reject) as exc:
            raise SpotV7RootSupervisorRejectV1("root_supervisor_control_name_invalid") from exc
        if self.network_namespace_name != self.cgroup_request.leaf_name:
            raise SpotV7RootSupervisorRejectV1("root_supervisor_control_name_mismatch")
        if not is_canonical_absolute_path_v1(self.network_namespace_root):
            raise SpotV7RootSupervisorRejectV1("root_supervisor_namespace_root_invalid")
        _require_timeout_ns(
            self.process_timeout_ns,
            maximum=300_000_000_000,
            code="root_supervisor_process_timeout_invalid",
        )
        _require_timeout_ns(
            self.teardown_timeout_ns,
            maximum=30_000_000_000,
            code="root_supervisor_teardown_timeout_invalid",
        )

    @property
    def expected_cgroup_relative_path(self) -> str:
        parts = relative_components(self.cgroup_request.parent_relative_path)
        return "/" + "/".join((*parts, self.cgroup_request.leaf_name))

    @property
    def expected_network_namespace_path(self) -> Path:
        return self.network_namespace_root / self.network_namespace_name


class SpotV7RootSupervisorOsPortV1(Protocol):
    """Narrow imperative-shell effects; successful calls remain non-authority."""

    def create_cgroup_leaf(self, request: CgroupCreateRequestV1) -> object: ...

    def create_network_namespace(
        self,
        *,
        namespace_root: Path,
        namespace_name: str,
        trusted_uid: int,
    ) -> object: ...

    def require_prelaunch_controls(
        self,
        *,
        cgroup: object,
        network_namespace: object,
        expected_cgroup_relative_path: str,
        expected_network_namespace_path: Path,
        expected_trusted_uid: int,
    ) -> None: ...

    def run_exact_prepared_lifecycle(
        self,
        *,
        handoff: _DescriptorBoundSpotV7LifecycleHandoffV1,
        cgroup: object,
        network_namespace: object,
        process_timeout_ns: int,
        exact_request_bytes: bytes,
    ) -> CompletedPreparedSpotV7JailerRunV1: ...

    def terminate_cgroup(self, cgroup: object, *, timeout_ns: int) -> None: ...

    def require_cgroup_absent(self, cgroup: object) -> None: ...

    def require_network_namespace_empty(self, network_namespace: object) -> None: ...

    def destroy_network_namespace(self, network_namespace: object) -> None: ...

    def require_network_namespace_absent(self, network_namespace: object) -> None: ...


class _CompletedSupervisorSealV1:
    __slots__ = ()


_COMPLETED_SUPERVISOR_SEAL_V1 = _CompletedSupervisorSealV1()


@final
class CompletedSpotV7RootSupervisorRunV1:
    """Sealed bounded payload observation; every authority property is false."""

    __slots__ = (
        "_cgroup_relative_path",
        "_finish_observation_sha256",
        "_launch_observation_sha256",
        "_network_namespace_path",
        "_payload_bytes",
        "_payload_sha256",
        "_prepare_observation_sha256",
        "_request_sha256",
        "_seal",
    )

    _cgroup_relative_path: str
    _finish_observation_sha256: bytes
    _launch_observation_sha256: bytes
    _network_namespace_path: Path
    _payload_bytes: bytes
    _payload_sha256: bytes
    _prepare_observation_sha256: bytes
    _request_sha256: bytes
    _seal: _CompletedSupervisorSealV1

    def __init__(
        self,
        *,
        payload_bytes: bytes,
        request_sha256: bytes,
        cgroup_relative_path: str,
        network_namespace_path: Path,
        prepare_observation_sha256: bytes,
        launch_observation_sha256: bytes,
        finish_observation_sha256: bytes,
        seal: _CompletedSupervisorSealV1,
    ) -> None:
        if seal is not _COMPLETED_SUPERVISOR_SEAL_V1:
            raise TypeError("root supervisor result requires the module-private seal")
        if type(payload_bytes) is not bytes or not payload_bytes:
            raise TypeError("root supervisor payload must be nonempty bytes")
        for digest in (
            request_sha256,
            prepare_observation_sha256,
            launch_observation_sha256,
            finish_observation_sha256,
        ):
            if type(digest) is not bytes or len(digest) != 32:
                raise TypeError("root supervisor digest must be exact bytes")
        object.__setattr__(self, "_payload_bytes", payload_bytes)
        object.__setattr__(self, "_payload_sha256", hashlib.sha256(payload_bytes).digest())
        object.__setattr__(self, "_request_sha256", request_sha256)
        object.__setattr__(self, "_cgroup_relative_path", cgroup_relative_path)
        object.__setattr__(self, "_network_namespace_path", network_namespace_path)
        object.__setattr__(self, "_prepare_observation_sha256", prepare_observation_sha256)
        object.__setattr__(self, "_launch_observation_sha256", launch_observation_sha256)
        object.__setattr__(self, "_finish_observation_sha256", finish_observation_sha256)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("root supervisor result cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("root supervisor result cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("root supervisor result cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("root supervisor result cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("root supervisor result cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("root supervisor result cannot be serialized")

    @property
    def payload_bytes(self) -> bytes:
        return self._payload_bytes

    @property
    def payload_sha256(self) -> bytes:
        return self._payload_sha256

    @property
    def request_sha256(self) -> bytes:
        return self._request_sha256

    @property
    def prepare_observation_sha256(self) -> bytes:
        return self._prepare_observation_sha256

    @property
    def launch_observation_sha256(self) -> bytes:
        return self._launch_observation_sha256

    @property
    def finish_observation_sha256(self) -> bytes:
        return self._finish_observation_sha256

    @property
    def cgroup_relative_path(self) -> str:
        return self._cgroup_relative_path

    @property
    def network_namespace_path(self) -> Path:
        return self._network_namespace_path

    @property
    def live_execution_verified(self) -> bool:
        return ROOT_SUPERVISOR_LIVE_EXECUTION_VERIFIED_V1

    @property
    def live_ownership_verified(self) -> bool:
        return ROOT_SUPERVISOR_LIVE_OWNERSHIP_VERIFIED_V1

    @property
    def governed_cgroup_parent_verified(self) -> bool:
        return ROOT_SUPERVISOR_GOVERNED_CGROUP_PARENT_VERIFIED_V1

    @property
    def governed_cgroup_resource_policy_verified(self) -> bool:
        return ROOT_SUPERVISOR_GOVERNED_CGROUP_RESOURCE_POLICY_VERIFIED_V1

    @property
    def governed_network_namespace_root_verified(self) -> bool:
        return ROOT_SUPERVISOR_GOVERNED_NETWORK_NAMESPACE_ROOT_VERIFIED_V1

    @property
    def runtime_authority(self) -> bool:
        return ROOT_SUPERVISOR_RUNTIME_AUTHORITY_V1

    @property
    def settlement_authority(self) -> bool:
        return ROOT_SUPERVISOR_SETTLEMENT_AUTHORITY_V1

    @property
    def release_authority(self) -> bool:
        return ROOT_SUPERVISOR_RELEASE_AUTHORITY_V1

    @property
    def production_authority(self) -> bool:
        return ROOT_SUPERVISOR_PRODUCTION_AUTHORITY_V1


@dataclass(slots=True)
class _RunStateV1:
    handoff: _DescriptorBoundSpotV7LifecycleHandoffV1
    cgroup: object | None = None
    network_namespace: object | None = None
    lifecycle_started: bool = False
    lifecycle_returned: bool = False
    cgroup_absence_verified: bool = False
    namespace_destroy_attempted: bool = False
    namespace_absence_verified: bool = False
    handoff_close_attempted: bool = False


def run_spot_v7_root_supervisor_contract_v1(
    *,
    prepared_launch: _PreparedDescriptorBoundSpotV7LaunchV1,
    plan: SpotV7RootSupervisorPlanV1,
    os_port: SpotV7RootSupervisorOsPortV1,
) -> CompletedSpotV7RootSupervisorRunV1:
    """Spend one prepared launch and enforce the bounded supervisor sequence.

    The OS port owns privileged effects.  The supervisor independently decodes
    the retained request and output.  The returned value stays authority-false
    until a concrete live port, governed release, and fresh proof evidence are
    separately admitted.
    """

    if type(prepared_launch) is not _PreparedDescriptorBoundSpotV7LaunchV1:
        raise TypeError("prepared_launch must be the exact sealed launch")
    if type(plan) is not SpotV7RootSupervisorPlanV1:
        raise TypeError("plan must be exact SpotV7RootSupervisorPlanV1")
    try:
        plan = SpotV7RootSupervisorPlanV1(
            cgroup_request=plan.cgroup_request,
            network_namespace_root=plan.network_namespace_root,
            network_namespace_name=plan.network_namespace_name,
            process_timeout_ns=plan.process_timeout_ns,
            teardown_timeout_ns=plan.teardown_timeout_ns,
        )
    except (CgroupV2Reject, SpotV7RootSupervisorRejectV1) as exc:
        raise SpotV7RootSupervisorRejectV1("root_supervisor_plan_invalid") from exc
    handoff = _take_handoff(prepared_launch)
    state = _RunStateV1(handoff=handoff)
    try:
        return _execute_supervised_run(os_port=os_port, state=state, plan=plan)
    except BaseException as original:
        teardown_error = _cleanup_rejected_run(
            os_port=os_port,
            state=state,
            plan=plan,
        )
        if teardown_error is not None:
            raise SpotV7RootSupervisorRejectV1("root_supervisor_teardown_uncertain") from original
        if isinstance(original, SpotV7RootSupervisorRejectV1):
            raise
        raise _normalize_reject(original) from original


def _execute_supervised_run(
    *,
    os_port: SpotV7RootSupervisorOsPortV1,
    state: _RunStateV1,
    plan: SpotV7RootSupervisorPlanV1,
) -> CompletedSpotV7RootSupervisorRunV1:
    handoff = state.handoff
    request_bytes = handoff._exact_request_bytes_for_supervisor_v1()
    request = decode_exact_request_v1(request_bytes)
    _require_plan_matches_handoff(plan, handoff)
    state.cgroup = os_port.create_cgroup_leaf(plan.cgroup_request)
    state.network_namespace = os_port.create_network_namespace(
        namespace_root=plan.network_namespace_root,
        namespace_name=plan.network_namespace_name,
        trusted_uid=plan.cgroup_request.trusted_uid,
    )
    os_port.require_prelaunch_controls(
        cgroup=state.cgroup,
        network_namespace=state.network_namespace,
        expected_cgroup_relative_path=plan.expected_cgroup_relative_path,
        expected_network_namespace_path=plan.expected_network_namespace_path,
        expected_trusted_uid=plan.cgroup_request.trusted_uid,
    )
    handoff.verify_prelaunch()
    state.lifecycle_started = True
    completed = os_port.run_exact_prepared_lifecycle(
        handoff=handoff,
        cgroup=state.cgroup,
        network_namespace=state.network_namespace,
        process_timeout_ns=plan.process_timeout_ns,
        exact_request_bytes=request_bytes,
    )
    state.lifecycle_returned = True
    _require_exact_completed_lifecycle(completed)
    decoded = validate_exact_committed_output_v1(
        completed.output_device_bytes,
        request,
    )
    _complete_control_teardown(os_port, state, plan=plan)
    state.handoff_close_attempted = True
    handoff._close_after_completed_lifecycle_v1()
    return _new_completed_result(
        decoded.raw_bytes,
        request_bytes=request_bytes,
        plan=plan,
        completed=completed,
    )


def _take_handoff(
    prepared_launch: _PreparedDescriptorBoundSpotV7LaunchV1,
) -> _DescriptorBoundSpotV7LifecycleHandoffV1:
    try:
        return prepared_launch._take_for_lifecycle_v1(_LIFECYCLE_HANDOFF_REQUEST_SEAL_V1)
    except (SpotV7DescriptorStagingRejectV1, TypeError) as exc:
        raise SpotV7RootSupervisorRejectV1("root_supervisor_handoff_rejected") from exc


def _require_plan_matches_handoff(
    plan: SpotV7RootSupervisorPlanV1,
    handoff: _DescriptorBoundSpotV7LifecycleHandoffV1,
) -> None:
    if (
        handoff.launch_spec.jail_id != plan.cgroup_request.leaf_name
        or handoff.launch_spec.jail_id != plan.network_namespace_name
        or handoff.prepared_jail.spec.trusted_uid != plan.cgroup_request.trusted_uid
    ):
        raise SpotV7RootSupervisorRejectV1("root_supervisor_launch_control_binding_mismatch")


def _require_exact_completed_lifecycle(
    completed: CompletedPreparedSpotV7JailerRunV1,
) -> None:
    if (
        type(completed) is not CompletedPreparedSpotV7JailerRunV1
        or type(completed.output_device_bytes) is not bytes
        or len(completed.output_device_bytes) != SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1
        or type(completed.prepare_observation) is not dict
        or type(completed.launch_observation) is not dict
        or type(completed.finish_observation) is not dict
    ):
        raise SpotV7RootSupervisorRejectV1("root_supervisor_lifecycle_result_invalid")


def _complete_control_teardown(
    os_port: SpotV7RootSupervisorOsPortV1,
    state: _RunStateV1,
    *,
    plan: SpotV7RootSupervisorPlanV1,
) -> None:
    if state.cgroup is None or state.network_namespace is None:
        raise SpotV7RootSupervisorRejectV1("root_supervisor_control_allocation_incomplete")
    os_port.terminate_cgroup(
        state.cgroup,
        timeout_ns=plan.teardown_timeout_ns,
    )
    os_port.require_cgroup_absent(state.cgroup)
    state.cgroup_absence_verified = True
    os_port.require_network_namespace_empty(state.network_namespace)
    state.namespace_destroy_attempted = True
    os_port.destroy_network_namespace(state.network_namespace)
    os_port.require_network_namespace_absent(state.network_namespace)
    state.namespace_absence_verified = True


def _cleanup_rejected_run(
    *,
    os_port: SpotV7RootSupervisorOsPortV1,
    state: _RunStateV1,
    plan: SpotV7RootSupervisorPlanV1,
) -> BaseException | None:
    cleanup_error: BaseException | None = None
    if state.cgroup is not None and not state.cgroup_absence_verified:
        try:
            os_port.terminate_cgroup(
                state.cgroup,
                timeout_ns=plan.teardown_timeout_ns,
            )
            os_port.require_cgroup_absent(state.cgroup)
            state.cgroup_absence_verified = True
        except BaseException as exc:
            cleanup_error = exc
    if state.network_namespace is not None and not state.namespace_absence_verified:
        try:
            _finish_network_namespace_teardown(os_port, state)
        except BaseException as exc:
            if cleanup_error is None:
                cleanup_error = exc
    if cleanup_error is not None:
        try:
            state.handoff._quarantine_after_uncertain_lifecycle_v1()
        except BaseException:
            pass
        return cleanup_error
    try:
        if state.handoff_close_attempted:
            return None
        if state.lifecycle_returned:
            state.handoff_close_attempted = True
            state.handoff._close_after_completed_lifecycle_v1()
        elif state.lifecycle_started:
            state.handoff._cleanup_after_forced_teardown_v1()
        else:
            state.handoff.abandon_before_launch()
    except BaseException as exc:
        return exc
    return None


def _finish_network_namespace_teardown(
    os_port: SpotV7RootSupervisorOsPortV1,
    state: _RunStateV1,
) -> None:
    network_namespace = state.network_namespace
    if network_namespace is None:
        raise SpotV7RootSupervisorRejectV1("root_supervisor_namespace_allocation_missing")
    if state.namespace_destroy_attempted:
        try:
            os_port.require_network_namespace_absent(network_namespace)
            state.namespace_absence_verified = True
            return
        except BaseException:
            pass
    os_port.require_network_namespace_empty(network_namespace)
    state.namespace_destroy_attempted = True
    os_port.destroy_network_namespace(network_namespace)
    os_port.require_network_namespace_absent(network_namespace)
    state.namespace_absence_verified = True


def _normalize_reject(original: BaseException) -> SpotV7RootSupervisorRejectV1:
    if isinstance(original, SpotV7RootSupervisorRejectV1):
        return original
    if isinstance(original, SpotV7FirecrackerProtocolRejectV1):
        return SpotV7RootSupervisorRejectV1("root_supervisor_output_rejected")
    if isinstance(original, SpotV7DescriptorStagingRejectV1):
        return SpotV7RootSupervisorRejectV1("root_supervisor_handoff_rejected")
    return SpotV7RootSupervisorRejectV1("root_supervisor_port_failed")


def _new_completed_result(
    payload: bytes,
    *,
    request_bytes: bytes,
    plan: SpotV7RootSupervisorPlanV1,
    completed: CompletedPreparedSpotV7JailerRunV1,
) -> CompletedSpotV7RootSupervisorRunV1:
    return CompletedSpotV7RootSupervisorRunV1(
        payload_bytes=payload,
        request_sha256=hashlib.sha256(request_bytes).digest(),
        cgroup_relative_path=plan.expected_cgroup_relative_path,
        network_namespace_path=plan.expected_network_namespace_path,
        prepare_observation_sha256=_observation_sha256(completed.prepare_observation),
        launch_observation_sha256=_observation_sha256(completed.launch_observation),
        finish_observation_sha256=_observation_sha256(completed.finish_observation),
        seal=_COMPLETED_SUPERVISOR_SEAL_V1,
    )


def _observation_sha256(document: dict[str, Any]) -> bytes:
    try:
        raw = (
            json.dumps(
                document,
                ensure_ascii=True,
                separators=(",", ":"),
                sort_keys=True,
            )
            + "\n"
        ).encode("ascii")
    except (TypeError, UnicodeEncodeError, ValueError) as exc:
        raise SpotV7RootSupervisorRejectV1("root_supervisor_observation_invalid") from exc
    if len(raw) > 1024 * 1024:
        raise SpotV7RootSupervisorRejectV1("root_supervisor_observation_too_large")
    return hashlib.sha256(raw).digest()


def _require_timeout_ns(value: int, *, maximum: int, code: str) -> None:
    if type(value) is not int or not 1_000_000 <= value <= maximum:
        raise SpotV7RootSupervisorRejectV1(code)
