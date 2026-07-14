"""Fail-closed future Firecracker-to-Spot-V7 authority boundary.

The current jailed-runner implementation does not yet own immutable staged
artifacts or validate the exact output image and V7 payload inside one trusted
lifecycle. The authority-false execution-binding detector closes the exact data
join and records the remaining governed-runner capability blocker. Therefore
this module exposes no mint path. It defines the sealed types and exact
runtime-to-store missing-condition error that the future governed runner must
close. Durable retries and exact-once consumption belong to the atomic store
transaction. Raw bytes, report dictionaries, Docker results, and caller
booleans remain data.
"""

from __future__ import annotations

from enum import Enum
from typing import Final, NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _SpotV7SettlementCandidateInputV1,
    _validate_candidate,
)
from src.integration._zrpf_spot_v7_firecracker_output import (
    _BoundCommittedSpotV7CandidateV1,
    _revalidate_bound_spot_v7_candidate_v1,
)

__all__ = [
    "SPOT_V7_FIRECRACKER_AUTHORITY_MISSING_CONDITIONS_V1",
    "SpotV7FirecrackerAuthorityMissingConditionV1",
    "SpotV7FirecrackerAuthorityUnavailableV1",
]


class SpotV7FirecrackerAuthorityMissingConditionV1(Enum):
    """Exact blockers for the governed Firecracker runtime-to-store seam.

    Operational DA, finality, consensus, release governance, and application
    settlement promotion remain separate gates. This enum is not the complete
    ZRPF production frontier.
    """

    FINAL_V6_CHILD_IMAGE_ID = "final_v6_child_image_id_unmaterialized"
    FINAL_V7_IMAGE_ID = "final_v7_image_id_unmaterialized"
    CURRENT_V7_RECEIPT_EVIDENCE = (
        "current_v7_receipt_and_seal_mutation_evidence_missing"
    )
    GOVERNED_RELEASE_BINDING = (
        "governed_v7_release_manifest_and_revocation_binding_missing"
    )
    ROOT_OWNED_IMMUTABLE_STAGING = "root_owned_immutable_artifact_staging_missing"
    EXACT_RUNTIME_ARTIFACT_SET = "exact_runtime_artifact_set_validation_missing"
    EXACT_REQUEST_OUTPUT_BINDING = "exact_request_output_device_binding_missing"
    LIVE_PRIVILEGED_JAILER = "live_privileged_jailer_execution_missing"
    LIVE_CGROUP_LIFECYCLE = (
        "live_cgroup_limits_membership_and_teardown_evidence_missing"
    )
    LIVE_EXCLUSIVE_NETWORK_NAMESPACE = (
        "live_exclusive_network_namespace_evidence_missing"
    )
    GOVERNED_RUNNER_RESULT_CAPABILITY = (
        "governed_live_jailed_execution_result_capability_missing"
    )
    EXACT_EXECUTION_RECORD_BINDING = (
        "canonical_execution_record_and_provenance_binding_missing"
    )
    EXACT_V7_PAYLOAD_BINDING = (
        "exact_firecracker_output_and_v7_payload_binding_missing"
    )
    AUTHORITY_CAPABLE_STORE_SCHEMA = "authority_capable_atomic_store_schema_missing"


SPOT_V7_FIRECRACKER_AUTHORITY_MISSING_CONDITIONS_V1: Final = tuple(
    SpotV7FirecrackerAuthorityMissingConditionV1
)


class SpotV7FirecrackerAuthorityUnavailableV1(RuntimeError):
    """Stable failure while the governed runner-to-store chain is incomplete."""

    code: Final = "SPOT_V7_FIRECRACKER_AUTHORITY_UNAVAILABLE"

    def __init__(self) -> None:
        self.missing_conditions = (
            SPOT_V7_FIRECRACKER_AUTHORITY_MISSING_CONDITIONS_V1
        )
        detail = ",".join(condition.value for condition in self.missing_conditions)
        super().__init__(f"{self.code}: {detail}")


class _GovernedRuntimeSealV1:
    __slots__ = ()


class _GovernedBinderSealV1:
    __slots__ = ()


_GOVERNED_RUNTIME_SEAL_V1 = _GovernedRuntimeSealV1()
_GOVERNED_BINDER_SEAL_V1 = _GovernedBinderSealV1()


@final
class _GovernedJailedFirecrackerExecutionV1:
    """Future runner-owned proof of one exact, fully checked jailed execution.

    There is deliberately no mint function while any condition in
    ``SPOT_V7_FIRECRACKER_AUTHORITY_MISSING_CONDITIONS_V1`` remains open.
    The future sole mint site must decode and bind the exact committed output
    inside the same checked jailed lifecycle. A later binder receives no
    independent candidate argument, preventing an execution for run A from
    authorizing candidate B. Observation dictionaries and committed-output
    bytes cannot construct this type.
    """

    __slots__ = ("_bound_output", "_seal")

    _bound_output: _BoundCommittedSpotV7CandidateV1
    _seal: _GovernedRuntimeSealV1

    def __init__(
        self,
        bound_output: _BoundCommittedSpotV7CandidateV1,
        *,
        seal: _GovernedRuntimeSealV1,
    ) -> None:
        if seal is not _GOVERNED_RUNTIME_SEAL_V1:
            raise TypeError(
                "governed jailed Firecracker execution requires the module-private "
                "governed runtime seal"
            )
        if type(bound_output) is not _BoundCommittedSpotV7CandidateV1:
            raise TypeError("bound_output must be exact _BoundCommittedSpotV7CandidateV1")
        _revalidate_bound_spot_v7_candidate_v1(bound_output)
        object.__setattr__(self, "_bound_output", bound_output)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("_GovernedJailedFirecrackerExecutionV1 cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("governed jailed Firecracker execution cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("governed jailed Firecracker execution cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("governed jailed Firecracker execution cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("governed jailed Firecracker execution cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("governed jailed Firecracker execution cannot be serialized")

    def _has_private_runtime_seal(self) -> bool:
        return getattr(self, "_seal", None) is _GOVERNED_RUNTIME_SEAL_V1

    def _candidate_for_binder(self) -> _SpotV7SettlementCandidateInputV1:
        if not self._has_private_runtime_seal():
            raise TypeError("runtime execution lacks the module-private governed runtime seal")
        bound_output = getattr(self, "_bound_output", None)
        if type(bound_output) is not _BoundCommittedSpotV7CandidateV1:
            raise TypeError("runtime execution lacks exact committed Spot V7 output binding")
        candidate = _revalidate_bound_spot_v7_candidate_v1(bound_output)
        _validate_candidate(candidate)
        return candidate


@final
class _GovernedFirecrackerSpotV7SettlementV1:
    """Future one-shot store capability bound to one validated V7 candidate."""

    __slots__ = ("_candidate", "_runtime_execution", "_seal")

    _candidate: _SpotV7SettlementCandidateInputV1
    _runtime_execution: _GovernedJailedFirecrackerExecutionV1
    _seal: _GovernedBinderSealV1

    def __init__(
        self,
        *,
        runtime_execution: _GovernedJailedFirecrackerExecutionV1,
        seal: _GovernedBinderSealV1,
    ) -> None:
        if seal is not _GOVERNED_BINDER_SEAL_V1:
            raise TypeError(
                "governed Firecracker Spot V7 capability requires the module-private "
                "governed binder seal"
            )
        if (
            type(runtime_execution) is not _GovernedJailedFirecrackerExecutionV1
            or not runtime_execution._has_private_runtime_seal()
        ):
            raise TypeError("runtime_execution must be a governed jailed Firecracker execution")
        candidate_input = runtime_execution._candidate_for_binder()
        _validate_candidate(candidate_input)
        object.__setattr__(self, "_candidate", candidate_input)
        object.__setattr__(self, "_runtime_execution", runtime_execution)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("_GovernedFirecrackerSpotV7SettlementV1 cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("governed Firecracker Spot V7 capability cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("governed Firecracker Spot V7 capability cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("governed Firecracker Spot V7 capability cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("governed Firecracker Spot V7 capability cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("governed Firecracker Spot V7 capability cannot be serialized")

    def _has_private_binder_seal(self) -> bool:
        return getattr(self, "_seal", None) is _GOVERNED_BINDER_SEAL_V1

    def _candidate_for_atomic_store(self) -> _SpotV7SettlementCandidateInputV1:
        if not self._has_private_binder_seal():
            raise TypeError("capability lacks the module-private governed binder seal")
        _validate_candidate(self._candidate)
        return self._candidate


def _require_governed_firecracker_spot_v7_authority_available_v1() -> None:
    """Fail closed until one live runner closes every enumerated condition."""

    raise SpotV7FirecrackerAuthorityUnavailableV1()


def _bind_governed_firecracker_spot_v7_settlement_v1(
    *,
    runtime_execution: object,
) -> None:
    """Future binder entrypoint; it cannot mint while the authority lane is open."""

    if (
        type(runtime_execution) is not _GovernedJailedFirecrackerExecutionV1
        or not runtime_execution._has_private_runtime_seal()
    ):
        raise TypeError("runtime_execution must be a governed jailed Firecracker execution")
    runtime_execution._candidate_for_binder()
    _require_governed_firecracker_spot_v7_authority_available_v1()
