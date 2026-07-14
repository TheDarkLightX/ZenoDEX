"""Fail-closed Spot V7 receipt, DA, and finality operational gate.

The Spot V7 Firecracker capability authenticates one exact proof result. The
proof-neutral ``full_blob_da_v1`` and ``checkpoint_finality_v2`` primitives do
not authenticate policy provenance or external finality. Authority-false
combined persistence and cursor mechanics now exist in a separate test-only
lane. This module defines the production join and exposes no production mint
path while governed policy and finality adapters remain absent.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import Enum
from typing import Final, NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _GovernedFirecrackerSpotV7SettlementV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    MAX_U64,
    _hash_bytes,
    _require_uint,
)


class SpotV7OperationalCommitMissingConditionV1(Enum):
    """Unclosed conditions between a V7 receipt and economic commit."""

    GOVERNED_V7_SETTLEMENT_CAPABILITY = (
        "governed_v7_receipt_and_firecracker_capability_unavailable"
    )
    GOVERNED_OPERATIONAL_POLICY = (
        "governed_da_and_finality_policy_provenance_unavailable"
    )
    AUTHENTICATED_EXTERNAL_FINALITY = (
        "protocol_specific_external_finality_authentication_unavailable"
    )
    EXACT_CHECKPOINT_FINALITY_V2_CHECK = (
        "exact_checkpoint_finality_v2_policy_result_adapter_unavailable"
    )


SPOT_V7_OPERATIONAL_COMMIT_MISSING_CONDITIONS_V1: Final = tuple(
    SpotV7OperationalCommitMissingConditionV1
)


class SpotV7OperationalCommitAuthorityUnavailableV1(RuntimeError):
    """Stable reject while no combined operational commit authority exists."""

    code: Final = "SPOT_V7_OPERATIONAL_COMMIT_AUTHORITY_UNAVAILABLE"

    def __init__(self) -> None:
        self.missing_conditions = SPOT_V7_OPERATIONAL_COMMIT_MISSING_CONDITIONS_V1
        detail = ",".join(condition.value for condition in self.missing_conditions)
        RuntimeError.__init__(self, f"{self.code}: {detail}")


class SpotV7OperationalGateBindingErrorV1(ValueError):
    """Typed cross-profile binding failure before persistence is opened."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_OPERATIONAL_GATE_BINDING_REJECTED: {code}")


@dataclass(frozen=True, slots=True)
class _GovernedOperationalPolicyProjectionV1:
    application_id: str
    chain_or_domain_id: str
    full_blob_da_policy_root: str
    checkpoint_finality_policy_root: str

    def __post_init__(self) -> None:
        _validate_hash_fields("operational policy", self)


@dataclass(frozen=True, slots=True)
class _GovernedFullBlobPolicyProjectionV1:
    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    certificate_root: str
    data_root: str
    policy_root: str
    exact_blob_sha256: str
    checked_epoch: int
    retention_through_epoch: int

    def __post_init__(self) -> None:
        _validate_hash_fields(
            "full-blob result",
            self,
            excluded=("epoch_id", "checked_epoch", "retention_through_epoch"),
        )
        _validate_u64_fields(
            "full-blob result",
            self,
            ("epoch_id", "checked_epoch", "retention_through_epoch"),
        )
        if self.checked_epoch < self.epoch_id:
            raise ValueError("full-blob checked epoch precedes certificate epoch")
        if self.retention_through_epoch < self.checked_epoch:
            raise ValueError("full-blob retention ends before checked epoch")


@dataclass(frozen=True, slots=True)
class _AuthenticatedCheckpointFinalityProjectionV2:
    application_id: str
    chain_or_domain_id: str
    epoch_id: int
    proof_journal_hash: str
    post_state_root: str
    policy_root: str
    certificate_root: str
    finality_evidence_root: str
    prior_application_checkpoint_sequence: int
    prior_application_checkpoint_hash: str
    next_application_checkpoint_sequence: int
    next_application_checkpoint_hash: str

    def __post_init__(self) -> None:
        integer_fields = (
            "epoch_id",
            "prior_application_checkpoint_sequence",
            "next_application_checkpoint_sequence",
        )
        _validate_hash_fields("finality result", self, excluded=integer_fields)
        _validate_u64_fields("finality result", self, integer_fields)
        expected_next = self.prior_application_checkpoint_sequence + 1
        if (
            expected_next > MAX_U64
            or self.next_application_checkpoint_sequence != expected_next
        ):
            raise ValueError("checkpoint finality cursor is not an exact successor")


class _GovernedOperationalPolicySealV1:
    __slots__ = ()


class _GovernedFullBlobPolicySealV1:
    __slots__ = ()


class _AuthenticatedCheckpointFinalitySealV2:
    __slots__ = ()


class _AtomicEconomicCommitSealV1:
    __slots__ = ()


_GOVERNED_OPERATIONAL_POLICY_SEAL_V1 = _GovernedOperationalPolicySealV1()
_GOVERNED_FULL_BLOB_POLICY_SEAL_V1 = _GovernedFullBlobPolicySealV1()
_AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V2 = (
    _AuthenticatedCheckpointFinalitySealV2()
)
_ATOMIC_ECONOMIC_COMMIT_SEAL_V1 = _AtomicEconomicCommitSealV1()


class _NonTransferableOperationalCapabilityV1:
    __slots__ = ()

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("Spot V7 operational capability cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("Spot V7 operational capability cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("Spot V7 operational capability cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("Spot V7 operational capability cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("Spot V7 operational capability cannot be serialized")


@final
class _GovernedSpotV7OperationalPolicyV1(_NonTransferableOperationalCapabilityV1):
    """Future release-owned DA/finality policy identity; currently unminted."""

    __slots__ = ("_projection", "_seal")

    _projection: _GovernedOperationalPolicyProjectionV1
    _seal: _GovernedOperationalPolicySealV1

    def __init__(
        self,
        projection: _GovernedOperationalPolicyProjectionV1,
        *,
        seal: _GovernedOperationalPolicySealV1,
    ) -> None:
        if type(projection) is not _GovernedOperationalPolicyProjectionV1:
            raise TypeError("operational policy projection has the wrong type")
        if seal is not _GOVERNED_OPERATIONAL_POLICY_SEAL_V1:
            raise TypeError("operational policy requires the module-private governed seal")
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _GOVERNED_OPERATIONAL_POLICY_SEAL_V1


@final
class _GovernedLocalFullBlobPolicySatisfactionV1(
    _NonTransferableOperationalCapabilityV1
):
    """Future exact governed full-blob check and persistence plan."""

    __slots__ = ("_projection", "_seal")

    _projection: _GovernedFullBlobPolicyProjectionV1
    _seal: _GovernedFullBlobPolicySealV1

    def __init__(
        self,
        projection: _GovernedFullBlobPolicyProjectionV1,
        *,
        seal: _GovernedFullBlobPolicySealV1,
    ) -> None:
        if type(projection) is not _GovernedFullBlobPolicyProjectionV1:
            raise TypeError("full-blob policy projection has the wrong type")
        if seal is not _GOVERNED_FULL_BLOB_POLICY_SEAL_V1:
            raise TypeError("full-blob result requires the module-private governed seal")
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _GOVERNED_FULL_BLOB_POLICY_SEAL_V1


@final
class _AuthenticatedCheckpointFinalityTransitionV2(
    _NonTransferableOperationalCapabilityV1
):
    """Future externally authenticated and exact V2 checked transition."""

    __slots__ = ("_projection", "_seal")

    _projection: _AuthenticatedCheckpointFinalityProjectionV2
    _seal: _AuthenticatedCheckpointFinalitySealV2

    def __init__(
        self,
        projection: _AuthenticatedCheckpointFinalityProjectionV2,
        *,
        seal: _AuthenticatedCheckpointFinalitySealV2,
    ) -> None:
        if type(projection) is not _AuthenticatedCheckpointFinalityProjectionV2:
            raise TypeError("checkpoint-finality projection has the wrong type")
        if seal is not _AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V2:
            raise TypeError("finality result requires the module-private authenticated seal")
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V2


@final
class _SpotV7AtomicEconomicCommitCapabilityV1(
    _NonTransferableOperationalCapabilityV1
):
    """Reserved authority type; there is deliberately no current mint path."""

    __slots__ = ("_seal",)

    _seal: _AtomicEconomicCommitSealV1

    def __init__(self, *, seal: _AtomicEconomicCommitSealV1) -> None:
        if seal is not _ATOMIC_ECONOMIC_COMMIT_SEAL_V1:
            raise TypeError("atomic economic commit requires the module-private seal")
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _ATOMIC_ECONOMIC_COMMIT_SEAL_V1


def _validate_spot_v7_operational_gate_inputs_v1(
    *,
    settlement: object,
    policy: object,
    data_availability: object,
    finality: object,
) -> _SpotV7SettlementCandidateInputV1:
    """Validate exact prerequisite types and bind shared transition facts."""

    settlement_value = _require_settlement_capability(settlement)
    policy_value = _require_operational_policy(policy)
    da_value = _require_full_blob_satisfaction(data_availability)
    finality_value = _require_authenticated_finality(finality)
    candidate = settlement_value._candidate_for_atomic_store()
    _require_policy_binding(candidate, policy_value._projection)
    _require_full_blob_binding(candidate, policy_value._projection, da_value._projection)
    _require_finality_binding(candidate, policy_value._projection, finality_value._projection)
    return candidate


def _bind_spot_v7_operational_commit_capability_v1(
    *,
    settlement: object,
    policy: object,
    data_availability: object,
    finality: object,
) -> None:
    """Validate the join and fail closed until the atomic sink exists."""

    _validate_spot_v7_operational_gate_inputs_v1(
        settlement=settlement,
        policy=policy,
        data_availability=data_availability,
        finality=finality,
    )
    _require_spot_v7_operational_commit_authority_available_v1()


def _require_spot_v7_operational_commit_authority_available_v1() -> NoReturn:
    raise SpotV7OperationalCommitAuthorityUnavailableV1()


def _require_settlement_capability(
    value: object,
) -> _GovernedFirecrackerSpotV7SettlementV1:
    if (
        not isinstance(value, _GovernedFirecrackerSpotV7SettlementV1)
        or type(value) is not _GovernedFirecrackerSpotV7SettlementV1
    ):
        raise TypeError("operational gate requires governed Spot V7 settlement facts")
    if not value._has_private_binder_seal():
        raise TypeError("operational gate requires governed Spot V7 settlement facts")
    return value


def _require_operational_policy(value: object) -> _GovernedSpotV7OperationalPolicyV1:
    if type(value) is not _GovernedSpotV7OperationalPolicyV1:
        raise TypeError("operational gate requires the governed DA/finality policy")
    if not value._has_private_seal():
        raise TypeError("operational gate requires the governed DA/finality policy")
    return value


def _require_full_blob_satisfaction(
    value: object,
) -> _GovernedLocalFullBlobPolicySatisfactionV1:
    if type(value) is not _GovernedLocalFullBlobPolicySatisfactionV1:
        raise TypeError("operational gate requires exact governed full-blob policy evidence")
    if not value._has_private_seal():
        raise TypeError("operational gate requires exact governed full-blob policy evidence")
    return value


def _require_authenticated_finality(
    value: object,
) -> _AuthenticatedCheckpointFinalityTransitionV2:
    if type(value) is not _AuthenticatedCheckpointFinalityTransitionV2:
        raise TypeError("operational gate requires authenticated checkpoint finality evidence")
    if not value._has_private_seal():
        raise TypeError("operational gate requires authenticated checkpoint finality evidence")
    return value


def _require_policy_binding(
    candidate: _SpotV7SettlementCandidateInputV1,
    policy: _GovernedOperationalPolicyProjectionV1,
) -> None:
    _require_checks(
        (
            (policy.application_id == candidate.application_id, "policy_application"),
            (policy.chain_or_domain_id == candidate.chain_or_domain_id, "policy_domain"),
        )
    )


def _require_full_blob_binding(
    candidate: _SpotV7SettlementCandidateInputV1,
    policy: _GovernedOperationalPolicyProjectionV1,
    data_availability: _GovernedFullBlobPolicyProjectionV1,
) -> None:
    _require_checks(
        (
            (data_availability.application_id == candidate.application_id, "da_application"),
            (
                data_availability.chain_or_domain_id == candidate.chain_or_domain_id,
                "da_domain",
            ),
            (data_availability.epoch_id == candidate.epoch_id, "da_epoch"),
            (
                data_availability.certificate_root
                == candidate.data_availability_certificate_root,
                "da_certificate_root",
            ),
            (data_availability.data_root == candidate.data_root, "da_data_root"),
            (
                data_availability.policy_root == policy.full_blob_da_policy_root,
                "da_policy_root",
            ),
        )
    )


def _require_finality_binding(
    candidate: _SpotV7SettlementCandidateInputV1,
    policy: _GovernedOperationalPolicyProjectionV1,
    finality: _AuthenticatedCheckpointFinalityProjectionV2,
) -> None:
    _require_checks(
        (
            (finality.application_id == candidate.application_id, "finality_application"),
            (
                finality.chain_or_domain_id == candidate.chain_or_domain_id,
                "finality_domain",
            ),
            (finality.epoch_id == candidate.epoch_id, "finality_epoch"),
            (
                finality.proof_journal_hash == _journal_sha256(candidate),
                "finality_proof_journal",
            ),
            (finality.post_state_root == candidate.post_state_root, "finality_post_state"),
            (
                finality.policy_root == policy.checkpoint_finality_policy_root,
                "finality_policy_root",
            ),
        )
    )


def _journal_sha256(candidate: _SpotV7SettlementCandidateInputV1) -> str:
    return "0x" + hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest()


def _require_checks(checks: tuple[tuple[bool, str], ...]) -> None:
    for accepted, code in checks:
        if not accepted:
            raise SpotV7OperationalGateBindingErrorV1(code)


def _validate_hash_fields(
    prefix: str,
    projection: (
        _GovernedOperationalPolicyProjectionV1
        | _GovernedFullBlobPolicyProjectionV1
        | _AuthenticatedCheckpointFinalityProjectionV2
    ),
    *,
    excluded: tuple[str, ...] = (),
) -> None:
    for name in projection.__dataclass_fields__:
        if name not in excluded:
            _hash_bytes(getattr(projection, name), name=f"Spot V7 {prefix} {name}")


def _validate_u64_fields(prefix: str, projection: object, fields: tuple[str, ...]) -> None:
    for name in fields:
        _require_uint(
            getattr(projection, name),
            name=f"Spot V7 {prefix} {name}",
            maximum=MAX_U64,
        )


__all__ = [
    "SPOT_V7_OPERATIONAL_COMMIT_MISSING_CONDITIONS_V1",
    "SpotV7OperationalCommitAuthorityUnavailableV1",
    "SpotV7OperationalCommitMissingConditionV1",
    "SpotV7OperationalGateBindingErrorV1",
]
