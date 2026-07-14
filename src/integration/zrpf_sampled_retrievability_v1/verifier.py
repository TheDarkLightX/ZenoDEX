"""Fail-closed verifier for bounded BLS-authenticated retrievability samples."""

from __future__ import annotations

import hashlib
from collections.abc import Mapping
from dataclasses import dataclass
from typing import NoReturn, SupportsIndex, final

from .codec import (
    AUTHORITY_CLAIMS_V1,
    SAMPLED_RETRIEVABILITY_EVIDENCE_SCHEMA_V1,
    decode_exact_evidence_document_v1,
)
from .errors import reject as _reject
from .hashing import (
    derive_certificate_root_v1,
    derive_chunk_root_v1,
)
from .model import (
    BeaconCommitmentV1,
    FullBlobRetrievabilityTargetV1,
    SampledRetrievabilityPolicyV1,
    require_root,
    require_u64,
)
from .response_verifier import verify_provider_responses_v1
from .validation import (
    checked_add as _checked_add,
)
from .validation import (
    exact_equal as _exact_equal,
)
from .validation import (
    require_list as _require_list,
)


@dataclass(frozen=True, slots=True)
class _VerifiedProjectionV1:
    checked_epoch: int
    accepted_provider_ids: tuple[str, ...]
    policy_root: str
    certificate_root: str
    beacon_commitment: str
    evidence_sha256: str


class _AuthenticatedEvidenceSealV1:
    __slots__ = ()


_AUTHENTICATED_EVIDENCE_SEAL_V1 = _AuthenticatedEvidenceSealV1()


@final
class _AuthenticatedSampledRetrievabilityEvidenceV1:
    """Process-local result of exact BLS, opening, lifecycle, and quorum checks."""

    __slots__ = ("_exact_evidence_bytes", "_projection", "_seal")

    _exact_evidence_bytes: bytes
    _projection: _VerifiedProjectionV1
    _seal: _AuthenticatedEvidenceSealV1

    def __init__(
        self,
        projection: _VerifiedProjectionV1,
        exact_evidence_bytes: bytes,
        *,
        seal: _AuthenticatedEvidenceSealV1,
    ) -> None:
        if type(projection) is not _VerifiedProjectionV1:
            raise TypeError("authenticated retrievability projection has the wrong type")
        if seal is not _AUTHENTICATED_EVIDENCE_SEAL_V1:
            raise TypeError("authenticated retrievability evidence requires the private seal")
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_exact_evidence_bytes", exact_evidence_bytes)
        object.__setattr__(self, "_seal", seal)

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("authenticated retrievability evidence cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated retrievability evidence cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated retrievability evidence cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated retrievability evidence cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("authenticated retrievability evidence cannot be serialized")

    @property
    def authenticated_sampled_response_scoped_to_checked_epoch(self) -> bool:
        return True

    @property
    def checked_epoch(self) -> int:
        return self._projection.checked_epoch

    @property
    def accepted_provider_ids(self) -> tuple[str, ...]:
        return self._projection.accepted_provider_ids

    @property
    def policy_root(self) -> str:
        return self._projection.policy_root

    @property
    def certificate_root(self) -> str:
        return self._projection.certificate_root

    @property
    def beacon_commitment(self) -> str:
        return self._projection.beacon_commitment

    @property
    def evidence_sha256(self) -> str:
        return self._projection.evidence_sha256

    @property
    def exact_evidence_bytes(self) -> bytes:
        return self._exact_evidence_bytes

    @property
    def continuous_availability_verified(self) -> bool:
        return False

    @property
    def governed_policy_provenance_verified(self) -> bool:
        return False

    @property
    def governed_beacon_provenance_verified(self) -> bool:
        return False

    @property
    def beacon_unpredictability_verified(self) -> bool:
        return False

    @property
    def response_timing_provenance_verified(self) -> bool:
        return False

    @property
    def provider_independence_verified(self) -> bool:
        return False

    @property
    def public_future_availability_verified(self) -> bool:
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


def verify_exact_evidence_v1(
    exact_evidence_bytes: bytes,
    *,
    expected_policy: SampledRetrievabilityPolicyV1,
    expected_target: FullBlobRetrievabilityTargetV1,
    expected_beacon: BeaconCommitmentV1,
    checked_epoch: int,
) -> _AuthenticatedSampledRetrievabilityEvidenceV1:
    """Verify one exact bounded sample under explicit trusted expectations.

    The positive result covers authenticated sampled retrievability only at the
    supplied checked epoch. Policy and beacon governance provenance, continuous
    availability, future public retrieval, settlement, release, and production
    authority remain external and false.
    """

    policy, target, beacon, checked = _validate_expectations(
        expected_policy,
        expected_target,
        expected_beacon,
        checked_epoch,
    )
    _require_expected_policy_and_retention(policy, target, beacon, checked)
    try:
        document = decode_exact_evidence_document_v1(exact_evidence_bytes)
    except (TypeError, ValueError):
        _reject("NONCANONICAL_EVIDENCE", "evidence bytes are not exact canonical V1 JSON")
    _require_top_level_bindings(document, policy, target, beacon, checked)
    chunk_hashes = _require_chunk_hash_vector(document, target)
    responses = _require_list(document.get("responses"), name="evidence responses")
    accepted = verify_provider_responses_v1(
        responses,
        policy=policy,
        target=target,
        beacon=beacon,
        checked_epoch=checked,
        ordered_chunk_hashes=chunk_hashes,
    )
    if len(accepted) < policy.minimum_provider_responses:
        _reject("PROVIDER_QUORUM_NOT_MET", "distinct active provider quorum is below policy")
    projection = _VerifiedProjectionV1(
        checked_epoch=checked,
        accepted_provider_ids=accepted,
        policy_root=policy.policy_root,
        certificate_root=target.certificate_root,
        beacon_commitment=beacon.commitment,
        evidence_sha256=hashlib.sha256(exact_evidence_bytes).hexdigest(),
    )
    return _AuthenticatedSampledRetrievabilityEvidenceV1(
        projection,
        exact_evidence_bytes,
        seal=_AUTHENTICATED_EVIDENCE_SEAL_V1,
    )


def _validate_expectations(
    policy: object,
    target: object,
    beacon: object,
    checked_epoch: object,
) -> tuple[
    SampledRetrievabilityPolicyV1,
    FullBlobRetrievabilityTargetV1,
    BeaconCommitmentV1,
    int,
]:
    if type(policy) is not SampledRetrievabilityPolicyV1:
        raise TypeError("expected_policy must be an exact SampledRetrievabilityPolicyV1")
    if type(target) is not FullBlobRetrievabilityTargetV1:
        raise TypeError("expected_target must be an exact FullBlobRetrievabilityTargetV1")
    if type(beacon) is not BeaconCommitmentV1:
        raise TypeError("expected_beacon must be an exact BeaconCommitmentV1")
    checked = require_u64(checked_epoch, name="checked_epoch")
    return policy, target, beacon, checked


def _require_expected_policy_and_retention(
    policy: SampledRetrievabilityPolicyV1,
    target: FullBlobRetrievabilityTargetV1,
    beacon: BeaconCommitmentV1,
    checked_epoch: int,
) -> None:
    if not policy.is_active_at(checked_epoch):
        _reject("POLICY_NOT_ACTIVE", "retrievability policy is inactive at checked epoch")
    if target.application_id != policy.application_id:
        _reject("POLICY_BINDING_MISMATCH", "policy application does not match full blob")
    if target.chain_or_domain_id != policy.chain_or_domain_id:
        _reject("POLICY_BINDING_MISMATCH", "policy domain does not match full blob")
    if target.storage_policy_hash != policy.storage_policy_hash:
        _reject("POLICY_BINDING_MISMATCH", "storage policy does not match full blob")
    if beacon.source_id != policy.beacon_source_id or (
        beacon.policy_hash != policy.beacon_policy_hash
    ):
        _reject("BEACON_BINDING_MISMATCH", "beacon source or policy mismatch")
    if beacon.beacon_epoch != checked_epoch:
        _reject("BEACON_BINDING_MISMATCH", "beacon epoch must equal checked epoch")
    if checked_epoch < target.epoch_id:
        _reject("RETENTION_INSUFFICIENT", "checked epoch precedes full-blob epoch")
    if derive_certificate_root_v1(target) != target.certificate_root:
        _reject("FULL_BLOB_TARGET_INVALID", "full-blob certificate root is inconsistent")
    deadline = _checked_add(checked_epoch, policy.response_window_epochs, "response deadline")
    initial = _checked_add(
        target.epoch_id,
        policy.minimum_retention_epochs,
        "initial retention",
    )
    remaining = _checked_add(
        checked_epoch,
        policy.minimum_remaining_epochs,
        "remaining retention",
    )
    if target.retention_through_epoch < max(deadline, initial, remaining):
        _reject("RETENTION_INSUFFICIENT", "full-blob retention does not cover the sample")
    active = policy.active_provider_ids_at(checked_epoch)
    if len(active) < policy.minimum_provider_responses:
        _reject("PROVIDER_QUORUM_NOT_MET", "policy has too few active providers")
    if policy.challenge_count > target.chunk_count:
        _reject("CHALLENGE_COUNT_INVALID", "challenge count exceeds full-blob chunks")


def _require_top_level_bindings(
    document: dict[str, object],
    policy: SampledRetrievabilityPolicyV1,
    target: FullBlobRetrievabilityTargetV1,
    beacon: BeaconCommitmentV1,
    checked_epoch: int,
) -> None:
    if document.get("schema") != SAMPLED_RETRIEVABILITY_EVIDENCE_SCHEMA_V1:
        _reject("EVIDENCE_SCHEMA_MISMATCH", "evidence schema is unsupported")
    authority = document.get("authority")
    if not _exact_equal(authority, AUTHORITY_CLAIMS_V1):
        _reject("AUTHORITY_CLAIM_MISMATCH", "evidence authority claims exceed V1 scope")
    if not _exact_equal(document.get("checked_epoch"), checked_epoch):
        _reject("CHECKED_EPOCH_MISMATCH", "evidence checked epoch mismatch")
    if document.get("policy_root") != policy.policy_root:
        _reject("POLICY_BINDING_MISMATCH", "evidence policy root mismatch")
    if not _exact_equal(document.get("full_blob_target"), target.to_document()):
        _reject("FULL_BLOB_BINDING_MISMATCH", "evidence full-blob target mismatch")
    if not _exact_equal(document.get("beacon"), beacon.to_document()):
        _reject("BEACON_BINDING_MISMATCH", "evidence beacon mismatch")


def _require_chunk_hash_vector(
    document: Mapping[str, object],
    target: FullBlobRetrievabilityTargetV1,
) -> tuple[str, ...]:
    values = _require_list(document.get("ordered_chunk_hashes"), name="chunk hashes")
    if len(values) != target.chunk_count:
        _reject("CHUNK_ROOT_MISMATCH", "chunk-hash vector length mismatch")
    parsed: list[str] = []
    try:
        for index, value in enumerate(values):
            parsed.append(require_root(value, name=f"ordered_chunk_hashes[{index}]"))
        result = tuple(parsed)
        observed_root = derive_chunk_root_v1(result)
    except (TypeError, ValueError):
        _reject("CHUNK_ROOT_MISMATCH", "chunk-hash vector is invalid")
    if observed_root != target.chunk_root:
        _reject("CHUNK_ROOT_MISMATCH", "chunk-hash vector does not open the full-blob root")
    return result
