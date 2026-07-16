"""Bind governed Spot V7 DA to one transaction-locked release.

The incoming DA values already authenticate exact full-blob content, governed
sampled-retrievability evidence, a governed checkpoint beacon, and finalized
ledger inclusion within the sampled response deadline.  This module closes the
remaining local release-selection gap.  It checks the exact DA policy root and
operational-policy manifest selected by the current release while the unified
V7 release write transaction remains open.

The resulting value is a private prerequisite for the later atomic authority
join.  It establishes scoped content and finalized response-timing provenance.
It does not establish provider independence, continuing or future public
availability, release authority, settlement authority, or production authority.
"""

from __future__ import annotations

import hashlib
import sqlite3
from dataclasses import dataclass
from typing import NoReturn, SupportsIndex, final

from src.integration import _zrpf_spot_v7_release_state_engine_v7 as release_v7
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
)
from src.integration.zrpf_spot_v7_finalized_da_response_inclusion import (
    _AuthenticatedFinalizedSampledResponseInclusionV1,
)
from src.integration.zrpf_spot_v7_governed_da_prerequisite_v2 import (
    _GovernedSpotV7DataAvailabilityPrerequisiteV2,
)
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority_v1

_RELEASE_DA_POLICY_DOMAIN_V1 = b"zenodex.zrpf.spot_v7.release_da_policy.v1"


class SpotV7ReleaseBoundDaRejectV1(ValueError):
    """Stable fail-closed rejection from the release/DA join."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


@dataclass(frozen=True, slots=True)
class _ReleaseBoundDaValuesV1:
    policy_root: bytes
    operational_policy_manifest_sha256: bytes
    full_blob_policy_root: bytes
    sampled_policy_root: bytes
    beacon_policy_root: bytes
    finality_policy_root: bytes
    full_blob_certificate_root: bytes
    data_root: bytes
    exact_blob_sha256: bytes
    sampled_evidence_sha256: bytes
    beacon_checkpoint_hash: bytes
    checked_epoch: int
    response_deadline_epoch: int
    finalized_inclusion_epoch: int
    finalized_inclusion_block_hash: bytes
    finalized_inclusion_body_root: bytes
    finalized_inclusion_proof_root: bytes
    finality_evidence_root: bytes
    provider_set_root: bytes
    exact_blob_bytes: bytes
    exact_certificate_bytes: bytes
    exact_sampled_evidence_bytes: bytes
    exact_inclusion_body_bytes: bytes
    exact_inclusion_finality_evidence_bytes: bytes

    def __post_init__(self) -> None:
        for name in (
            "policy_root",
            "operational_policy_manifest_sha256",
            "full_blob_policy_root",
            "sampled_policy_root",
            "beacon_policy_root",
            "finality_policy_root",
            "full_blob_certificate_root",
            "data_root",
            "exact_blob_sha256",
            "sampled_evidence_sha256",
            "beacon_checkpoint_hash",
            "finalized_inclusion_block_hash",
            "finalized_inclusion_body_root",
            "finalized_inclusion_proof_root",
            "finality_evidence_root",
            "provider_set_root",
        ):
            _require_digest(getattr(self, name), name)
        for name in (
            "checked_epoch",
            "response_deadline_epoch",
            "finalized_inclusion_epoch",
        ):
            _require_u64(getattr(self, name), name)
        if not (
            self.checked_epoch
            <= self.finalized_inclusion_epoch
            <= self.response_deadline_epoch
        ):
            raise ValueError("finalized DA response inclusion is outside its deadline")
        for name in (
            "exact_blob_bytes",
            "exact_certificate_bytes",
            "exact_sampled_evidence_bytes",
            "exact_inclusion_body_bytes",
            "exact_inclusion_finality_evidence_bytes",
        ):
            value = getattr(self, name)
            if type(value) is not bytes or not value:
                raise TypeError(f"{name} must be non-empty exact bytes")


class _ReleaseBoundDaSealV1:
    __slots__ = ()


_RELEASE_BOUND_DA_SEAL_V1 = _ReleaseBoundDaSealV1()


@final
class _ReleaseBoundSpotV7DataAvailabilityV1:
    """Non-transferable governed DA fact tied to one release transaction."""

    __slots__ = (
        "_exact_execution_authority_manifest_bytes",
        "_finalized_inclusion",
        "_governed_da",
        "_identity",
        "_policy",
        "_release",
        "_release_candidate_id",
        "_release_candidate_sha256",
        "_release_revision",
        "_seal",
        "_values",
    )

    _exact_execution_authority_manifest_bytes: bytes
    _finalized_inclusion: _AuthenticatedFinalizedSampledResponseInclusionV1
    _governed_da: _GovernedSpotV7DataAvailabilityPrerequisiteV2
    _identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3
    _policy: _GovernedSpotV7OperationalPolicyV3
    _release: release_v7._TransactionBoundSpotV7CurrentReleaseV7
    _release_candidate_id: bytes
    _release_candidate_sha256: bytes
    _release_revision: int
    _seal: _ReleaseBoundDaSealV1
    _values: _ReleaseBoundDaValuesV1

    def __new__(cls) -> _ReleaseBoundSpotV7DataAvailabilityV1:
        raise TypeError("release-bound DA requires verified private construction")

    @classmethod
    def _from_verified_join(
        cls,
        *,
        identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
        release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
        policy: _GovernedSpotV7OperationalPolicyV3,
        governed_da: _GovernedSpotV7DataAvailabilityPrerequisiteV2,
        finalized_inclusion: _AuthenticatedFinalizedSampledResponseInclusionV1,
        exact_execution_authority_manifest_bytes: bytes,
        values: _ReleaseBoundDaValuesV1,
        seal: _ReleaseBoundDaSealV1,
    ) -> _ReleaseBoundSpotV7DataAvailabilityV1:
        if seal is not _RELEASE_BOUND_DA_SEAL_V1:
            raise TypeError("release-bound DA requires its module-private seal")
        result = object.__new__(cls)
        fields = {
            "_identity": identity,
            "_release": release,
            "_policy": policy,
            "_governed_da": governed_da,
            "_finalized_inclusion": finalized_inclusion,
            "_exact_execution_authority_manifest_bytes": (
                exact_execution_authority_manifest_bytes
            ),
            "_release_candidate_id": release.current_candidate_id,
            "_release_candidate_sha256": release.current_candidate_sha256,
            "_release_revision": release.current_release_revision,
            "_values": values,
            "_seal": seal,
        }
        for name, value in fields.items():
            object.__setattr__(result, name, value)
        return result

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("release-bound DA cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("release-bound DA is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("release-bound DA is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("release-bound DA cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("release-bound DA cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("release-bound DA cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("release-bound DA cannot be serialized")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _RELEASE_BOUND_DA_SEAL_V1

    @property
    def release_candidate_id(self) -> bytes:
        return self._release_candidate_id

    @property
    def release_candidate_sha256(self) -> bytes:
        return self._release_candidate_sha256

    @property
    def release_revision(self) -> int:
        return self._release_revision

    @property
    def policy_root(self) -> bytes:
        return self._values.policy_root

    @property
    def operational_policy_manifest_sha256(self) -> bytes:
        return self._values.operational_policy_manifest_sha256

    @property
    def full_blob_certificate_root(self) -> bytes:
        return self._values.full_blob_certificate_root

    @property
    def data_root(self) -> bytes:
        return self._values.data_root

    @property
    def exact_blob_sha256(self) -> bytes:
        return self._values.exact_blob_sha256

    @property
    def sampled_evidence_sha256(self) -> bytes:
        return self._values.sampled_evidence_sha256

    @property
    def beacon_checkpoint_hash(self) -> bytes:
        return self._values.beacon_checkpoint_hash

    @property
    def checked_epoch(self) -> int:
        return self._values.checked_epoch

    @property
    def response_deadline_epoch(self) -> int:
        return self._values.response_deadline_epoch

    @property
    def finalized_inclusion_epoch(self) -> int:
        return self._values.finalized_inclusion_epoch

    @property
    def finalized_inclusion_block_hash(self) -> bytes:
        return self._values.finalized_inclusion_block_hash

    @property
    def finalized_inclusion_body_root(self) -> bytes:
        return self._values.finalized_inclusion_body_root

    @property
    def finalized_inclusion_proof_root(self) -> bytes:
        return self._values.finalized_inclusion_proof_root

    @property
    def finality_evidence_root(self) -> bytes:
        return self._values.finality_evidence_root

    @property
    def provider_set_root(self) -> bytes:
        return self._values.provider_set_root

    @property
    def exact_blob_bytes(self) -> bytes:
        return self._values.exact_blob_bytes

    @property
    def exact_certificate_bytes(self) -> bytes:
        return self._values.exact_certificate_bytes

    @property
    def exact_sampled_evidence_bytes(self) -> bytes:
        return self._values.exact_sampled_evidence_bytes

    @property
    def exact_inclusion_body_bytes(self) -> bytes:
        return self._values.exact_inclusion_body_bytes

    @property
    def exact_inclusion_finality_evidence_bytes(self) -> bytes:
        return self._values.exact_inclusion_finality_evidence_bytes

    @property
    def release_governed_da_policy_identity_verified(self) -> bool:
        return True

    @property
    def governed_exact_full_blob_policy_satisfied(self) -> bool:
        return True

    @property
    def finalized_sampled_evidence_digest_included_by_deadline(self) -> bool:
        return True

    @property
    def response_timing_provenance_verified(self) -> bool:
        return True

    @property
    def provider_response_generation_time_verified(self) -> bool:
        return False

    @property
    def provider_independence_verified(self) -> bool:
        return False

    @property
    def continuous_availability_verified(self) -> bool:
        return False

    @property
    def public_future_availability_verified(self) -> bool:
        return False

    @property
    def external_monotonic_release_anchor_authenticated(self) -> bool:
        return False

    @property
    def hostile_same_interpreter_resistance_established(self) -> bool:
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


def _bind_release_locked_spot_v7_da_v1(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    operational_policy: object,
    governed_da: object,
    finalized_inclusion: object,
    exact_execution_authority_manifest_bytes: bytes,
) -> _ReleaseBoundSpotV7DataAvailabilityV1:
    """Bind exact sealed DA facts to the current selected release."""

    policy = _require_policy(operational_policy)
    data_availability = _require_governed_da(governed_da)
    inclusion = _require_finalized_inclusion(finalized_inclusion)
    if type(exact_execution_authority_manifest_bytes) is not bytes:
        raise TypeError("execution authority manifest must be exact bytes")
    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=release,
    )
    checked = _checked_execution_manifest(
        release=release,
        exact_execution_authority_manifest_bytes=(
            exact_execution_authority_manifest_bytes
        ),
    )
    values = _derive_bound_values_v1(
        policy=policy,
        governed_da=data_availability,
        finalized_inclusion=inclusion,
        checked_manifest=checked,
    )
    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=release,
    )
    result = _ReleaseBoundSpotV7DataAvailabilityV1._from_verified_join(
        identity=identity,
        release=release,
        policy=policy,
        governed_da=data_availability,
        finalized_inclusion=inclusion,
        exact_execution_authority_manifest_bytes=(
            exact_execution_authority_manifest_bytes
        ),
        values=values,
        seal=_RELEASE_BOUND_DA_SEAL_V1,
    )
    _revalidate_release_bound_da_v1(result)
    return result


def _require_release_bound_da_still_locked_v1(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    data_availability: _ReleaseBoundSpotV7DataAvailabilityV1,
) -> _ReleaseBoundSpotV7DataAvailabilityV1:
    """Revalidate the release lock and every retained DA byte projection."""

    if type(data_availability) is not _ReleaseBoundSpotV7DataAvailabilityV1:
        raise TypeError("atomic join requires exact release-bound DA")
    if not data_availability._has_private_seal():
        raise TypeError("release-bound DA lacks its private seal")
    if identity != data_availability._identity:
        raise ValueError("release-bound DA retained a different store identity")
    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=data_availability._release,
    )
    _revalidate_release_bound_da_v1(data_availability)
    return data_availability


def _revalidate_release_bound_da_v1(
    value: _ReleaseBoundSpotV7DataAvailabilityV1,
) -> None:
    if not value._has_private_seal():
        raise TypeError("release-bound DA lacks its private seal")
    checked = _checked_execution_manifest(
        release=value._release,
        exact_execution_authority_manifest_bytes=(
            value._exact_execution_authority_manifest_bytes
        ),
    )
    expected_values = _derive_bound_values_v1(
        policy=value._policy,
        governed_da=value._governed_da,
        finalized_inclusion=value._finalized_inclusion,
        checked_manifest=checked,
    )
    observed = (
        value._release_candidate_id,
        value._release_candidate_sha256,
        value._release_revision,
        value._values,
    )
    expected = (
        value._release.current_candidate_id,
        value._release.current_candidate_sha256,
        value._release.current_release_revision,
        expected_values,
    )
    if observed != expected:
        raise _reject("RETAINED_BINDING_DRIFT", "release-bound DA retained binding drift")


def _derive_release_da_policy_root_v1(operational_policy: object) -> bytes:
    """Derive the release identity for the complete governed DA policy surface."""

    policy = _require_policy(operational_policy)
    projection = policy._projection_for_governed_da_v2()
    components = (
        projection.application_id,
        projection.chain_or_domain_id,
        projection.full_blob_da_policy_root,
        projection.checkpoint_finality_policy_root,
        projection.beacon_source_finality_policy_root,
        projection.sampled_policy_root,
        projection.beacon_policy_root,
        projection.policy_provenance_root,
    )
    chain_id = projection.zeno_ledger_chain_id.encode("ascii")
    if not chain_id or len(chain_id) > 0xFFFF:
        raise ValueError("governed DA chain ID is outside the release bound")
    payload = bytearray()
    payload.extend(len(_RELEASE_DA_POLICY_DOMAIN_V1).to_bytes(2, "big"))
    payload.extend(_RELEASE_DA_POLICY_DOMAIN_V1)
    payload.extend(len(chain_id).to_bytes(2, "big"))
    payload.extend(chain_id)
    for component in components:
        payload.extend(_prefixed_digest(component, "governed DA policy component"))
    return hashlib.sha256(payload).digest()


def _derive_bound_values_v1(
    *,
    policy: _GovernedSpotV7OperationalPolicyV3,
    governed_da: _GovernedSpotV7DataAvailabilityPrerequisiteV2,
    finalized_inclusion: _AuthenticatedFinalizedSampledResponseInclusionV1,
    checked_manifest: authority_v1.CheckedSpotV7ExecutionAuthorityManifestV1,
) -> _ReleaseBoundDaValuesV1:
    policy._require_live_integrity()
    if governed_da._policy is not policy:
        raise _reject(
            "POLICY_CAPABILITY_MISMATCH",
            "governed DA retained a different operational policy capability",
        )
    if finalized_inclusion._sampled is not governed_da._sampled._sampled:
        raise _reject(
            "SAMPLED_EVIDENCE_CAPABILITY_MISMATCH",
            "finalized inclusion and governed DA do not share one sampled fact",
        )
    try:
        da_projection = governed_da._projection_for_downstream_binding_v2()
    except (TypeError, ValueError) as exc:
        raise _reject("DA_PREREQUISITE_BINDING", str(exc)) from exc
    try:
        inclusion = finalized_inclusion._projection_for_da_store_v5()
    except (TypeError, ValueError) as exc:
        raise _reject("FINALIZED_INCLUSION_BINDING", str(exc)) from exc

    policy_projection = policy._projection_for_governed_da_v2()
    expected_policy_root = _derive_release_da_policy_root_v1(policy)
    execution = checked_manifest.execution_manifest
    if execution._policies["data_availability_policy_root"] != expected_policy_root:
        raise _reject(
            "DA_POLICY_BINDING",
            "governed DA policy differs from the selected release",
        )
    operational_policy_manifest_sha256 = bytes.fromhex(policy._provenance.manifest_sha256)
    if execution._policies["operational_policy_root"] != (
        operational_policy_manifest_sha256
    ):
        raise _reject(
            "OPERATIONAL_POLICY_BINDING",
            "governed operational policy differs from the selected release",
        )
    finality_policy_root = _prefixed_digest(
        inclusion.finality_policy_root,
        "finalized inclusion finality policy root",
    )
    if (
        finality_policy_root
        != _prefixed_digest(
            policy_projection.checkpoint_finality_policy_root,
            "governed checkpoint-finality policy root",
        )
        or finality_policy_root != execution._policies["finality_policy_root"]
    ):
        raise _reject(
            "FINALITY_POLICY_BINDING",
            "finalized inclusion uses a different finality policy",
        )

    base = da_projection.base
    observed = (
        inclusion.application_id,
        inclusion.chain_or_domain_id,
        inclusion.zeno_ledger_chain_id,
        inclusion.data_epoch_id,
        inclusion.checked_epoch,
        inclusion.policy_root,
        inclusion.certificate_root,
        inclusion.data_root,
        inclusion.beacon_commitment,
        inclusion.sampled_evidence_sha256,
        inclusion.accepted_provider_set_root,
    )
    expected = (
        base.application_id,
        base.chain_or_domain_id,
        da_projection.zeno_ledger_chain_id,
        base.epoch_id,
        base.checked_epoch,
        base.sampled_policy_root,
        base.certificate_root,
        base.data_root,
        base.beacon_commitment,
        "0x" + base.sampled_evidence_sha256,
        base.accepted_provider_set_root,
    )
    if observed != expected:
        raise _reject(
            "FINALIZED_INCLUSION_DA_BINDING",
            "finalized inclusion differs from governed exact DA",
        )
    policy._require_active_at_epoch_for_governed_da_v2(base.checked_epoch)
    policy._require_active_at_epoch_for_governed_da_v2(inclusion.inclusion_height)

    return _ReleaseBoundDaValuesV1(
        policy_root=expected_policy_root,
        operational_policy_manifest_sha256=operational_policy_manifest_sha256,
        full_blob_policy_root=_prefixed_digest(
            base.full_blob_policy_root,
            "full-blob policy root",
        ),
        sampled_policy_root=_prefixed_digest(base.sampled_policy_root, "sampled policy root"),
        beacon_policy_root=_prefixed_digest(base.beacon_policy_hash, "beacon policy root"),
        finality_policy_root=finality_policy_root,
        full_blob_certificate_root=_prefixed_digest(
            base.certificate_root,
            "full-blob certificate root",
        ),
        data_root=_prefixed_digest(base.data_root, "DA data root"),
        exact_blob_sha256=_prefixed_digest(base.exact_blob_sha256, "exact blob SHA-256"),
        sampled_evidence_sha256=_bare_digest(
            base.sampled_evidence_sha256,
            "sampled evidence SHA-256",
        ),
        beacon_checkpoint_hash=_prefixed_digest(
            da_projection.source_checkpoint_hash,
            "beacon checkpoint hash",
        ),
        checked_epoch=base.checked_epoch,
        response_deadline_epoch=inclusion.response_deadline_epoch,
        finalized_inclusion_epoch=inclusion.inclusion_height,
        finalized_inclusion_block_hash=_prefixed_digest(
            inclusion.finalized_header_hash,
            "finalized inclusion block hash",
        ),
        finalized_inclusion_body_root=_prefixed_digest(
            inclusion.finalized_body_root,
            "finalized inclusion body root",
        ),
        finalized_inclusion_proof_root=_prefixed_digest(
            inclusion.inclusion_record_root,
            "finalized inclusion proof root",
        ),
        finality_evidence_root=_prefixed_digest(
            inclusion.finality_evidence_root,
            "finalized inclusion finality evidence root",
        ),
        provider_set_root=_prefixed_digest(
            base.accepted_provider_set_root,
            "sampled provider-set root",
        ),
        exact_blob_bytes=governed_da._full_blob._exact_blob_bytes,
        exact_certificate_bytes=governed_da._full_blob._exact_certificate_bytes,
        exact_sampled_evidence_bytes=governed_da._sampled._sampled.exact_evidence_bytes,
        exact_inclusion_body_bytes=finalized_inclusion._exact_body_bytes,
        exact_inclusion_finality_evidence_bytes=(
            finalized_inclusion._finality._exact_finality_evidence_bytes
        ),
    )


def _checked_execution_manifest(
    *,
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    exact_execution_authority_manifest_bytes: bytes,
) -> authority_v1.CheckedSpotV7ExecutionAuthorityManifestV1:
    try:
        checked = authority_v1.check_exact_spot_v7_execution_authority_manifest_v1(
            exact_release_candidate_bytes=release.current_candidate_bytes,
            exact_authority_manifest_bytes=exact_execution_authority_manifest_bytes,
        )
    except (TypeError, ValueError) as exc:
        raise _reject(
            "EXECUTION_AUTHORITY_MANIFEST",
            "execution authority manifest is not bound to selected release",
        ) from exc
    observed = (
        checked.candidate_id,
        checked.candidate_manifest_sha256,
        checked.release_revision,
    )
    expected = (
        release.current_candidate_id,
        release.current_candidate_sha256,
        release.current_release_revision,
    )
    if observed != expected:
        raise _reject(
            "RELEASE_CANDIDATE_BINDING",
            "execution authority manifest differs from current release",
        )
    return checked


def _require_policy(value: object) -> _GovernedSpotV7OperationalPolicyV3:
    if (
        not isinstance(value, _GovernedSpotV7OperationalPolicyV3)
        or type(value) is not _GovernedSpotV7OperationalPolicyV3
    ):
        raise TypeError("release-bound DA requires exact Spot V7 operational policy V3")
    policy = value
    if not policy._has_private_seal():
        raise TypeError("release-bound DA requires sealed Spot V7 operational policy V3")
    policy._require_live_integrity()
    return policy


def _require_governed_da(
    value: object,
) -> _GovernedSpotV7DataAvailabilityPrerequisiteV2:
    if (
        not isinstance(value, _GovernedSpotV7DataAvailabilityPrerequisiteV2)
        or type(value) is not _GovernedSpotV7DataAvailabilityPrerequisiteV2
    ):
        raise TypeError("release-bound DA requires exact governed DA V2")
    governed_da = value
    if not governed_da._has_private_seal():
        raise TypeError("release-bound DA requires sealed governed DA V2")
    governed_da._projection_for_downstream_binding_v2()
    return governed_da


def _require_finalized_inclusion(
    value: object,
) -> _AuthenticatedFinalizedSampledResponseInclusionV1:
    if (
        not isinstance(value, _AuthenticatedFinalizedSampledResponseInclusionV1)
        or type(value) is not _AuthenticatedFinalizedSampledResponseInclusionV1
    ):
        raise TypeError("release-bound DA requires exact finalized inclusion V1")
    inclusion = value
    if not inclusion._has_private_seal():
        raise TypeError("release-bound DA requires sealed finalized inclusion V1")
    inclusion._projection_for_da_store_v5()
    return inclusion


def _prefixed_digest(value: object, name: str) -> bytes:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise ValueError(f"{name} must be canonical lowercase 32-byte hex")
    return _require_digest(bytes.fromhex(value[2:]), name)


def _bare_digest(value: object, name: str) -> bytes:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValueError(f"{name} must be canonical lowercase 32-byte hex")
    return _require_digest(bytes.fromhex(value), name)


def _require_digest(value: object, name: str) -> bytes:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise ValueError(f"{name} must be nonzero 32-byte bytes")
    return value


def _require_u64(value: object, name: str) -> int:
    if type(value) is not int or value < 0 or value > 0xFFFF_FFFF_FFFF_FFFF:
        raise ValueError(f"{name} must be a u64")
    return value


def _reject(code: str, detail: str) -> SpotV7ReleaseBoundDaRejectV1:
    return SpotV7ReleaseBoundDaRejectV1(code, detail)


__all__ = ()
