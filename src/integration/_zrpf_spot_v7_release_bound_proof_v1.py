"""Bind one pinned Spot V7 proof observation to the transaction-locked release.

The pinned verifier observation is authority-neutral because its caller chooses
the executable and manifest.  This module closes that local identity gap by
requiring the exact current release candidate, the candidate-bound execution
authority manifest, and the exact proof-verifier manifest in one still-open V7
release transaction.  It deliberately carries no asset-effects root: the later
atomic settlement join must derive that root from its independently validated
settlement plan and compare the exact Plan B bytes retained here.
"""

from __future__ import annotations

import hashlib
import json
import sqlite3
from typing import Any, NoReturn, SupportsIndex, cast, final

from src.integration import _zrpf_spot_v7_authenticated_proof_v1 as proof_v1
from src.integration import _zrpf_spot_v7_release_state_engine_v7 as release_v7
from src.integration.recursive_stark_verifier_adapter import (
    RecursiveVerifierExecutableFormat,
)
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority_v1
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate_v1

_APPLICATION_ID_DOMAIN_V1 = b"zenodex.zrpf.application_id.v3"
_CHAIN_OR_DOMAIN_ID_DOMAIN_V1 = b"zenodex.zrpf.chain_or_domain_id.v3"


class SpotV7ReleaseBoundProofRejectV1(ValueError):
    """Stable fail-closed rejection from the release/proof join."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


class _ReleaseBoundProofSealV1:
    __slots__ = ()


_RELEASE_BOUND_PROOF_SEAL_V1 = _ReleaseBoundProofSealV1()


@final
class _ReleaseBoundSpotV7SemanticProofV1:
    """Private proof capability that remains tied to one release transaction."""

    __slots__ = (
        "_candidate_id",
        "_candidate_sha256",
        "_exact_execution_authority_manifest_bytes",
        "_exact_plan_b_bytes",
        "_exact_proof_verifier_manifest_bytes",
        "_observation",
        "_proof_verifier_executable_sha256",
        "_proof_verifier_manifest_sha256",
        "_release",
        "_release_revision",
        "_settlement_effect_plan_commitment",
    )
    _candidate_id: bytes
    _candidate_sha256: bytes
    _exact_execution_authority_manifest_bytes: bytes
    _exact_plan_b_bytes: bytes
    _exact_proof_verifier_manifest_bytes: bytes
    _observation: proof_v1._PinnedSpotV7SemanticProofObservationV1
    _proof_verifier_executable_sha256: bytes
    _proof_verifier_manifest_sha256: bytes
    _release: release_v7._TransactionBoundSpotV7CurrentReleaseV7
    _release_revision: int
    _settlement_effect_plan_commitment: bytes

    def __new__(cls) -> _ReleaseBoundSpotV7SemanticProofV1:
        raise TypeError("release-bound proof requires verified private construction")

    @classmethod
    def _from_verified_join(
        cls,
        *,
        release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
        observation: proof_v1._PinnedSpotV7SemanticProofObservationV1,
        exact_execution_authority_manifest_bytes: bytes,
        exact_proof_verifier_manifest_bytes: bytes,
        proof_verifier_manifest_sha256: bytes,
        proof_verifier_executable_sha256: bytes,
        seal: _ReleaseBoundProofSealV1,
    ) -> _ReleaseBoundSpotV7SemanticProofV1:
        if seal is not _RELEASE_BOUND_PROOF_SEAL_V1:
            raise TypeError("release-bound proof requires its module-private seal")
        value = object.__new__(cls)
        object.__setattr__(value, "_release", release)
        object.__setattr__(value, "_observation", observation)
        object.__setattr__(value, "_candidate_id", release.current_candidate_id)
        object.__setattr__(value, "_candidate_sha256", release.current_candidate_sha256)
        object.__setattr__(value, "_release_revision", release.current_release_revision)
        object.__setattr__(
            value,
            "_exact_execution_authority_manifest_bytes",
            exact_execution_authority_manifest_bytes,
        )
        object.__setattr__(
            value,
            "_exact_proof_verifier_manifest_bytes",
            exact_proof_verifier_manifest_bytes,
        )
        object.__setattr__(
            value,
            "_proof_verifier_manifest_sha256",
            _require_digest(proof_verifier_manifest_sha256, "proof verifier manifest"),
        )
        object.__setattr__(
            value,
            "_proof_verifier_executable_sha256",
            _require_digest(proof_verifier_executable_sha256, "proof verifier executable"),
        )
        object.__setattr__(value, "_exact_plan_b_bytes", observation.exact_plan_b_bytes)
        object.__setattr__(
            value,
            "_settlement_effect_plan_commitment",
            bytes.fromhex(observation.settlement_effect_plan_commitment),
        )
        return value

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("release-bound proof cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("release-bound proof is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("release-bound proof is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("release-bound proof cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("release-bound proof cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("release-bound proof cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("release-bound proof cannot be serialized")

    @property
    def release_candidate_id(self) -> bytes:
        return self._candidate_id

    @property
    def release_candidate_sha256(self) -> bytes:
        return self._candidate_sha256

    @property
    def release_revision(self) -> int:
        return self._release_revision

    @property
    def exact_execution_authority_manifest_bytes(self) -> bytes:
        return self._exact_execution_authority_manifest_bytes

    @property
    def exact_proof_verifier_manifest_bytes(self) -> bytes:
        return self._exact_proof_verifier_manifest_bytes

    @property
    def proof_verifier_manifest_sha256(self) -> bytes:
        return self._proof_verifier_manifest_sha256

    @property
    def proof_verifier_executable_sha256(self) -> bytes:
        return self._proof_verifier_executable_sha256

    @property
    def exact_plan_b_bytes(self) -> bytes:
        return self._exact_plan_b_bytes

    @property
    def exact_plan_b_sha256(self) -> bytes:
        return hashlib.sha256(self._exact_plan_b_bytes).digest()

    @property
    def settlement_effect_plan_commitment(self) -> bytes:
        return self._settlement_effect_plan_commitment

    @property
    def exact_v7_receipt_bytes(self) -> bytes:
        return self._observation.exact_v7_receipt_bytes

    @property
    def exact_v7_journal_bytes(self) -> bytes:
        return self._observation.exact_v7_journal_bytes

    @property
    def release_and_proof_share_write_transaction(self) -> bool:
        return self._release.release_and_settlement_share_write_transaction

    @property
    def release_governed_verifier_identity_verified(self) -> bool:
        return True

    @property
    def proof_receipt_authority(self) -> bool:
        return True

    @property
    def external_monotonic_anchor_authenticated(self) -> bool:
        return False

    @property
    def finality_verified(self) -> bool:
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


def _bind_release_locked_spot_v7_semantic_proof_v1(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    observation: proof_v1._PinnedSpotV7SemanticProofObservationV1,
    exact_execution_authority_manifest_bytes: bytes,
    exact_proof_verifier_manifest_bytes: bytes,
) -> _ReleaseBoundSpotV7SemanticProofV1:
    """Bind a sealed proof observation to the exact transaction-locked release."""

    if type(release) is not release_v7._TransactionBoundSpotV7CurrentReleaseV7:
        raise TypeError("proof join requires the exact transaction-bound release type")
    if type(observation) is not proof_v1._PinnedSpotV7SemanticProofObservationV1:
        raise TypeError("proof join requires the exact pinned proof observation type")
    if not observation._has_private_seal():
        raise _reject("PROOF_OBSERVATION_SEAL", "pinned proof observation seal differs")
    if type(exact_execution_authority_manifest_bytes) is not bytes:
        raise TypeError("execution authority manifest must be exact bytes")
    if type(exact_proof_verifier_manifest_bytes) is not bytes:
        raise TypeError("proof verifier manifest must be exact bytes")
    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=release,
    )
    candidate_document = _checked_release_candidate_document(release, identity)
    manifest_binding = _checked_execution_authority_manifest(
        release=release,
        exact_execution_authority_manifest_bytes=exact_execution_authority_manifest_bytes,
    )
    verifier_manifest_sha256 = _bind_exact_proof_verifier_manifest(
        candidate_document=candidate_document,
        exact_proof_verifier_manifest_bytes=exact_proof_verifier_manifest_bytes,
    )
    executable_sha256, trusted_policy = _parse_selected_proof_verifier_manifest(
        exact_proof_verifier_manifest_bytes,
        verifier_manifest_sha256,
    )
    _bind_execution_manifest_verifier(
        exact_execution_authority_manifest_bytes=exact_execution_authority_manifest_bytes,
        proof_verifier_manifest_sha256=verifier_manifest_sha256,
        proof_verifier_executable_sha256=executable_sha256,
    )
    _bind_observation(
        observation=observation,
        identity=identity,
        trusted_policy=trusted_policy,
        proof_verifier_manifest_sha256=verifier_manifest_sha256,
        proof_verifier_executable_sha256=executable_sha256,
    )
    if manifest_binding.release_revision != release.current_release_revision:
        raise _reject("AUTHORITY_RELEASE_REVISION", "authority manifest revision differs")
    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=release,
    )
    return _ReleaseBoundSpotV7SemanticProofV1._from_verified_join(
        release=release,
        observation=observation,
        exact_execution_authority_manifest_bytes=exact_execution_authority_manifest_bytes,
        exact_proof_verifier_manifest_bytes=exact_proof_verifier_manifest_bytes,
        proof_verifier_manifest_sha256=verifier_manifest_sha256,
        proof_verifier_executable_sha256=executable_sha256,
        seal=_RELEASE_BOUND_PROOF_SEAL_V1,
    )


def _require_release_bound_proof_still_locked_v1(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    proof: _ReleaseBoundSpotV7SemanticProofV1,
) -> _ReleaseBoundSpotV7SemanticProofV1:
    """Recheck the nontransferable capability immediately before its consumer."""

    if type(proof) is not _ReleaseBoundSpotV7SemanticProofV1:
        raise TypeError("atomic join requires the exact release-bound proof type")
    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=proof._release,
    )
    _revalidate_release_bound_proof_v1(identity=identity, proof=proof)
    return proof


def _revalidate_release_bound_proof_v1(
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    proof: _ReleaseBoundSpotV7SemanticProofV1,
) -> None:
    """Recompose every retained proof binding before an authority join."""

    if not proof._observation._has_private_seal():
        raise _reject("PROOF_OBSERVATION_SEAL", "pinned proof observation seal differs")
    candidate_document = _checked_release_candidate_document(proof._release, identity)
    manifest_binding = _checked_execution_authority_manifest(
        release=proof._release,
        exact_execution_authority_manifest_bytes=(proof._exact_execution_authority_manifest_bytes),
    )
    verifier_manifest_sha256 = _bind_exact_proof_verifier_manifest(
        candidate_document=candidate_document,
        exact_proof_verifier_manifest_bytes=proof._exact_proof_verifier_manifest_bytes,
    )
    executable_sha256, trusted_policy = _parse_selected_proof_verifier_manifest(
        proof._exact_proof_verifier_manifest_bytes,
        verifier_manifest_sha256,
    )
    _bind_execution_manifest_verifier(
        exact_execution_authority_manifest_bytes=(proof._exact_execution_authority_manifest_bytes),
        proof_verifier_manifest_sha256=verifier_manifest_sha256,
        proof_verifier_executable_sha256=executable_sha256,
    )
    _bind_observation(
        observation=proof._observation,
        identity=identity,
        trusted_policy=trusted_policy,
        proof_verifier_manifest_sha256=verifier_manifest_sha256,
        proof_verifier_executable_sha256=executable_sha256,
    )
    try:
        settlement_effect_plan_commitment = bytes.fromhex(
            proof._observation.settlement_effect_plan_commitment
        )
    except (TypeError, ValueError) as exc:
        raise _reject(
            "RETAINED_BINDING_DRIFT",
            "proof observation settlement-plan commitment is invalid",
        ) from exc
    observed = (
        proof._candidate_id,
        proof._candidate_sha256,
        proof._release_revision,
        proof._exact_plan_b_bytes,
        proof._proof_verifier_manifest_sha256,
        proof._proof_verifier_executable_sha256,
        proof._settlement_effect_plan_commitment,
    )
    expected = (
        proof._release.current_candidate_id,
        proof._release.current_candidate_sha256,
        manifest_binding.release_revision,
        proof._observation.exact_plan_b_bytes,
        verifier_manifest_sha256,
        executable_sha256,
        settlement_effect_plan_commitment,
    )
    if observed != expected:
        raise _reject(
            "RETAINED_BINDING_DRIFT",
            "release-bound proof retained binding drift",
        )


def _checked_release_candidate_document(
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> dict[str, Any]:
    try:
        candidate = candidate_v1.parse_exact_spot_v7_release_candidate_manifest_v1(
            release.current_candidate_bytes
        )
    except (TypeError, ValueError) as exc:
        raise _reject("RELEASE_CANDIDATE", str(exc)) from exc
    if (
        candidate.candidate_id != release.current_candidate_id
        or hashlib.sha256(candidate.canonical_bytes).digest() != release.current_candidate_sha256
        or candidate.release_revision != release.current_release_revision
    ):
        raise _reject("RELEASE_CANDIDATE_BINDING", "locked release candidate differs")
    document = cast(dict[str, Any], json.loads(candidate.canonical_bytes))
    scope = cast(dict[str, object], document["scope"])
    if (
        scope["application_id"] != identity.application_id
        or scope["chain_id"] != identity.chain_id
        or scope["domain_id"] != identity.domain_id
        or scope["release_profile"] != identity.release_profile
    ):
        raise _reject("RELEASE_SCOPE", "candidate scope differs from release-store identity")
    return document


def _checked_execution_authority_manifest(
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
        raise _reject("EXECUTION_AUTHORITY_MANIFEST", str(exc)) from exc
    if (
        checked.candidate_id != release.current_candidate_id
        or checked.candidate_manifest_sha256 != release.current_candidate_sha256
        or checked.release_revision != release.current_release_revision
    ):
        raise _reject("EXECUTION_AUTHORITY_BINDING", "authority manifest release differs")
    return checked


def _bind_exact_proof_verifier_manifest(
    *,
    candidate_document: dict[str, Any],
    exact_proof_verifier_manifest_bytes: bytes,
) -> bytes:
    digest = hashlib.sha256(exact_proof_verifier_manifest_bytes).digest()
    manifests = cast(dict[str, object], candidate_document["manifests"])
    inventory = cast(list[dict[str, object]], candidate_document["evidence_inventory"])
    rows = [row for row in inventory if row.get("role") == "verifier_manifest"]
    if len(rows) != 1:
        raise _reject("VERIFIER_MANIFEST_INVENTORY", "candidate verifier row is not unique")
    row = rows[0]
    expected_codec = candidate_v1.EXPECTED_EVIDENCE_CODEC_BY_ROLE_V1["verifier_manifest"]
    if (
        manifests.get("verifier_manifest_sha256") != digest.hex()
        or row.get("artifact_sha256") != digest.hex()
        or row.get("bound_identity") != digest.hex()
        or row.get("codec") != expected_codec
        or type(row.get("size_bytes")) is not int
        or row["size_bytes"] != len(exact_proof_verifier_manifest_bytes)
    ):
        raise _reject("VERIFIER_MANIFEST_BINDING", "exact verifier manifest differs")
    return digest


def _parse_selected_proof_verifier_manifest(
    exact_proof_verifier_manifest_bytes: bytes,
    verifier_manifest_sha256: bytes,
) -> tuple[bytes, proof_v1._TrustedSpotV7ProofPolicyV1]:
    try:
        executable, executable_format, policy, _policy_json = proof_v1._parse_authority_manifest(
            exact_proof_verifier_manifest_bytes,
            expected_sha256=verifier_manifest_sha256.hex(),
        )
    except (TypeError, ValueError) as exc:
        raise _reject("PROOF_VERIFIER_MANIFEST", str(exc)) from exc
    if executable_format is not RecursiveVerifierExecutableFormat.STATIC_ELF_X86_64:
        raise _reject("PROOF_VERIFIER_FORMAT", "selected verifier is not a static ELF")
    return bytes.fromhex(executable), policy


def _bind_execution_manifest_verifier(
    *,
    exact_execution_authority_manifest_bytes: bytes,
    proof_verifier_manifest_sha256: bytes,
    proof_verifier_executable_sha256: bytes,
) -> None:
    document = cast(dict[str, Any], json.loads(exact_execution_authority_manifest_bytes))
    artifacts = cast(dict[str, object], document["artifacts"])
    if (
        artifacts.get("proof_verifier_manifest_sha256") != proof_verifier_manifest_sha256.hex()
        or artifacts.get("proof_verifier_executable_sha256")
        != proof_verifier_executable_sha256.hex()
    ):
        raise _reject("AUTHORITY_VERIFIER_BINDING", "authority verifier identity differs")


def _bind_observation(
    *,
    observation: proof_v1._PinnedSpotV7SemanticProofObservationV1,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    trusted_policy: proof_v1._TrustedSpotV7ProofPolicyV1,
    proof_verifier_manifest_sha256: bytes,
    proof_verifier_executable_sha256: bytes,
) -> None:
    observed_profile = observation.receipt_security_profile
    expected_profile = trusted_policy.receipt_security_profile
    observed = (
        observation.application_id,
        observation.chain_or_domain_id,
        observation.epoch_id,
        observation.verified_program_id,
        observation.verified_profile_id,
        observation.verified_program_manifest_root,
        observed_profile,
        observation.source_child_program_id,
        observation.required_source_child_receipt_security_profile_id,
        observation.proof_verifier_authority_manifest_sha256,
        observation.proof_verifier_executable_sha256,
    )
    expected = (
        _derive_release_scope_id_v1(_APPLICATION_ID_DOMAIN_V1, identity.application_id),
        _derive_release_scope_id_v1(_CHAIN_OR_DOMAIN_ID_DOMAIN_V1, identity.domain_id),
        trusted_policy.epoch_id,
        trusted_policy.verified_program_id,
        trusted_policy.verified_profile_id,
        trusted_policy.verified_program_manifest_root,
        expected_profile,
        trusted_policy.source_child_program_id,
        trusted_policy.required_source_child_receipt_security_profile_id,
        proof_verifier_manifest_sha256.hex(),
        proof_verifier_executable_sha256.hex(),
    )
    if observed != expected:
        raise _reject("PROOF_OBSERVATION_BINDING", "proof observation differs from release")
    if type(observation.exact_plan_b_bytes) is not bytes or not observation.exact_plan_b_bytes:
        raise _reject("PLAN_B_BYTES", "proof observation has no exact Plan B bytes")
    try:
        commitment = bytes.fromhex(observation.settlement_effect_plan_commitment)
    except ValueError as exc:
        raise _reject("PLAN_B_COMMITMENT", "settlement plan commitment is invalid") from exc
    _require_digest(commitment, "settlement plan commitment")


def _derive_release_scope_id_v1(domain: bytes, value: str) -> str:
    if type(domain) is not bytes or not domain or len(domain) > 0xFFFF:
        raise ValueError("release scope hash domain is invalid")
    if type(value) is not str or not value or not value.isascii():
        raise ValueError("release scope identifier must be nonempty ASCII")
    payload = value.encode("ascii")
    if len(payload) > 0xFFFF_FFFF:
        raise ValueError("release scope identifier is too large")
    return hashlib.sha256(
        len(domain).to_bytes(2, "big") + domain + len(payload).to_bytes(4, "big") + payload
    ).hexdigest()


def _require_digest(value: object, name: str) -> bytes:
    if type(value) is not bytes or len(value) != 32 or not any(value):
        raise ValueError(f"{name} digest must be nonzero 32-byte bytes")
    return value


def _reject(code: str, detail: str) -> SpotV7ReleaseBoundProofRejectV1:
    return SpotV7ReleaseBoundProofRejectV1(code, detail)


__all__ = ()
