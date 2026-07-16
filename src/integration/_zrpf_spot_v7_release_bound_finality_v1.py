"""Bind authenticated checkpoint finality to one transaction-locked release.

The checkpoint transition entering this module has already passed the
protocol-specific BLS adapter and one exact invocation of the pinned Rust
cross-checker.  That result is still caller-configured until the executable and
manifest identities are checked against the selected release candidate.  This
module closes that identity gap while the V7 release write transaction remains
open.

The resulting capability proves release-bound checkpoint finality only.  The
release watermark remains authority-neutral, and no settlement or production
authority is minted here.
"""

from __future__ import annotations

import hashlib
import sqlite3
from typing import NoReturn, SupportsIndex, final

from src.integration import _zrpf_spot_v7_release_state_engine_v7 as release_v7
from src.integration import zrpf_spot_v7_checkpoint_finality_checker_adapter as finality_v1
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority_v1


class SpotV7ReleaseBoundFinalityRejectV1(ValueError):
    """Stable fail-closed rejection at the release-to-finality join."""

    def __init__(self, code: str, detail: str) -> None:
        self.code = code
        self.detail = detail
        super().__init__(f"{code}: {detail}")


@final
class _ReleaseBoundSpotV7CheckpointFinalityV1:
    """Non-transferable checkpoint finality bound to one locked release."""

    __slots__ = (
        "_certificate_root",
        "_checker_executable_sha256",
        "_checker_manifest_sha256",
        "_cross_checked_finality",
        "_epoch_id",
        "_exact_execution_authority_manifest_bytes",
        "_finality_evidence_root",
        "_finality_policy_root",
        "_identity",
        "_next_checkpoint_hash",
        "_next_checkpoint_sequence",
        "_post_state_root",
        "_prior_checkpoint_hash",
        "_prior_checkpoint_sequence",
        "_proof_journal_hash",
        "_release",
        "_release_candidate_id",
        "_release_candidate_sha256",
        "_release_revision",
        "_seal",
    )

    _certificate_root: bytes
    _checker_executable_sha256: bytes
    _checker_manifest_sha256: bytes
    _cross_checked_finality: finality_v1._CrossCheckedAuthenticatedCheckpointFinalityTransitionV1
    _epoch_id: int
    _exact_execution_authority_manifest_bytes: bytes
    _finality_evidence_root: bytes
    _finality_policy_root: bytes
    _identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3
    _next_checkpoint_hash: bytes
    _next_checkpoint_sequence: int
    _post_state_root: bytes
    _prior_checkpoint_hash: bytes
    _prior_checkpoint_sequence: int
    _proof_journal_hash: bytes
    _release: release_v7._TransactionBoundSpotV7CurrentReleaseV7
    _release_candidate_id: bytes
    _release_candidate_sha256: bytes
    _release_revision: int
    _seal: object

    def __new__(cls) -> _ReleaseBoundSpotV7CheckpointFinalityV1:
        raise TypeError("release-bound finality requires verified private construction")

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("release-bound finality cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("release-bound finality is immutable")

    def __delattr__(self, _name: str) -> NoReturn:
        raise TypeError("release-bound finality is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("release-bound finality cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("release-bound finality cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("release-bound finality cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("release-bound finality cannot be serialized")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is self

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
    def epoch_id(self) -> int:
        return self._epoch_id

    @property
    def proof_journal_hash(self) -> bytes:
        return self._proof_journal_hash

    @property
    def post_state_root(self) -> bytes:
        return self._post_state_root

    @property
    def certificate_root(self) -> bytes:
        return self._certificate_root

    @property
    def finality_policy_root(self) -> bytes:
        return self._finality_policy_root

    @property
    def finality_evidence_root(self) -> bytes:
        return self._finality_evidence_root

    @property
    def prior_checkpoint_sequence(self) -> int:
        return self._prior_checkpoint_sequence

    @property
    def prior_checkpoint_hash(self) -> bytes:
        return self._prior_checkpoint_hash

    @property
    def next_checkpoint_sequence(self) -> int:
        return self._next_checkpoint_sequence

    @property
    def next_checkpoint_hash(self) -> bytes:
        return self._next_checkpoint_hash

    @property
    def checker_manifest_sha256(self) -> bytes:
        return self._checker_manifest_sha256

    @property
    def checker_executable_sha256(self) -> bytes:
        return self._checker_executable_sha256

    @property
    def release_governed_checker_identity_verified(self) -> bool:
        return True

    @property
    def checkpoint_finality_authenticated(self) -> bool:
        return True

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


def _bind_release_locked_spot_v7_checkpoint_finality_v1(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    release: release_v7._TransactionBoundSpotV7CurrentReleaseV7,
    finality: finality_v1._CrossCheckedAuthenticatedCheckpointFinalityTransitionV1,
    exact_execution_authority_manifest_bytes: bytes,
) -> _ReleaseBoundSpotV7CheckpointFinalityV1:
    """Bind one cross-checked finality result to the exact selected release."""

    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=release,
    )
    if type(finality) is not finality_v1._CrossCheckedAuthenticatedCheckpointFinalityTransitionV1:
        raise TypeError("release-bound finality requires exact cross-checked finality")
    finality_v1._revalidate_cross_checked_transition_v1(finality)
    if type(exact_execution_authority_manifest_bytes) is not bytes:
        raise TypeError("execution authority manifest must be exact bytes")

    checked = _checked_execution_manifest(
        release=release,
        exact_execution_authority_manifest_bytes=exact_execution_authority_manifest_bytes,
    )
    policy = finality._policy
    invocation = finality._invocation_artifacts_for_operational_join_v3(policy)
    authenticated = finality._finality_for_operational_join_v3(policy)
    projection = authenticated._projection
    execution = checked.execution_manifest

    checker_manifest_sha256 = hashlib.sha256(invocation.exact_authority_manifest_bytes).digest()
    checker_executable_sha256 = bytes.fromhex(invocation.evidence.executable_sha256)
    expected_artifacts = execution._artifacts
    if checker_manifest_sha256 != expected_artifacts["checkpoint_finality_checker_manifest_sha256"]:
        raise _reject(
            "CHECKER_MANIFEST_BINDING",
            "checkpoint-finality checker manifest differs from selected release",
        )
    if (
        checker_executable_sha256
        != expected_artifacts["checkpoint_finality_checker_executable_sha256"]
    ):
        raise _reject(
            "CHECKER_EXECUTABLE_BINDING",
            "checkpoint-finality checker executable differs from selected release",
        )

    finality_policy_root = _prefixed_digest(projection.policy_root, "finality policy root")
    if finality_policy_root != execution._policies["finality_policy_root"]:
        raise _reject(
            "FINALITY_POLICY_BINDING",
            "authenticated finality policy differs from selected release",
        )
    policy._require_live_integrity()
    operational_policy_manifest_sha256 = bytes.fromhex(policy._provenance.manifest_sha256)
    if operational_policy_manifest_sha256 != execution._policies["operational_policy_root"]:
        raise _reject(
            "OPERATIONAL_POLICY_BINDING",
            "governed operational policy differs from selected release",
        )

    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=release,
    )
    result = object.__new__(_ReleaseBoundSpotV7CheckpointFinalityV1)
    values = {
        "_certificate_root": _prefixed_digest(projection.certificate_root, "certificate root"),
        "_checker_executable_sha256": checker_executable_sha256,
        "_checker_manifest_sha256": checker_manifest_sha256,
        "_cross_checked_finality": finality,
        "_epoch_id": projection.epoch_id,
        "_exact_execution_authority_manifest_bytes": (exact_execution_authority_manifest_bytes),
        "_finality_evidence_root": _prefixed_digest(
            projection.finality_evidence_root,
            "finality evidence root",
        ),
        "_finality_policy_root": finality_policy_root,
        "_identity": identity,
        "_next_checkpoint_hash": _prefixed_digest(
            projection.next_application_checkpoint_hash,
            "next checkpoint hash",
        ),
        "_next_checkpoint_sequence": projection.next_application_checkpoint_sequence,
        "_post_state_root": _prefixed_digest(projection.post_state_root, "post-state root"),
        "_prior_checkpoint_hash": _prefixed_digest(
            projection.prior_application_checkpoint_hash,
            "prior checkpoint hash",
        ),
        "_prior_checkpoint_sequence": projection.prior_application_checkpoint_sequence,
        "_proof_journal_hash": _prefixed_digest(
            projection.proof_journal_hash,
            "proof journal hash",
        ),
        "_release": release,
        "_release_candidate_id": release.current_candidate_id,
        "_release_candidate_sha256": release.current_candidate_sha256,
        "_release_revision": release.current_release_revision,
    }
    for name, value in values.items():
        object.__setattr__(result, name, value)
    object.__setattr__(result, "_seal", result)
    _revalidate_release_bound_finality_v1(result)
    return result


def _require_release_bound_finality_still_locked_v1(
    connection: sqlite3.Connection,
    *,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    finality: _ReleaseBoundSpotV7CheckpointFinalityV1,
) -> _ReleaseBoundSpotV7CheckpointFinalityV1:
    """Revalidate release currentness and all retained finality bindings."""

    if type(finality) is not _ReleaseBoundSpotV7CheckpointFinalityV1:
        raise TypeError("atomic join requires exact release-bound finality")
    if not finality._has_private_seal():
        raise TypeError("release-bound finality lacks its private seal")
    if identity != finality._identity:
        raise ValueError("release-bound finality retained a different store identity")
    release_v7._require_current_release_still_locked_v7(
        connection,
        identity=identity,
        release=finality._release,
    )
    _revalidate_release_bound_finality_v1(finality)
    return finality


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


def _revalidate_release_bound_finality_v1(
    value: _ReleaseBoundSpotV7CheckpointFinalityV1,
) -> None:
    if not value._has_private_seal():
        raise TypeError("release-bound finality lacks its private seal")
    finality_v1._revalidate_cross_checked_transition_v1(value._cross_checked_finality)
    checked = _checked_execution_manifest(
        release=value._release,
        exact_execution_authority_manifest_bytes=value._exact_execution_authority_manifest_bytes,
    )
    execution = checked.execution_manifest
    invocation = value._cross_checked_finality._invocation_artifacts_for_operational_join_v3(
        value._cross_checked_finality._policy
    )
    projection = value._cross_checked_finality._finality._projection
    observed = (
        value._release_candidate_id,
        value._release_candidate_sha256,
        value._release_revision,
        value._checker_manifest_sha256,
        value._checker_executable_sha256,
        value._epoch_id,
        value._proof_journal_hash,
        value._post_state_root,
        value._certificate_root,
        value._finality_policy_root,
        value._finality_evidence_root,
        value._prior_checkpoint_sequence,
        value._prior_checkpoint_hash,
        value._next_checkpoint_sequence,
        value._next_checkpoint_hash,
    )
    expected = (
        value._release.current_candidate_id,
        value._release.current_candidate_sha256,
        value._release.current_release_revision,
        hashlib.sha256(invocation.exact_authority_manifest_bytes).digest(),
        bytes.fromhex(invocation.evidence.executable_sha256),
        projection.epoch_id,
        _prefixed_digest(projection.proof_journal_hash, "proof journal hash"),
        _prefixed_digest(projection.post_state_root, "post-state root"),
        _prefixed_digest(projection.certificate_root, "certificate root"),
        execution._policies["finality_policy_root"],
        _prefixed_digest(projection.finality_evidence_root, "finality evidence root"),
        projection.prior_application_checkpoint_sequence,
        _prefixed_digest(
            projection.prior_application_checkpoint_hash,
            "prior checkpoint hash",
        ),
        projection.next_application_checkpoint_sequence,
        _prefixed_digest(
            projection.next_application_checkpoint_hash,
            "next checkpoint hash",
        ),
    )
    if observed != expected:
        raise ValueError("release-bound finality retained binding drift")
    if (
        value._checker_manifest_sha256
        != execution._artifacts["checkpoint_finality_checker_manifest_sha256"]
    ):
        raise ValueError("release-bound finality checker manifest drift")
    if (
        value._checker_executable_sha256
        != execution._artifacts["checkpoint_finality_checker_executable_sha256"]
    ):
        raise ValueError("release-bound finality checker executable drift")
    policy = value._cross_checked_finality._policy
    policy._require_live_integrity()
    if (
        bytes.fromhex(policy._provenance.manifest_sha256)
        != execution._policies["operational_policy_root"]
    ):
        raise ValueError("release-bound operational policy drift")


def _prefixed_digest(value: object, name: str) -> bytes:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise ValueError(f"{name} must be canonical lowercase 32-byte hex")
    decoded = bytes.fromhex(value[2:])
    if not any(decoded):
        raise ValueError(f"{name} must be nonzero")
    return decoded


def _reject(code: str, detail: str) -> SpotV7ReleaseBoundFinalityRejectV1:
    return SpotV7ReleaseBoundFinalityRejectV1(code, detail)


__all__ = ()
