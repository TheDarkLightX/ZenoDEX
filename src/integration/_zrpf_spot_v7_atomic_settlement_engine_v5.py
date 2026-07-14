"""Dormant authority-capable commit engine for Spot V7 schema V5.

The V5 engine binds every authority prerequisite into one private capability.
Its production mint is deliberately unavailable until fresh governed release
and runtime evidence exists.  The test-only mint exercises persistence while
all release, proof, runtime, settlement, and production authority claims stay
false.
"""

from __future__ import annotations

import hashlib
import sqlite3
from dataclasses import dataclass
from enum import Enum
from typing import NoReturn, SupportsIndex, cast, final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
    _seal_test_only_spot_v7_settlement_v1,
)
from src.integration._zrpf_spot_v7_operational_capability_v3 import (
    _SpotV7AtomicEconomicCommitCapabilityV3,
    _SpotV7OperationalCommitPacketV3,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    SpotV7AtomicSettlementRejectReasonV1,
    _hash_bytes,
)

MAX_SPOT_V7_V5_MANIFEST_BYTES = 4 * 1_024 * 1_024
MAX_SPOT_V7_V5_RELEASE_EVIDENCE_BYTES = 8 * 1_024 * 1_024
_MAX_U64 = (1 << 64) - 1
_PREREQUISITE_ROOT_DOMAIN_V5 = b"zenodex.zrpf.spot_v7.authority_prerequisites.v5\0"


class SpotV7OperationalStoreActivationBlockerCodeV5(Enum):
    """Typed missing conditions for the dormant V5 production mint."""

    GOVERNED_RELEASE_SELECTION_REQUIRED = (
        "spot_v7.operational_v5.governed_release_selection_required"
    )
    RELEASE_REVOCATION_POLICY_REQUIRED = "spot_v7.operational_v5.release_revocation_policy_required"
    RELEASE_ROLLBACK_PROTECTION_REQUIRED = (
        "spot_v7.operational_v5.release_rollback_protection_required"
    )
    FRESH_GOVERNED_RELEASE_EVIDENCE_REQUIRED = (
        "spot_v7.operational_v5.fresh_governed_release_evidence_required"
    )
    FRESH_GOVERNED_RUNTIME_EVIDENCE_REQUIRED = (
        "spot_v7.operational_v5.fresh_governed_runtime_evidence_required"
    )


@dataclass(frozen=True, slots=True)
class SpotV7OperationalStoreActivationBlockerV5:
    """Stable code-only blocker retained by every V5 store instance."""

    codes: tuple[SpotV7OperationalStoreActivationBlockerCodeV5, ...]

    def __post_init__(self) -> None:
        expected = (
            SpotV7OperationalStoreActivationBlockerCodeV5.GOVERNED_RELEASE_SELECTION_REQUIRED,
            SpotV7OperationalStoreActivationBlockerCodeV5.RELEASE_REVOCATION_POLICY_REQUIRED,
            SpotV7OperationalStoreActivationBlockerCodeV5.RELEASE_ROLLBACK_PROTECTION_REQUIRED,
            SpotV7OperationalStoreActivationBlockerCodeV5.FRESH_GOVERNED_RELEASE_EVIDENCE_REQUIRED,
            SpotV7OperationalStoreActivationBlockerCodeV5.FRESH_GOVERNED_RUNTIME_EVIDENCE_REQUIRED,
        )
        if self.codes != expected:
            raise ValueError("Spot V7 V5 activation blocker set is not exact")


SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5 = SpotV7OperationalStoreActivationBlockerV5(
    (
        SpotV7OperationalStoreActivationBlockerCodeV5.GOVERNED_RELEASE_SELECTION_REQUIRED,
        SpotV7OperationalStoreActivationBlockerCodeV5.RELEASE_REVOCATION_POLICY_REQUIRED,
        SpotV7OperationalStoreActivationBlockerCodeV5.RELEASE_ROLLBACK_PROTECTION_REQUIRED,
        SpotV7OperationalStoreActivationBlockerCodeV5.FRESH_GOVERNED_RELEASE_EVIDENCE_REQUIRED,
        SpotV7OperationalStoreActivationBlockerCodeV5.FRESH_GOVERNED_RUNTIME_EVIDENCE_REQUIRED,
    )
)


class SpotV7OperationalStoreActivationUnavailableV5(RuntimeError):
    """Typed fail-closed result from the sole dormant production mint."""

    code = "SPOT_V7_OPERATIONAL_STORE_V5_ACTIVATION_UNAVAILABLE"

    def __init__(self) -> None:
        self.blocker = SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5
        detail = ",".join(code.value for code in self.blocker.codes)
        super().__init__(f"{self.code}: {detail}")


@dataclass(frozen=True, slots=True)
class _SpotV7DormantAuthorityProvenanceV5:
    """Exact bytes and lifecycle facts retained by the dormant V5 lane."""

    exact_proof_verifier_manifest_bytes: bytes
    exact_runtime_manifest_bytes: bytes
    exact_release_manifest_bytes: bytes
    exact_release_evidence_bytes: bytes
    exact_authority_manifest_bytes: bytes
    release_revision: int
    release_activation_epoch: int
    release_revocation_epoch: int | None
    evaluation_epoch: int

    def __post_init__(self) -> None:
        for name in (
            "exact_proof_verifier_manifest_bytes",
            "exact_runtime_manifest_bytes",
            "exact_release_manifest_bytes",
            "exact_authority_manifest_bytes",
        ):
            _require_exact_bytes(
                getattr(self, name),
                name=name,
                maximum=MAX_SPOT_V7_V5_MANIFEST_BYTES,
            )
        _require_exact_bytes(
            self.exact_release_evidence_bytes,
            name="exact_release_evidence_bytes",
            maximum=MAX_SPOT_V7_V5_RELEASE_EVIDENCE_BYTES,
        )
        for name in (
            "release_revision",
            "release_activation_epoch",
            "evaluation_epoch",
        ):
            _require_u64(getattr(self, name), name=name)
        if self.release_revocation_epoch is not None:
            _require_u64(self.release_revocation_epoch, name="release_revocation_epoch")
            if self.release_revocation_epoch <= self.release_activation_epoch:
                raise ValueError("Spot V7 V5 release revocation must follow activation")
        if self.evaluation_epoch < self.release_activation_epoch:
            raise ValueError("Spot V7 V5 release evidence is not active yet")
        if (
            self.release_revocation_epoch is not None
            and self.evaluation_epoch >= self.release_revocation_epoch
        ):
            raise ValueError("Spot V7 V5 release evidence is revoked")

    @property
    def proof_verifier_manifest_sha256(self) -> str:
        return _sha256(self.exact_proof_verifier_manifest_bytes)

    @property
    def runtime_manifest_sha256(self) -> str:
        return _sha256(self.exact_runtime_manifest_bytes)

    @property
    def release_manifest_sha256(self) -> str:
        return _sha256(self.exact_release_manifest_bytes)

    @property
    def release_evidence_sha256(self) -> str:
        return _sha256(self.exact_release_evidence_bytes)

    @property
    def authority_manifest_sha256(self) -> str:
        return _sha256(self.exact_authority_manifest_bytes)


@dataclass(frozen=True, slots=True)
class _SpotV7DormantAuthorityPacketV5:
    operational: _SpotV7OperationalCommitPacketV3
    provenance: _SpotV7DormantAuthorityProvenanceV5

    @property
    def prerequisite_set_root(self) -> str:
        candidate = self.operational.candidate
        sealed = _seal_test_only_spot_v7_settlement_v1(candidate)
        projection = self.operational.durable_replay_packet._projection_for_history_reverification()
        roots = (
            _derive_capability_commitment(candidate),
            sealed.receipt_sha256,
            sealed.journal_sha256,
            candidate.verified_program_id,
            candidate.verified_profile_id,
            candidate.verified_program_manifest_root,
            sealed.firecracker_execution_record_sha256,
            sealed.firecracker_output_sha256,
            "0x" + self.provenance.proof_verifier_manifest_sha256,
            "0x" + self.provenance.runtime_manifest_sha256,
            "0x" + self.provenance.release_manifest_sha256,
            "0x" + self.provenance.release_evidence_sha256,
            "0x" + self.provenance.authority_manifest_sha256,
            self.operational.data_availability.base.certificate_root,
            self.operational.finality.certificate_root,
            projection.replay_material_root,
        )
        body = b"".join(_hash_bytes(value, name="V5 prerequisite root") for value in roots)
        body += self.provenance.release_revision.to_bytes(8, "big")
        body += self.provenance.release_activation_epoch.to_bytes(8, "big")
        body += (
            b"\x00"
            if self.provenance.release_revocation_epoch is None
            else b"\x01" + self.provenance.release_revocation_epoch.to_bytes(8, "big")
        )
        body += self.provenance.evaluation_epoch.to_bytes(8, "big")
        return "0x" + hashlib.sha256(_PREREQUISITE_ROOT_DOMAIN_V5 + body).hexdigest()


class _DormantSpotV7AuthorityPrerequisiteSealV5:
    __slots__ = ()


_DORMANT_SPOT_V7_AUTHORITY_PREREQUISITE_SEAL_V5 = _DormantSpotV7AuthorityPrerequisiteSealV5()


class _NonTransferableDormantSpotV7AuthorityPrerequisitesV5:
    __slots__ = ()

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("Spot V7 V5 prerequisites cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("Spot V7 V5 prerequisites cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("Spot V7 V5 prerequisites cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("Spot V7 V5 prerequisites cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("Spot V7 V5 prerequisites cannot be serialized")


@final
class _DormantSpotV7AuthorityPrerequisitesV5(_NonTransferableDormantSpotV7AuthorityPrerequisitesV5):
    """Private exact prerequisite bundle with every authority claim false."""

    _operational: _SpotV7AtomicEconomicCommitCapabilityV3
    _provenance: _SpotV7DormantAuthorityProvenanceV5
    _seal: _DormantSpotV7AuthorityPrerequisiteSealV5

    __slots__ = ("_operational", "_provenance", "_seal")

    def __init__(
        self,
        *,
        operational: _SpotV7AtomicEconomicCommitCapabilityV3,
        provenance: _SpotV7DormantAuthorityProvenanceV5,
        seal: _DormantSpotV7AuthorityPrerequisiteSealV5,
    ) -> None:
        if seal is not _DORMANT_SPOT_V7_AUTHORITY_PREREQUISITE_SEAL_V5:
            raise TypeError("Spot V7 V5 prerequisites require their private seal")
        if type(operational) is not _SpotV7AtomicEconomicCommitCapabilityV3:
            raise TypeError("Spot V7 V5 prerequisites require exact operational V3")
        if not operational._has_private_seal():
            raise TypeError("Spot V7 V5 prerequisites require sealed operational V3")
        if type(provenance) is not _SpotV7DormantAuthorityProvenanceV5:
            raise TypeError("Spot V7 V5 prerequisites require exact provenance V5")
        packet = operational._packet_for_atomic_store_v4()
        _validate_packet_provenance(packet, provenance)
        object.__setattr__(self, "_operational", operational)
        object.__setattr__(self, "_provenance", provenance)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("Spot V7 V5 prerequisites cannot be subclassed")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _DORMANT_SPOT_V7_AUTHORITY_PREREQUISITE_SEAL_V5

    def _packet_for_atomic_store_v5(self) -> _SpotV7DormantAuthorityPacketV5:
        if not self._has_private_seal():
            raise TypeError("Spot V7 V5 prerequisites lack their private V5 prerequisite seal")
        operational = self._operational._packet_for_atomic_store_v4()
        _validate_packet_provenance(operational, self._provenance)
        return _SpotV7DormantAuthorityPacketV5(operational, self._provenance)

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _seal_test_only_dormant_spot_v7_authority_prerequisites_v5(
    *,
    operational_capability_v3: object,
    exact_proof_verifier_manifest_bytes: bytes,
    exact_runtime_manifest_bytes: bytes,
    exact_release_manifest_bytes: bytes,
    exact_release_evidence_bytes: bytes,
    exact_authority_manifest_bytes: bytes,
    release_revision: int,
    release_activation_epoch: int,
    release_revocation_epoch: int | None,
    evaluation_epoch: int,
) -> _DormantSpotV7AuthorityPrerequisitesV5:
    """Exercise dormant persistence without creating any authority claim."""

    if type(operational_capability_v3) is not _SpotV7AtomicEconomicCommitCapabilityV3:
        raise TypeError("test-only V5 sealer requires exact operational V3")
    operational = cast(
        _SpotV7AtomicEconomicCommitCapabilityV3,
        operational_capability_v3,
    )
    if not operational._has_private_seal():
        raise TypeError("test-only V5 sealer requires sealed operational V3")
    provenance = _SpotV7DormantAuthorityProvenanceV5(
        exact_proof_verifier_manifest_bytes=exact_proof_verifier_manifest_bytes,
        exact_runtime_manifest_bytes=exact_runtime_manifest_bytes,
        exact_release_manifest_bytes=exact_release_manifest_bytes,
        exact_release_evidence_bytes=exact_release_evidence_bytes,
        exact_authority_manifest_bytes=exact_authority_manifest_bytes,
        release_revision=release_revision,
        release_activation_epoch=release_activation_epoch,
        release_revocation_epoch=release_revocation_epoch,
        evaluation_epoch=evaluation_epoch,
    )
    return _DormantSpotV7AuthorityPrerequisitesV5(
        operational=operational,
        provenance=provenance,
        seal=_DORMANT_SPOT_V7_AUTHORITY_PREREQUISITE_SEAL_V5,
    )


def _require_fresh_governed_release_and_runtime_evidence_v5(
    _untrusted_evidence: object,
) -> NoReturn:
    """Sole production activation seam, intentionally unavailable today."""

    raise SpotV7OperationalStoreActivationUnavailableV5()


def _authority_v5_reject_reason_locked(
    connection: sqlite3.Connection,
    packet: _SpotV7DormantAuthorityPacketV5,
) -> SpotV7AtomicSettlementRejectReasonV1 | None:
    duplicate = connection.execute(
        "SELECT 1 FROM spot_v7_authority_provenance_v5 WHERE prerequisite_set_root = ?",
        (_hash_bytes(packet.prerequisite_set_root, name="V5 prerequisite root"),),
    ).fetchone()
    if duplicate is not None:
        return SpotV7AtomicSettlementRejectReasonV1.DUPLICATE_SETTLEMENT_PLAN
    return None


def _persist_authority_provenance_v5(
    connection: sqlite3.Connection,
    packet: _SpotV7DormantAuthorityPacketV5,
) -> None:
    operational = packet.operational
    candidate = operational.candidate
    sealed = _seal_test_only_spot_v7_settlement_v1(candidate)
    provenance = packet.provenance
    replay = operational.durable_replay_packet._projection_for_history_reverification()
    connection.execute(
        """
        INSERT INTO spot_v7_authority_provenance_v5 (
            settlement_commitment, prerequisite_set_root,
            proof_receipt_sha256, proof_journal_sha256,
            verified_program_id, verified_profile_id,
            verified_program_manifest_root, proof_verifier_manifest_sha256,
            runtime_execution_record_sha256, runtime_output_sha256,
            runtime_manifest_sha256, release_manifest_sha256,
            release_evidence_sha256, authority_manifest_sha256,
            da_certificate_root, finality_certificate_root, replay_material_root,
            exact_proof_verifier_manifest, exact_runtime_manifest,
            exact_release_manifest, exact_release_evidence,
            exact_authority_manifest, release_revision_be,
            release_activation_epoch_be, release_revocation_epoch_be,
            evaluation_epoch_be, current_release_evidence_verified,
            proof_receipt_authority, runtime_authority, release_authority,
            settlement_authority, production_authority, activation_blocker
        ) VALUES (
            ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
            ?, ?, ?, ?, 0, 0, 0, 0, 0, 0, ?
        )
        """,
        (
            _hash_bytes(
                _derive_capability_commitment(candidate),
                name="V5 settlement commitment",
            ),
            _hash_bytes(packet.prerequisite_set_root, name="V5 prerequisite root"),
            _hash_bytes(sealed.receipt_sha256, name="V5 proof receipt"),
            _hash_bytes(sealed.journal_sha256, name="V5 proof journal"),
            _hash_bytes(candidate.verified_program_id, name="V5 program ID"),
            _hash_bytes(candidate.verified_profile_id, name="V5 profile ID"),
            _hash_bytes(candidate.verified_program_manifest_root, name="V5 program manifest"),
            bytes.fromhex(provenance.proof_verifier_manifest_sha256),
            _hash_bytes(
                sealed.firecracker_execution_record_sha256,
                name="V5 runtime execution record",
            ),
            _hash_bytes(sealed.firecracker_output_sha256, name="V5 runtime output"),
            bytes.fromhex(provenance.runtime_manifest_sha256),
            bytes.fromhex(provenance.release_manifest_sha256),
            bytes.fromhex(provenance.release_evidence_sha256),
            bytes.fromhex(provenance.authority_manifest_sha256),
            _hash_bytes(
                operational.data_availability.base.certificate_root,
                name="V5 DA certificate",
            ),
            _hash_bytes(operational.finality.certificate_root, name="V5 finality certificate"),
            _hash_bytes(replay.replay_material_root, name="V5 replay material"),
            provenance.exact_proof_verifier_manifest_bytes,
            provenance.exact_runtime_manifest_bytes,
            provenance.exact_release_manifest_bytes,
            provenance.exact_release_evidence_bytes,
            provenance.exact_authority_manifest_bytes,
            provenance.release_revision.to_bytes(8, "big"),
            provenance.release_activation_epoch.to_bytes(8, "big"),
            None
            if provenance.release_revocation_epoch is None
            else provenance.release_revocation_epoch.to_bytes(8, "big"),
            provenance.evaluation_epoch.to_bytes(8, "big"),
            _activation_blocker_text(),
        ),
    )


def _stored_authority_provenance_matches_v5(
    connection: sqlite3.Connection,
    packet: _SpotV7DormantAuthorityPacketV5,
) -> bool:
    commitment = _hash_bytes(
        _derive_capability_commitment(packet.operational.candidate),
        name="V5 stored settlement commitment",
    )
    row = connection.execute(
        "SELECT * FROM spot_v7_authority_provenance_v5 WHERE settlement_commitment = ?",
        (commitment,),
    ).fetchone()
    if row is None:
        return False
    try:
        _validate_authority_provenance_row_v5(row, packet)
    except (TypeError, ValueError):
        return False
    return True


def _validate_authority_provenance_row_v5(
    row: sqlite3.Row,
    packet: _SpotV7DormantAuthorityPacketV5,
) -> None:
    operational = packet.operational
    candidate = operational.candidate
    sealed = _seal_test_only_spot_v7_settlement_v1(candidate)
    provenance = packet.provenance
    replay = operational.durable_replay_packet._projection_for_history_reverification()
    expected_blobs = {
        "settlement_commitment": _hash_bytes(
            _derive_capability_commitment(candidate), name="V5 stored commitment"
        ),
        "prerequisite_set_root": _hash_bytes(
            packet.prerequisite_set_root, name="V5 stored prerequisite root"
        ),
        "proof_receipt_sha256": _hash_bytes(sealed.receipt_sha256, name="V5 receipt"),
        "proof_journal_sha256": _hash_bytes(sealed.journal_sha256, name="V5 journal"),
        "verified_program_id": _hash_bytes(candidate.verified_program_id, name="V5 program"),
        "verified_profile_id": _hash_bytes(candidate.verified_profile_id, name="V5 profile"),
        "verified_program_manifest_root": _hash_bytes(
            candidate.verified_program_manifest_root, name="V5 program manifest"
        ),
        "proof_verifier_manifest_sha256": bytes.fromhex(provenance.proof_verifier_manifest_sha256),
        "runtime_execution_record_sha256": _hash_bytes(
            sealed.firecracker_execution_record_sha256, name="V5 runtime execution"
        ),
        "runtime_output_sha256": _hash_bytes(
            sealed.firecracker_output_sha256, name="V5 runtime output"
        ),
        "runtime_manifest_sha256": bytes.fromhex(provenance.runtime_manifest_sha256),
        "release_manifest_sha256": bytes.fromhex(provenance.release_manifest_sha256),
        "release_evidence_sha256": bytes.fromhex(provenance.release_evidence_sha256),
        "authority_manifest_sha256": bytes.fromhex(provenance.authority_manifest_sha256),
        "da_certificate_root": _hash_bytes(
            operational.data_availability.base.certificate_root, name="V5 DA"
        ),
        "finality_certificate_root": _hash_bytes(
            operational.finality.certificate_root, name="V5 finality"
        ),
        "replay_material_root": _hash_bytes(replay.replay_material_root, name="V5 replay"),
        "exact_proof_verifier_manifest": provenance.exact_proof_verifier_manifest_bytes,
        "exact_runtime_manifest": provenance.exact_runtime_manifest_bytes,
        "exact_release_manifest": provenance.exact_release_manifest_bytes,
        "exact_release_evidence": provenance.exact_release_evidence_bytes,
        "exact_authority_manifest": provenance.exact_authority_manifest_bytes,
        "release_revision_be": provenance.release_revision.to_bytes(8, "big"),
        "release_activation_epoch_be": provenance.release_activation_epoch.to_bytes(8, "big"),
        "evaluation_epoch_be": provenance.evaluation_epoch.to_bytes(8, "big"),
    }
    for field, expected in expected_blobs.items():
        if bytes(row[field]) != expected:
            raise ValueError(f"Spot V7 V5 authority provenance mismatch: {field}")
    observed_revocation = (
        None
        if row["release_revocation_epoch_be"] is None
        else int.from_bytes(bytes(row["release_revocation_epoch_be"]), "big")
    )
    if observed_revocation != provenance.release_revocation_epoch:
        raise ValueError("Spot V7 V5 release revocation mismatch")
    false_fields = (
        "current_release_evidence_verified",
        "proof_receipt_authority",
        "runtime_authority",
        "release_authority",
        "settlement_authority",
        "production_authority",
    )
    if any(int(row[field]) != 0 for field in false_fields):
        raise ValueError("Spot V7 V5 authority nonclaim mismatch")
    if str(row["activation_blocker"]) != _activation_blocker_text():
        raise ValueError("Spot V7 V5 activation blocker mismatch")


def _validate_packet_provenance(
    packet: _SpotV7OperationalCommitPacketV3,
    provenance: _SpotV7DormantAuthorityProvenanceV5,
) -> None:
    if provenance.evaluation_epoch != packet.candidate.epoch_id:
        raise ValueError("Spot V7 V5 release evaluation epoch differs from candidate")


def _activation_blocker_text() -> str:
    return ",".join(code.value for code in SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5.codes)


def _require_exact_bytes(value: object, *, name: str, maximum: int) -> bytes:
    if type(value) is not bytes or not value or len(value) > maximum:
        raise ValueError(f"{name} must be nonempty bounded exact bytes")
    return value


def _require_u64(value: object, *, name: str) -> int:
    if type(value) is not int or not 0 <= value <= _MAX_U64:
        raise ValueError(f"{name} must be a u64")
    return value


def _sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


__all__ = [
    "SPOT_V7_OPERATIONAL_STORE_ACTIVATION_BLOCKER_V5",
    "SpotV7OperationalStoreActivationBlockerCodeV5",
    "SpotV7OperationalStoreActivationBlockerV5",
    "SpotV7OperationalStoreActivationUnavailableV5",
]
