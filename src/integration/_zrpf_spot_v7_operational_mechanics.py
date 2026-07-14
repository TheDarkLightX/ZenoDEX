"""Authority-false combined Spot V7 DA/finality store mechanics.

This module mirrors the fixed hash contracts needed to exercise one atomic
SQLite transaction.  It does not mint governed V7, DA, external-finality,
settlement, release, or production authority.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _TestOnlySealedSpotV7SettlementV1,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    MAX_U64,
    _hash_bytes,
    _require_uint,
    _root_bytes_allow_zero,
    _sha256_prefixed,
)

_FULL_BLOB_DATA_ROOT_DOMAIN_V1 = b"zenodex.zrpf.full_blob_da.data_root.v1"
_FULL_BLOB_CHUNK_DOMAIN_V1 = b"zenodex.zrpf.full_blob_da.chunk.v1"
_FULL_BLOB_CHUNK_ROOT_DOMAIN_V1 = b"zenodex.zrpf.full_blob_da.chunk_root.v1"
_FULL_BLOB_CERTIFICATE_ROOT_DOMAIN_V1 = (
    b"zenodex.zrpf.full_blob_da.certificate_root.v1"
)
_FULL_BLOB_POLICY_ROOT_DOMAIN_V1 = b"zenodex.zrpf.local_full_blob_policy.root.v1"
_FINALITY_POLICY_ROOT_DOMAIN_V2 = b"zenodex.zrpf.checkpoint_finality.policy_root.v2"
_FINALITY_CERTIFICATE_ROOT_DOMAIN_V2 = (
    b"zenodex.zrpf.checkpoint_finality.certificate_root.v2"
)

FULL_BLOB_CHUNK_BYTES_V1 = 65_536
MAX_FULL_BLOB_BYTES_V1 = 8 * 1_024 * 1_024
MAX_FULL_BLOB_CERTIFICATE_BYTES_V1 = 512
MAX_FINALITY_CERTIFICATE_BYTES_V2 = 576
MAX_FINALITY_EVIDENCE_BYTES_V2 = 1 * 1_024 * 1_024


@dataclass(frozen=True, slots=True)
class _TestOnlySpotV7OperationalPolicyV1:
    application_id: str
    chain_or_domain_id: str
    data_schema_id: str
    storage_policy_hash: str
    minimum_retention_epochs: int
    minimum_remaining_epochs: int
    maximum_blob_bytes: int
    finality_network_id: str
    finality_protocol_id: str
    external_finality_policy_hash: str
    finality_verifier_set_root: str
    genesis_application_checkpoint_sequence: int
    genesis_application_checkpoint_hash: str

    def __post_init__(self) -> None:
        for name in (
            "application_id",
            "chain_or_domain_id",
            "data_schema_id",
            "storage_policy_hash",
            "finality_network_id",
            "finality_protocol_id",
            "external_finality_policy_hash",
            "finality_verifier_set_root",
        ):
            _hash_bytes(getattr(self, name), name=f"test-only operational policy {name}")
        _root_bytes_allow_zero(
            self.genesis_application_checkpoint_hash,
            name="test-only operational policy genesis_application_checkpoint_hash",
        )
        for name in (
            "minimum_retention_epochs",
            "minimum_remaining_epochs",
            "genesis_application_checkpoint_sequence",
        ):
            _require_uint(getattr(self, name), name=name, maximum=MAX_U64)
        _require_uint(
            self.maximum_blob_bytes,
            name="maximum_blob_bytes",
            minimum=1,
            maximum=MAX_FULL_BLOB_BYTES_V1,
        )

    @property
    def full_blob_policy_root(self) -> str:
        return _domain_hash(
            _FULL_BLOB_POLICY_ROOT_DOMAIN_V1,
            b"".join(
                (
                    (1).to_bytes(2, "big"),
                    _hash_bytes(self.application_id, name="policy application"),
                    _hash_bytes(self.chain_or_domain_id, name="policy domain"),
                    _hash_bytes(self.data_schema_id, name="policy schema"),
                    _hash_bytes(self.storage_policy_hash, name="storage policy"),
                    self.minimum_retention_epochs.to_bytes(8, "big"),
                    self.minimum_remaining_epochs.to_bytes(8, "big"),
                    self.maximum_blob_bytes.to_bytes(8, "big"),
                )
            ),
        )

    @property
    def checkpoint_finality_policy_root(self) -> str:
        return _domain_hash(
            _FINALITY_POLICY_ROOT_DOMAIN_V2,
            b"".join(
                (
                    (2).to_bytes(2, "big"),
                    _hash_bytes(self.application_id, name="policy application"),
                    _hash_bytes(self.chain_or_domain_id, name="policy domain"),
                    _hash_bytes(self.finality_network_id, name="finality network"),
                    _hash_bytes(self.finality_protocol_id, name="finality protocol"),
                    _hash_bytes(
                        self.external_finality_policy_hash,
                        name="external finality policy",
                    ),
                    _hash_bytes(
                        self.finality_verifier_set_root,
                        name="finality verifier set",
                    ),
                    self.genesis_application_checkpoint_sequence.to_bytes(8, "big"),
                    _root_bytes_allow_zero(
                        self.genesis_application_checkpoint_hash,
                        name="genesis checkpoint hash",
                    ),
                )
            ),
        )

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


@dataclass(frozen=True, slots=True)
class _TestOnlyFullBlobArtifactsV1:
    epoch_id: int
    data_root: str
    chunk_count: int
    chunk_root: str
    retention_through_epoch: int
    certificate_root: str
    policy_root: str
    checked_epoch: int
    exact_blob_bytes: bytes
    exact_certificate_bytes: bytes

    def __post_init__(self) -> None:
        for name in ("data_root", "chunk_root", "certificate_root", "policy_root"):
            _hash_bytes(getattr(self, name), name=f"test-only full-blob {name}")
        for name in (
            "epoch_id",
            "chunk_count",
            "retention_through_epoch",
            "checked_epoch",
        ):
            _require_uint(getattr(self, name), name=name, maximum=MAX_U64)
        _bounded_bytes(
            self.exact_blob_bytes,
            name="full blob",
            maximum=MAX_FULL_BLOB_BYTES_V1,
        )
        _bounded_bytes(
            self.exact_certificate_bytes,
            name="full-blob certificate",
            maximum=MAX_FULL_BLOB_CERTIFICATE_BYTES_V1,
        )

    @property
    def blob_sha256(self) -> str:
        return _sha256_prefixed(self.exact_blob_bytes)

    @property
    def certificate_sha256(self) -> str:
        return _sha256_prefixed(self.exact_certificate_bytes)


@dataclass(frozen=True, slots=True)
class _TestOnlyCheckpointFinalityArtifactsV2:
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
    exact_certificate_bytes: bytes
    exact_finality_evidence_bytes: bytes

    def __post_init__(self) -> None:
        for name in (
            "proof_journal_hash",
            "post_state_root",
            "policy_root",
            "certificate_root",
            "finality_evidence_root",
            "next_application_checkpoint_hash",
        ):
            _hash_bytes(getattr(self, name), name=f"test-only finality {name}")
        _root_bytes_allow_zero(
            self.prior_application_checkpoint_hash,
            name="test-only finality prior_application_checkpoint_hash",
        )
        for name in (
            "epoch_id",
            "prior_application_checkpoint_sequence",
            "next_application_checkpoint_sequence",
        ):
            _require_uint(getattr(self, name), name=name, maximum=MAX_U64)
        if self.prior_application_checkpoint_sequence == MAX_U64:
            raise ValueError("test-only finality prior sequence overflows")
        if (
            self.next_application_checkpoint_sequence
            != self.prior_application_checkpoint_sequence + 1
        ):
            raise ValueError("test-only finality cursor is not an exact successor")
        _bounded_bytes(
            self.exact_certificate_bytes,
            name="finality certificate",
            maximum=MAX_FINALITY_CERTIFICATE_BYTES_V2,
        )
        _bounded_bytes(
            self.exact_finality_evidence_bytes,
            name="finality evidence",
            maximum=MAX_FINALITY_EVIDENCE_BYTES_V2,
        )
        if _sha256_prefixed(self.exact_finality_evidence_bytes) != self.finality_evidence_root:
            raise ValueError("test-only finality evidence root mismatch")

    @property
    def certificate_sha256(self) -> str:
        return _sha256_prefixed(self.exact_certificate_bytes)

    @property
    def evidence_sha256(self) -> str:
        return _sha256_prefixed(self.exact_finality_evidence_bytes)


@dataclass(frozen=True, slots=True)
class _TestOnlySpotV7OperationalCommitInputV1:
    settlement: _TestOnlySealedSpotV7SettlementV1
    policy: _TestOnlySpotV7OperationalPolicyV1
    data_availability: _TestOnlyFullBlobArtifactsV1
    finality: _TestOnlyCheckpointFinalityArtifactsV2


class _TestOnlyOperationalCommitSealV1:
    __slots__ = ()


_TEST_ONLY_OPERATIONAL_COMMIT_SEAL_V1 = _TestOnlyOperationalCommitSealV1()


@final
class _TestOnlySpotV7OperationalCommitV1:
    """Non-transferable authority-false packet for atomic mechanics tests."""

    __slots__ = ("_input", "_seal")

    _input: _TestOnlySpotV7OperationalCommitInputV1
    _seal: _TestOnlyOperationalCommitSealV1

    def __init__(
        self,
        value: _TestOnlySpotV7OperationalCommitInputV1,
        *,
        seal: _TestOnlyOperationalCommitSealV1,
    ) -> None:
        if type(value) is not _TestOnlySpotV7OperationalCommitInputV1:
            raise TypeError("test-only operational commit input has the wrong type")
        if seal is not _TEST_ONLY_OPERATIONAL_COMMIT_SEAL_V1:
            raise TypeError("test-only operational commit requires the module-private seal")
        _validate_test_only_operational_input(value)
        object.__setattr__(self, "_input", value)
        object.__setattr__(self, "_seal", seal)

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("test-only operational commit cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("test-only operational commit cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("test-only operational commit cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("test-only operational commit cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("test-only operational commit cannot be serialized")

    def _has_private_test_seal(self) -> bool:
        return getattr(self, "_seal", None) is _TEST_ONLY_OPERATIONAL_COMMIT_SEAL_V1

    def _candidate_for_store(self) -> _TestOnlySealedSpotV7SettlementV1:
        if not self._has_private_test_seal():
            raise TypeError("test-only operational commit lacks its private seal")
        _validate_test_only_operational_input(self._input)
        return self._input.settlement

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _seal_test_only_spot_v7_operational_commit_v1(
    value: _TestOnlySpotV7OperationalCommitInputV1,
) -> _TestOnlySpotV7OperationalCommitV1:
    return _TestOnlySpotV7OperationalCommitV1(
        value,
        seal=_TEST_ONLY_OPERATIONAL_COMMIT_SEAL_V1,
    )


def _derive_test_only_full_blob_artifacts_v1(
    *,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    epoch_id: int,
    checked_epoch: int,
    retention_through_epoch: int,
    exact_blob_bytes: bytes,
    exact_certificate_bytes: bytes,
) -> _TestOnlyFullBlobArtifactsV1:
    """Mirror the Rust V1 roots and exact local policy checks."""

    if type(policy) is not _TestOnlySpotV7OperationalPolicyV1:
        raise TypeError("policy must be exact test-only operational policy")
    _bounded_bytes(exact_blob_bytes, name="full blob", maximum=policy.maximum_blob_bytes)
    _require_retention(policy, epoch_id, checked_epoch, retention_through_epoch)
    data_root = _full_blob_data_root_v1(exact_blob_bytes)
    chunk_count, chunk_root = _full_blob_chunk_root_v1(exact_blob_bytes)
    certificate_root = _full_blob_certificate_root_v1(
        policy=policy,
        epoch_id=epoch_id,
        data_root=data_root,
        blob_length=len(exact_blob_bytes),
        chunk_count=chunk_count,
        chunk_root=chunk_root,
        retention_through_epoch=retention_through_epoch,
    )
    expected_certificate = _encode_full_blob_certificate_v1(
        policy=policy,
        epoch_id=epoch_id,
        data_root=data_root,
        blob_length=len(exact_blob_bytes),
        chunk_count=chunk_count,
        chunk_root=chunk_root,
        retention_through_epoch=retention_through_epoch,
        certificate_root=certificate_root,
    )
    if exact_certificate_bytes != expected_certificate:
        raise ValueError("test-only full-blob certificate bytes are not canonical")
    return _TestOnlyFullBlobArtifactsV1(
        epoch_id=epoch_id,
        data_root=data_root,
        chunk_count=chunk_count,
        chunk_root=chunk_root,
        retention_through_epoch=retention_through_epoch,
        certificate_root=certificate_root,
        policy_root=policy.full_blob_policy_root,
        checked_epoch=checked_epoch,
        exact_blob_bytes=exact_blob_bytes,
        exact_certificate_bytes=exact_certificate_bytes,
    )


def _build_test_only_full_blob_artifacts_v1(
    *,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    epoch_id: int,
    checked_epoch: int,
    retention_through_epoch: int,
    exact_blob_bytes: bytes,
) -> _TestOnlyFullBlobArtifactsV1:
    """Build canonical certificate bytes for authority-false store tests."""

    if type(policy) is not _TestOnlySpotV7OperationalPolicyV1:
        raise TypeError("policy must be exact test-only operational policy")
    _bounded_bytes(exact_blob_bytes, name="full blob", maximum=policy.maximum_blob_bytes)
    _require_retention(policy, epoch_id, checked_epoch, retention_through_epoch)
    data_root = _full_blob_data_root_v1(exact_blob_bytes)
    chunk_count, chunk_root = _full_blob_chunk_root_v1(exact_blob_bytes)
    certificate_root = _full_blob_certificate_root_v1(
        policy=policy,
        epoch_id=epoch_id,
        data_root=data_root,
        blob_length=len(exact_blob_bytes),
        chunk_count=chunk_count,
        chunk_root=chunk_root,
        retention_through_epoch=retention_through_epoch,
    )
    certificate = _encode_full_blob_certificate_v1(
        policy=policy,
        epoch_id=epoch_id,
        data_root=data_root,
        blob_length=len(exact_blob_bytes),
        chunk_count=chunk_count,
        chunk_root=chunk_root,
        retention_through_epoch=retention_through_epoch,
        certificate_root=certificate_root,
    )
    return _derive_test_only_full_blob_artifacts_v1(
        policy=policy,
        epoch_id=epoch_id,
        checked_epoch=checked_epoch,
        retention_through_epoch=retention_through_epoch,
        exact_blob_bytes=exact_blob_bytes,
        exact_certificate_bytes=certificate,
    )


def _derive_test_only_checkpoint_finality_artifacts_v2(
    *,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    settlement: _TestOnlySealedSpotV7SettlementV1,
    prior_application_checkpoint_sequence: int,
    prior_application_checkpoint_hash: str,
    next_application_checkpoint_hash: str,
    exact_certificate_bytes: bytes,
    exact_finality_evidence_bytes: bytes,
) -> _TestOnlyCheckpointFinalityArtifactsV2:
    """Mirror V2 roots for a proof-neutral, authority-false finality packet."""

    if type(policy) is not _TestOnlySpotV7OperationalPolicyV1:
        raise TypeError("policy must be exact test-only operational policy")
    if type(settlement) is not _TestOnlySealedSpotV7SettlementV1:
        raise TypeError("settlement must be exact test-only sealed candidate")
    if not settlement._has_private_test_seal():
        raise TypeError("settlement lacks its private test-only seal")
    candidate = settlement._input
    next_sequence = prior_application_checkpoint_sequence + 1
    if next_sequence > MAX_U64:
        raise ValueError("test-only finality sequence overflow")
    evidence_root = _sha256_prefixed(exact_finality_evidence_bytes)
    policy_root = policy.checkpoint_finality_policy_root
    certificate_root = _finality_certificate_root_v2(
        policy=policy,
        epoch_id=candidate.epoch_id,
        proof_journal_hash=settlement.journal_sha256,
        post_state_root=candidate.post_state_root,
        sequence=next_sequence,
        checkpoint_hash=next_application_checkpoint_hash,
        parent_hash=prior_application_checkpoint_hash,
        evidence_root=evidence_root,
        policy_root=policy_root,
    )
    expected_certificate = _encode_checkpoint_finality_certificate_v2(
        policy=policy,
        epoch_id=candidate.epoch_id,
        proof_journal_hash=settlement.journal_sha256,
        post_state_root=candidate.post_state_root,
        sequence=next_sequence,
        checkpoint_hash=next_application_checkpoint_hash,
        parent_hash=prior_application_checkpoint_hash,
        evidence_root=evidence_root,
        policy_root=policy_root,
        certificate_root=certificate_root,
    )
    if exact_certificate_bytes != expected_certificate:
        raise ValueError("test-only checkpoint-finality certificate bytes are not canonical")
    return _TestOnlyCheckpointFinalityArtifactsV2(
        epoch_id=candidate.epoch_id,
        proof_journal_hash=settlement.journal_sha256,
        post_state_root=candidate.post_state_root,
        policy_root=policy_root,
        certificate_root=certificate_root,
        finality_evidence_root=evidence_root,
        prior_application_checkpoint_sequence=prior_application_checkpoint_sequence,
        prior_application_checkpoint_hash=prior_application_checkpoint_hash,
        next_application_checkpoint_sequence=next_sequence,
        next_application_checkpoint_hash=next_application_checkpoint_hash,
        exact_certificate_bytes=exact_certificate_bytes,
        exact_finality_evidence_bytes=exact_finality_evidence_bytes,
    )


def _build_test_only_checkpoint_finality_artifacts_v2(
    *,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    settlement: _TestOnlySealedSpotV7SettlementV1,
    prior_application_checkpoint_sequence: int,
    prior_application_checkpoint_hash: str,
    next_application_checkpoint_hash: str,
    exact_finality_evidence_bytes: bytes,
) -> _TestOnlyCheckpointFinalityArtifactsV2:
    """Build canonical certificate bytes for authority-false store tests."""

    if type(policy) is not _TestOnlySpotV7OperationalPolicyV1:
        raise TypeError("policy must be exact test-only operational policy")
    if type(settlement) is not _TestOnlySealedSpotV7SettlementV1:
        raise TypeError("settlement must be exact test-only sealed candidate")
    if not settlement._has_private_test_seal():
        raise TypeError("settlement lacks its private test-only seal")
    _require_uint(
        prior_application_checkpoint_sequence,
        name="prior_application_checkpoint_sequence",
        maximum=MAX_U64,
    )
    if prior_application_checkpoint_sequence == MAX_U64:
        raise ValueError("test-only finality sequence overflow")
    _root_bytes_allow_zero(
        prior_application_checkpoint_hash,
        name="prior application checkpoint hash",
    )
    _hash_bytes(
        next_application_checkpoint_hash,
        name="next application checkpoint hash",
    )
    _bounded_bytes(
        exact_finality_evidence_bytes,
        name="finality evidence",
        maximum=MAX_FINALITY_EVIDENCE_BYTES_V2,
    )
    candidate = settlement._input
    sequence = prior_application_checkpoint_sequence + 1
    evidence_root = _sha256_prefixed(exact_finality_evidence_bytes)
    policy_root = policy.checkpoint_finality_policy_root
    certificate_root = _finality_certificate_root_v2(
        policy=policy,
        epoch_id=candidate.epoch_id,
        proof_journal_hash=settlement.journal_sha256,
        post_state_root=candidate.post_state_root,
        sequence=sequence,
        checkpoint_hash=next_application_checkpoint_hash,
        parent_hash=prior_application_checkpoint_hash,
        evidence_root=evidence_root,
        policy_root=policy_root,
    )
    certificate = _encode_checkpoint_finality_certificate_v2(
        policy=policy,
        epoch_id=candidate.epoch_id,
        proof_journal_hash=settlement.journal_sha256,
        post_state_root=candidate.post_state_root,
        sequence=sequence,
        checkpoint_hash=next_application_checkpoint_hash,
        parent_hash=prior_application_checkpoint_hash,
        evidence_root=evidence_root,
        policy_root=policy_root,
        certificate_root=certificate_root,
    )
    return _derive_test_only_checkpoint_finality_artifacts_v2(
        policy=policy,
        settlement=settlement,
        prior_application_checkpoint_sequence=prior_application_checkpoint_sequence,
        prior_application_checkpoint_hash=prior_application_checkpoint_hash,
        next_application_checkpoint_hash=next_application_checkpoint_hash,
        exact_certificate_bytes=certificate,
        exact_finality_evidence_bytes=exact_finality_evidence_bytes,
    )


def _validate_test_only_operational_input(
    value: _TestOnlySpotV7OperationalCommitInputV1,
) -> None:
    if type(value.settlement) is not _TestOnlySealedSpotV7SettlementV1:
        raise TypeError("operational input requires exact test-only settlement")
    if not value.settlement._has_private_test_seal():
        raise TypeError("operational input settlement lacks its private seal")
    if type(value.policy) is not _TestOnlySpotV7OperationalPolicyV1:
        raise TypeError("operational input policy has the wrong type")
    if type(value.data_availability) is not _TestOnlyFullBlobArtifactsV1:
        raise TypeError("operational input DA artifacts have the wrong type")
    if type(value.finality) is not _TestOnlyCheckpointFinalityArtifactsV2:
        raise TypeError("operational input finality artifacts have the wrong type")
    candidate = value.settlement._input
    checks = (
        value.policy.application_id == candidate.application_id,
        value.policy.chain_or_domain_id == candidate.chain_or_domain_id,
        value.data_availability.epoch_id == candidate.epoch_id,
        value.data_availability.data_root == candidate.data_root,
        value.data_availability.certificate_root
        == candidate.data_availability_certificate_root,
        value.data_availability.policy_root == value.policy.full_blob_policy_root,
        value.finality.epoch_id == candidate.epoch_id,
        value.finality.proof_journal_hash == value.settlement.journal_sha256,
        value.finality.post_state_root == candidate.post_state_root,
        value.finality.policy_root == value.policy.checkpoint_finality_policy_root,
    )
    if not all(checks):
        raise ValueError("test-only operational input cross-binding mismatch")
    expected_da = _derive_test_only_full_blob_artifacts_v1(
        policy=value.policy,
        epoch_id=value.data_availability.epoch_id,
        checked_epoch=value.data_availability.checked_epoch,
        retention_through_epoch=value.data_availability.retention_through_epoch,
        exact_blob_bytes=value.data_availability.exact_blob_bytes,
        exact_certificate_bytes=value.data_availability.exact_certificate_bytes,
    )
    if expected_da != value.data_availability:
        raise ValueError("test-only operational DA artifacts do not match exact bytes")
    expected_finality = _derive_test_only_checkpoint_finality_artifacts_v2(
        policy=value.policy,
        settlement=value.settlement,
        prior_application_checkpoint_sequence=(
            value.finality.prior_application_checkpoint_sequence
        ),
        prior_application_checkpoint_hash=(
            value.finality.prior_application_checkpoint_hash
        ),
        next_application_checkpoint_hash=(
            value.finality.next_application_checkpoint_hash
        ),
        exact_certificate_bytes=value.finality.exact_certificate_bytes,
        exact_finality_evidence_bytes=value.finality.exact_finality_evidence_bytes,
    )
    if expected_finality != value.finality:
        raise ValueError("test-only operational finality artifacts do not match exact bytes")


def _require_retention(
    policy: _TestOnlySpotV7OperationalPolicyV1,
    epoch_id: int,
    checked_epoch: int,
    retention_through_epoch: int,
) -> None:
    for name, value in (
        ("epoch_id", epoch_id),
        ("checked_epoch", checked_epoch),
        ("retention_through_epoch", retention_through_epoch),
    ):
        _require_uint(value, name=name, maximum=MAX_U64)
    if checked_epoch < epoch_id:
        raise ValueError("test-only full-blob check precedes certificate epoch")
    initial = epoch_id + policy.minimum_retention_epochs
    remaining = checked_epoch + policy.minimum_remaining_epochs
    if initial > MAX_U64 or remaining > MAX_U64:
        raise ValueError("test-only full-blob retention horizon overflows")
    if retention_through_epoch < initial or retention_through_epoch < remaining:
        raise ValueError("test-only full-blob retention policy is unsatisfied")


def _full_blob_data_root_v1(blob: bytes) -> str:
    _bounded_bytes(blob, name="full blob", maximum=MAX_FULL_BLOB_BYTES_V1)
    return _domain_hash(
        _FULL_BLOB_DATA_ROOT_DOMAIN_V1,
        len(blob).to_bytes(8, "big") + blob,
    )


def _full_blob_chunk_root_v1(blob: bytes) -> tuple[int, str]:
    _bounded_bytes(blob, name="full blob", maximum=MAX_FULL_BLOB_BYTES_V1)
    chunks = tuple(
        blob[offset : offset + FULL_BLOB_CHUNK_BYTES_V1]
        for offset in range(0, len(blob), FULL_BLOB_CHUNK_BYTES_V1)
    )
    encoded = [len(chunks).to_bytes(4, "big")]
    for index, chunk in enumerate(chunks):
        encoded.append(
            _domain_hash_bytes(
                _FULL_BLOB_CHUNK_DOMAIN_V1,
                index.to_bytes(4, "big")
                + len(chunk).to_bytes(4, "big")
                + chunk,
            )
        )
    return len(chunks), _domain_hash(_FULL_BLOB_CHUNK_ROOT_DOMAIN_V1, b"".join(encoded))


def _full_blob_certificate_root_v1(
    *,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    epoch_id: int,
    data_root: str,
    blob_length: int,
    chunk_count: int,
    chunk_root: str,
    retention_through_epoch: int,
) -> str:
    return _domain_hash(
        _FULL_BLOB_CERTIFICATE_ROOT_DOMAIN_V1,
        b"".join(
            (
                (1).to_bytes(2, "big"),
                _hash_bytes(policy.application_id, name="certificate application"),
                _hash_bytes(policy.chain_or_domain_id, name="certificate domain"),
                epoch_id.to_bytes(8, "big"),
                _hash_bytes(policy.data_schema_id, name="certificate schema"),
                _hash_bytes(data_root, name="certificate data root"),
                blob_length.to_bytes(8, "big"),
                FULL_BLOB_CHUNK_BYTES_V1.to_bytes(4, "big"),
                chunk_count.to_bytes(4, "big"),
                _hash_bytes(chunk_root, name="certificate chunk root"),
                retention_through_epoch.to_bytes(8, "big"),
                _hash_bytes(policy.storage_policy_hash, name="certificate storage policy"),
            )
        ),
    )


def _finality_certificate_root_v2(
    *,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    epoch_id: int,
    proof_journal_hash: str,
    post_state_root: str,
    sequence: int,
    checkpoint_hash: str,
    parent_hash: str,
    evidence_root: str,
    policy_root: str,
) -> str:
    return _domain_hash(
        _FINALITY_CERTIFICATE_ROOT_DOMAIN_V2,
        b"".join(
            (
                (2).to_bytes(2, "big"),
                _hash_bytes(policy.application_id, name="finality application"),
                _hash_bytes(policy.chain_or_domain_id, name="finality domain"),
                epoch_id.to_bytes(8, "big"),
                _hash_bytes(proof_journal_hash, name="finality journal"),
                _hash_bytes(post_state_root, name="finality post state"),
                sequence.to_bytes(8, "big"),
                _hash_bytes(checkpoint_hash, name="checkpoint hash"),
                _root_bytes_allow_zero(parent_hash, name="checkpoint parent"),
                _hash_bytes(policy.finality_network_id, name="finality network"),
                _hash_bytes(policy.finality_protocol_id, name="finality protocol"),
                _hash_bytes(
                    policy.external_finality_policy_hash,
                    name="external finality policy",
                ),
                _hash_bytes(
                    policy.finality_verifier_set_root,
                    name="finality verifier set",
                ),
                _hash_bytes(evidence_root, name="finality evidence root"),
                _hash_bytes(policy_root, name="finality policy root"),
            )
        ),
    )


def _encode_full_blob_certificate_v1(
    *,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    epoch_id: int,
    data_root: str,
    blob_length: int,
    chunk_count: int,
    chunk_root: str,
    retention_through_epoch: int,
    certificate_root: str,
) -> bytes:
    """Encode the exact fixed-field Rust Postcard V1 certificate."""

    fields = (
        _postcard_uint(1),
        _hash_bytes(policy.application_id, name="certificate application"),
        _hash_bytes(policy.chain_or_domain_id, name="certificate domain"),
        _postcard_uint(epoch_id),
        _hash_bytes(policy.data_schema_id, name="certificate schema"),
        _hash_bytes(data_root, name="certificate data root"),
        _postcard_uint(blob_length),
        _postcard_uint(FULL_BLOB_CHUNK_BYTES_V1),
        _postcard_uint(chunk_count),
        _hash_bytes(chunk_root, name="certificate chunk root"),
        _postcard_uint(retention_through_epoch),
        _hash_bytes(policy.storage_policy_hash, name="certificate storage policy"),
        _hash_bytes(certificate_root, name="full-blob certificate root"),
    )
    return b"".join(fields)


def _encode_checkpoint_finality_certificate_v2(
    *,
    policy: _TestOnlySpotV7OperationalPolicyV1,
    epoch_id: int,
    proof_journal_hash: str,
    post_state_root: str,
    sequence: int,
    checkpoint_hash: str,
    parent_hash: str,
    evidence_root: str,
    policy_root: str,
    certificate_root: str,
) -> bytes:
    """Encode the exact fixed-field Rust Postcard V2 certificate."""

    fields = (
        _postcard_uint(2),
        _hash_bytes(policy.application_id, name="finality application"),
        _hash_bytes(policy.chain_or_domain_id, name="finality domain"),
        _postcard_uint(epoch_id),
        _hash_bytes(proof_journal_hash, name="finality journal"),
        _hash_bytes(post_state_root, name="finality post state"),
        _postcard_uint(sequence),
        _hash_bytes(checkpoint_hash, name="checkpoint hash"),
        _root_bytes_allow_zero(parent_hash, name="checkpoint parent"),
        _hash_bytes(policy.finality_network_id, name="finality network"),
        _hash_bytes(policy.finality_protocol_id, name="finality protocol"),
        _hash_bytes(
            policy.external_finality_policy_hash,
            name="external finality policy",
        ),
        _hash_bytes(policy.finality_verifier_set_root, name="finality verifier set"),
        _hash_bytes(evidence_root, name="finality evidence root"),
        _hash_bytes(policy_root, name="finality policy root"),
        _hash_bytes(certificate_root, name="finality certificate root"),
    )
    return b"".join(fields)


def _postcard_uint(value: int) -> bytes:
    """Encode Postcard's canonical unsigned varint for bounded protocol integers."""

    _require_uint(value, name="Postcard unsigned integer", maximum=MAX_U64)
    encoded = bytearray()
    remaining = value
    while remaining >= 0x80:
        encoded.append((remaining & 0x7F) | 0x80)
        remaining >>= 7
    encoded.append(remaining)
    return bytes(encoded)


def _bounded_bytes(value: bytes, *, name: str, maximum: int) -> None:
    if type(value) is not bytes or not value or len(value) > maximum:
        raise ValueError(f"{name} must be exact nonempty bytes within {maximum}")


def _domain_hash(domain: bytes, body: bytes) -> str:
    return "0x" + _domain_hash_bytes(domain, body).hex()


def _domain_hash_bytes(domain: bytes, body: bytes) -> bytes:
    return hashlib.sha256(len(domain).to_bytes(2, "big") + domain + body).digest()


__all__: list[str] = []
