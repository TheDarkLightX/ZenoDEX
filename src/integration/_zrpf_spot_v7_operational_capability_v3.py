"""Authority-neutral join for the complete bounded Spot V7 V3 prerequisite set.

The private capability produced here is a transaction input for the V4 durable
mechanics store.  It proves that already-authenticated prerequisite values agree
on one settlement.  It grants no release, settlement, or production authority.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import NoReturn, SupportsIndex, cast, final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_firecracker_authority import (
    _GovernedFirecrackerSpotV7SettlementV1,
)
from src.integration._zrpf_spot_v7_governed_da_projection_v2 import (
    _SpotV7GovernedDaPrerequisiteProjectionV2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _require_policy_binding,
    _require_settlement_capability,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    _encode_checkpoint_finality_certificate_v2,
    _finality_certificate_root_v2,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedOperationalPolicyProvenanceV2,
    _GovernedSpotV7OperationalPolicyV3,
    _require_governed_operational_policy_v3,
)
from src.integration._zrpf_spot_v7_settlement_durable_replay import (
    _DurablyReverifiedSpotV7SettlementReplayV2,
    _require_durably_reverified_spot_v7_settlement_replay_v2,
)
from src.integration._zrpf_spot_v7_settlement_envelope_codec import (
    MAX_HEADER_OR_CONFIG_BYTES_V1,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    _decode_exact_json_object,
    _SpotV7SettlementReplayProjectionV2,
)
from src.integration._zrpf_spot_v7_settlement_replay_packet import (
    _DurableSpotV7SettlementReplayPacketV2,
    _UntrustedPersistedSpotV7SettlementReplayInputsV2,
)
from src.integration._zrpf_spot_v7_zeno_ledger_finality_contract import _ZERO_ROOT
from src.integration.zeno_ledger_v0 import canonical_header_hash_v0
from src.integration.zrpf_spot_v7_governed_da_prerequisite_v2 import (
    _GovernedSpotV7DataAvailabilityPrerequisiteV2,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    _AuthenticatedCheckpointFinalityProjectionV3,
    _AuthenticatedExactCheckpointFinalityTransitionV3,
)


class SpotV7OperationalCapabilityBindingErrorV3(ValueError):
    """Stable rejection before the V3 atomic mechanics capability is minted."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_OPERATIONAL_CAPABILITY_V3_REJECTED: {code}")


@dataclass(frozen=True, slots=True)
class _SpotV7OperationalCommitPacketV3:
    settlement: _GovernedFirecrackerSpotV7SettlementV1
    candidate: _SpotV7SettlementCandidateInputV1
    policy: _GovernedSpotV7OperationalPolicyV3
    policy_provenance: _GovernedOperationalPolicyProvenanceV2
    data_availability: _SpotV7GovernedDaPrerequisiteProjectionV2
    exact_full_blob_bytes: bytes
    exact_full_blob_certificate_bytes: bytes
    exact_sampled_evidence_bytes: bytes
    exact_source_finality_certificate_bytes: bytes
    exact_source_finality_evidence_bytes: bytes
    finality: _AuthenticatedCheckpointFinalityProjectionV3
    exact_finality_certificate_bytes: bytes
    exact_finality_evidence_bytes: bytes
    durable_replay_packet: _DurableSpotV7SettlementReplayPacketV2
    persisted_replay_inputs: _UntrustedPersistedSpotV7SettlementReplayInputsV2
    exact_parent_header_bytes: bytes | None


class _SpotV7AtomicEconomicCommitSealV3:
    __slots__ = ()


_SPOT_V7_ATOMIC_ECONOMIC_COMMIT_SEAL_V3 = _SpotV7AtomicEconomicCommitSealV3()


class _NonTransferableOperationalCapabilityV3:
    __slots__ = ()

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("Spot V7 operational V3 capability cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("Spot V7 operational V3 capability cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("Spot V7 operational V3 capability cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("Spot V7 operational V3 capability cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("Spot V7 operational V3 capability cannot be serialized")


@final
class _SpotV7AtomicEconomicCommitCapabilityV3(_NonTransferableOperationalCapabilityV3):
    """Private recomposable packet for one authority-neutral atomic commit."""

    __slots__ = (
        "_data_availability",
        "_durable_replay",
        "_exact_parent_header_bytes",
        "_finality",
        "_policy",
        "_seal",
        "_settlement",
    )

    _settlement: _GovernedFirecrackerSpotV7SettlementV1
    _policy: _GovernedSpotV7OperationalPolicyV3
    _data_availability: _GovernedSpotV7DataAvailabilityPrerequisiteV2
    _finality: _AuthenticatedExactCheckpointFinalityTransitionV3
    _durable_replay: _DurablyReverifiedSpotV7SettlementReplayV2
    _exact_parent_header_bytes: bytes | None
    _seal: _SpotV7AtomicEconomicCommitSealV3

    def __init__(
        self,
        *,
        settlement: _GovernedFirecrackerSpotV7SettlementV1,
        policy: _GovernedSpotV7OperationalPolicyV3,
        data_availability: _GovernedSpotV7DataAvailabilityPrerequisiteV2,
        finality: _AuthenticatedExactCheckpointFinalityTransitionV3,
        durable_replay: _DurablyReverifiedSpotV7SettlementReplayV2,
        exact_parent_header_bytes: bytes | None,
        seal: _SpotV7AtomicEconomicCommitSealV3,
    ) -> None:
        if seal is not _SPOT_V7_ATOMIC_ECONOMIC_COMMIT_SEAL_V3:
            raise TypeError("Spot V7 operational V3 capability requires its private seal")
        _build_operational_commit_packet_v3(
            settlement=settlement,
            policy=policy,
            data_availability=data_availability,
            finality=finality,
            durable_replay=durable_replay,
            exact_parent_header_bytes=exact_parent_header_bytes,
        )
        object.__setattr__(self, "_settlement", settlement)
        object.__setattr__(self, "_policy", policy)
        object.__setattr__(self, "_data_availability", data_availability)
        object.__setattr__(self, "_finality", finality)
        object.__setattr__(self, "_durable_replay", durable_replay)
        object.__setattr__(self, "_exact_parent_header_bytes", exact_parent_header_bytes)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("Spot V7 operational V3 capability cannot be subclassed")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _SPOT_V7_ATOMIC_ECONOMIC_COMMIT_SEAL_V3

    def _packet_for_atomic_store_v4(self) -> _SpotV7OperationalCommitPacketV3:
        if not self._has_private_seal():
            raise TypeError("Spot V7 operational V3 capability lacks its private seal")
        return _build_operational_commit_packet_v3(
            settlement=self._settlement,
            policy=self._policy,
            data_availability=self._data_availability,
            finality=self._finality,
            durable_replay=self._durable_replay,
            exact_parent_header_bytes=self._exact_parent_header_bytes,
        )

    @property
    def durable_settlement_replay_reverified(self) -> bool:
        self._packet_for_atomic_store_v4()
        return True

    @property
    def sampled_policy_governance_provenance_verified(self) -> bool:
        self._packet_for_atomic_store_v4()
        return True

    @property
    def governed_beacon_provenance_verified(self) -> bool:
        self._packet_for_atomic_store_v4()
        return True

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


def _bind_spot_v7_operational_commit_capability_v3(
    *,
    settlement: object,
    policy: object,
    data_availability: object,
    finality: object,
    durable_replay: object,
    exact_parent_header_bytes: bytes | None = None,
) -> _SpotV7AtomicEconomicCommitCapabilityV3:
    return _SpotV7AtomicEconomicCommitCapabilityV3(
        settlement=_require_settlement_capability(settlement),
        policy=_require_governed_operational_policy_v3(policy),
        data_availability=_require_governed_da_v2(data_availability),
        finality=_require_finality_v3(finality),
        durable_replay=_require_durably_reverified_spot_v7_settlement_replay_v2(
            durable_replay
        ),
        exact_parent_header_bytes=_require_optional_parent_header_bytes(
            exact_parent_header_bytes
        ),
        seal=_SPOT_V7_ATOMIC_ECONOMIC_COMMIT_SEAL_V3,
    )


def _require_governed_da_v2(
    value: object,
) -> _GovernedSpotV7DataAvailabilityPrerequisiteV2:
    if type(value) is not _GovernedSpotV7DataAvailabilityPrerequisiteV2:
        raise TypeError("operational V3 join requires exact governed DA V2")
    typed = value
    if not typed._has_private_seal():
        raise TypeError("operational V3 join requires sealed governed DA V2")
    typed._projection_for_downstream_binding_v2()
    return typed


def _require_finality_v3(
    value: object,
) -> _AuthenticatedExactCheckpointFinalityTransitionV3:
    if type(value) is not _AuthenticatedExactCheckpointFinalityTransitionV3:
        raise TypeError("operational V3 join requires exact finality V3")
    typed = cast(_AuthenticatedExactCheckpointFinalityTransitionV3, value)
    if not typed._has_private_seal():
        raise TypeError("operational V3 join requires sealed finality V3")
    if "0x" + hashlib.sha256(typed._exact_finality_evidence_bytes).hexdigest() != (
        typed._projection.finality_evidence_root
    ):
        raise ValueError("operational V3 finality evidence drift")
    return typed


def _require_optional_parent_header_bytes(value: bytes | None) -> bytes | None:
    if value is None:
        return None
    if type(value) is not bytes or not value:
        raise TypeError("exact parent header must be non-empty bytes or None")
    return value


def _build_operational_commit_packet_v3(
    *,
    settlement: _GovernedFirecrackerSpotV7SettlementV1,
    policy: _GovernedSpotV7OperationalPolicyV3,
    data_availability: _GovernedSpotV7DataAvailabilityPrerequisiteV2,
    finality: _AuthenticatedExactCheckpointFinalityTransitionV3,
    durable_replay: _DurablyReverifiedSpotV7SettlementReplayV2,
    exact_parent_header_bytes: bytes | None,
) -> _SpotV7OperationalCommitPacketV3:
    settlement_value = _require_settlement_capability(settlement)
    policy_value = _require_governed_operational_policy_v3(policy)
    da_value = _require_governed_da_v2(data_availability)
    finality_value = _require_finality_v3(finality)
    replay_value = _require_durably_reverified_spot_v7_settlement_replay_v2(
        durable_replay
    )
    if da_value._policy is not policy_value:
        _mismatch("DA_POLICY_CAPABILITY_MISMATCH")
    candidate = settlement_value._candidate_for_atomic_store()
    policy_value._require_active_at_epoch_for_finality_v3(candidate.epoch_id)
    _require_policy_binding(
        candidate,
        policy_value._legacy_projection_for_finality_v3(),
    )
    da_projection = da_value._projection_for_downstream_binding_v2()
    replay_packet = replay_value._durable_replay_packet_for_history_commit()
    replay_projection = replay_packet._projection_for_history_reverification()
    finality_projection = finality_value._projection
    _require_join_bindings(
        candidate=candidate,
        policy=policy_value,
        data_availability=da_projection,
        finality=finality_projection,
        replay=replay_projection,
        exact_parent_header_bytes=exact_parent_header_bytes,
    )
    _require_exact_finality_certificate(policy_value, finality_value)
    persisted = replay_packet._persisted_inputs_for_storage()
    provenance = policy_value._provenance_for_governed_da_v2()
    source_finality_certificate, source_finality_evidence = (
        da_value._source_finality_artifacts_for_operational_store_v4()
    )
    return _SpotV7OperationalCommitPacketV3(
        settlement=settlement_value,
        candidate=candidate,
        policy=policy_value,
        policy_provenance=provenance,
        data_availability=da_projection,
        exact_full_blob_bytes=da_value._full_blob._exact_blob_bytes,
        exact_full_blob_certificate_bytes=da_value._full_blob._exact_certificate_bytes,
        exact_sampled_evidence_bytes=da_value._sampled._sampled.exact_evidence_bytes,
        exact_source_finality_certificate_bytes=source_finality_certificate,
        exact_source_finality_evidence_bytes=source_finality_evidence,
        finality=finality_projection,
        exact_finality_certificate_bytes=finality_value._exact_certificate_bytes,
        exact_finality_evidence_bytes=finality_value._exact_finality_evidence_bytes,
        durable_replay_packet=replay_packet,
        persisted_replay_inputs=persisted,
        exact_parent_header_bytes=exact_parent_header_bytes,
    )


def _require_join_bindings(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    policy: _GovernedSpotV7OperationalPolicyV3,
    data_availability: _SpotV7GovernedDaPrerequisiteProjectionV2,
    finality: _AuthenticatedCheckpointFinalityProjectionV3,
    replay: _SpotV7SettlementReplayProjectionV2,
    exact_parent_header_bytes: bytes | None,
) -> None:
    projection = replay
    base_da = data_availability.base
    policy_projection = policy._projection_for_governed_da_v2()
    checks = (
        (base_da.application_id == candidate.application_id, "DA_APPLICATION_MISMATCH"),
        (base_da.chain_or_domain_id == candidate.chain_or_domain_id, "DA_DOMAIN_MISMATCH"),
        (base_da.epoch_id == candidate.epoch_id, "DA_EPOCH_MISMATCH"),
        (
            base_da.certificate_root == candidate.data_availability_certificate_root,
            "DA_CERTIFICATE_MISMATCH",
        ),
        (base_da.data_root == candidate.data_root, "DA_DATA_ROOT_MISMATCH"),
        (
            data_availability.zeno_ledger_chain_id == projection.chain_id,
            "LEDGER_CHAIN_MISMATCH",
        ),
        (finality.application_id == candidate.application_id, "FINALITY_APPLICATION_MISMATCH"),
        (
            finality.chain_or_domain_id == candidate.chain_or_domain_id,
            "FINALITY_DOMAIN_MISMATCH",
        ),
        (finality.epoch_id == candidate.epoch_id, "FINALITY_EPOCH_MISMATCH"),
        (
            finality.proof_journal_hash
            == "0x" + hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest(),
            "FINALITY_JOURNAL_MISMATCH",
        ),
        (finality.post_state_root == candidate.post_state_root, "FINALITY_STATE_MISMATCH"),
        (
            finality.policy_root == policy_projection.checkpoint_finality_policy_root,
            "FINALITY_POLICY_MISMATCH",
        ),
        (
            finality.next_application_checkpoint_hash == projection.header_hash,
            "FINALITY_HEADER_MISMATCH",
        ),
        (
            (projection.parent_header_hash or _ZERO_ROOT)
            == finality.prior_application_checkpoint_hash,
            "FINALITY_PARENT_MISMATCH",
        ),
        (
            projection.candidate_settlement_commitment
            == _derive_capability_commitment(candidate),
            "REPLAY_SETTLEMENT_MISMATCH",
        ),
        (projection.pre_state_root == candidate.pre_state_root, "REPLAY_PRE_STATE_MISMATCH"),
        (projection.post_state_root == candidate.post_state_root, "REPLAY_POST_STATE_MISMATCH"),
    )
    for accepted, code in checks:
        if not accepted:
            _mismatch(code)
    if projection.parent_header_hash is None:
        if exact_parent_header_bytes is not None:
            _mismatch("UNEXPECTED_PARENT_HEADER")
    elif exact_parent_header_bytes is None:
        _mismatch("MISSING_PARENT_HEADER")
    else:
        _require_exact_parent_header_binding(
            exact_parent_header_bytes,
            expected_hash=projection.parent_header_hash,
        )


def _require_exact_parent_header_binding(
    exact_parent_header_bytes: bytes,
    *,
    expected_hash: str,
) -> None:
    if (
        type(exact_parent_header_bytes) is not bytes
        or not exact_parent_header_bytes
        or len(exact_parent_header_bytes) > MAX_HEADER_OR_CONFIG_BYTES_V1
    ):
        _mismatch("PARENT_HEADER_BYTES_INVALID")
    try:
        parent_header = _decode_exact_json_object(
            exact_parent_header_bytes,
            name="operational V3 exact parent header",
        )
        observed_hash = canonical_header_hash_v0(parent_header)
    except (TypeError, ValueError, RecursionError):
        _mismatch("PARENT_HEADER_BYTES_INVALID")
    if observed_hash != expected_hash:
        _mismatch("PARENT_HEADER_HASH_MISMATCH")


def _require_exact_finality_certificate(
    policy: _GovernedSpotV7OperationalPolicyV3,
    finality: _AuthenticatedExactCheckpointFinalityTransitionV3,
) -> None:
    projection = finality._projection
    store_policy = policy._base_store_policy_for_finality_v3()
    expected_root = _finality_certificate_root_v2(
        policy=store_policy,
        epoch_id=projection.epoch_id,
        proof_journal_hash=projection.proof_journal_hash,
        post_state_root=projection.post_state_root,
        sequence=projection.next_application_checkpoint_sequence,
        checkpoint_hash=projection.next_application_checkpoint_hash,
        parent_hash=projection.prior_application_checkpoint_hash,
        evidence_root=projection.finality_evidence_root,
        policy_root=projection.policy_root,
    )
    if expected_root != projection.certificate_root:
        _mismatch("FINALITY_CERTIFICATE_ROOT_MISMATCH")
    expected_bytes = _encode_checkpoint_finality_certificate_v2(
        policy=store_policy,
        epoch_id=projection.epoch_id,
        proof_journal_hash=projection.proof_journal_hash,
        post_state_root=projection.post_state_root,
        sequence=projection.next_application_checkpoint_sequence,
        checkpoint_hash=projection.next_application_checkpoint_hash,
        parent_hash=projection.prior_application_checkpoint_hash,
        evidence_root=projection.finality_evidence_root,
        policy_root=projection.policy_root,
        certificate_root=projection.certificate_root,
    )
    if expected_bytes != finality._exact_certificate_bytes:
        _mismatch("FINALITY_CERTIFICATE_BYTES_MISMATCH")


def _mismatch(code: str) -> NoReturn:
    raise SpotV7OperationalCapabilityBindingErrorV3(code)


__all__ = ()
