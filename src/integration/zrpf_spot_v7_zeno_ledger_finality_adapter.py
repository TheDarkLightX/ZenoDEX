"""Governed ZenoLedger BLS-quorum adapters for Spot V7 checkpoint finality.

Both versions accept one sealed Spot V7 settlement candidate and one sealed
operational policy. V2 binds the legacy transaction-only replay observation.
V3 derives its header from the exact retained-material settlement-envelope
observation, then binds the candidate, effect plan, action, nullifiers, cell
effects, state roots, and parent before authenticating the same proof-neutral
checkpoint quorum and certificate primitive.

Only the V2 private capability is accepted by the authority-false V2 atomic
store sink. V3 deliberately returns a distinct sealed transition pending a V3
durable store that persists and re-executes the retained replay material.
Release provenance, data availability, economic settlement, and production
authority remain separate gates.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Any, Mapping, NoReturn, Sequence, SupportsIndex, TypeAlias, final

from src.integration._zrpf_spot_v7_atomic_settlement_capability import (
    _derive_capability_commitment,
    _seal_test_only_spot_v7_settlement_v1,
    _SpotV7SettlementCandidateInputV1,
)
from src.integration._zrpf_spot_v7_operational_capability_v2 import (
    _AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2,
    _AuthenticatedExactCheckpointFinalityTransitionV2,
    _GovernedSpotV7OperationalPolicyV2,
    _require_operational_policy_v2,
)
from src.integration._zrpf_spot_v7_operational_gate import (
    _AuthenticatedCheckpointFinalityProjectionV2,
    _GovernedOperationalPolicyProjectionV1,
    _require_policy_binding,
    _require_settlement_capability,
)
from src.integration._zrpf_spot_v7_operational_mechanics import (
    MAX_FINALITY_CERTIFICATE_BYTES_V2,
    MAX_FINALITY_EVIDENCE_BYTES_V2,
    _build_test_only_checkpoint_finality_artifacts_v2,
    _TestOnlySpotV7OperationalPolicyV1,
)
from src.integration._zrpf_spot_v7_operational_policy_v3 import (
    _GovernedSpotV7OperationalPolicyV3,
    _require_governed_operational_policy_v3,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    SPOT_V7_SETTLEMENT_EFFECT_IDS_ROOT_DOMAIN_V1,
    _AuthenticatedSpotV7SettlementReplayObservationV2,
    _require_settlement_replay_observation_v2,
)
from src.integration._zrpf_spot_v7_zeno_ledger_finality_contract import (
    _MAX_FINALITY_QUORUM_SIGNERS_V1,
    _ZERO_ROOT,
    SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2,
    SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V3,
    SPOT_V7_ZENO_LEDGER_PROPOSER_AUTHORSHIP_ADMISSION_SCHEMA_V1,
    SpotV7ZenoLedgerFinalityBindingErrorV1,
    ZenoLedgerCheckpointFinalityCursorV1,
    _FinalityInputSnapshotV1,
    _require_hash,
    _require_nonempty_string,
    _require_positive_u64,
    _snapshot_inputs,
    derive_zeno_ledger_external_finality_policy_hash_v2,
    derive_zeno_ledger_finality_network_id_v1,
    derive_zeno_ledger_finality_protocol_id_v2,
    derive_zeno_ledger_finality_protocol_id_v3,
    derive_zeno_ledger_proposer_authorship_payload_hash_v1,
)
from src.integration._zrpf_spot_v7_zeno_ledger_replay_observation import (
    _AuthenticatedReplayBoundBlockObservationV1,
    _require_replay_observation,
)
from src.integration.zeno_ledger_live_quorum_v0 import build_live_checkpoint_quorum_admission_v0
from src.integration.zeno_ledger_signature import (
    validate_bls_signed_artifact_envelope_v0,
)
from src.integration.zeno_ledger_signer_registry import (
    validate_signer_registry_v0,
)
from src.integration.zeno_ledger_v0 import (
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
    compute_app_hash_v0,
    hash_v0,
    validate_checkpoint_header_binding_v0,
)
from src.integration.zeno_ledger_validator_schedule_v0 import (
    build_proposer_duty_v0,
    build_scheduled_header_admission_v0,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import (
    MAX_U64,
    _hash_bytes,
    _require_uint,
    _root_bytes_allow_zero,
)


@dataclass(frozen=True, slots=True)
class _AuthenticatedCheckpointQuorumCoreV1:
    """Private proof-neutral result of one exact checkpoint quorum verification."""

    scheduled_header_admission: dict[str, Any]
    proposer_authorship_admission: dict[str, Any]
    live_quorum_admission: dict[str, Any]


@dataclass(frozen=True, slots=True)
class _AuthenticatedCheckpointFinalityProjectionV3:
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
        for name in (
            "application_id",
            "chain_or_domain_id",
            "proof_journal_hash",
            "post_state_root",
            "policy_root",
            "certificate_root",
            "finality_evidence_root",
            "next_application_checkpoint_hash",
        ):
            _hash_bytes(getattr(self, name), name=f"checkpoint finality V3 {name}")
        _root_bytes_allow_zero(
            self.prior_application_checkpoint_hash,
            name="checkpoint finality V3 prior_application_checkpoint_hash",
        )
        for name in (
            "epoch_id",
            "prior_application_checkpoint_sequence",
            "next_application_checkpoint_sequence",
        ):
            _require_uint(getattr(self, name), name=name, maximum=MAX_U64)
        if self.prior_application_checkpoint_sequence == MAX_U64:
            raise ValueError("checkpoint finality V3 prior sequence overflows")
        if self.next_application_checkpoint_sequence != (
            self.prior_application_checkpoint_sequence + 1
        ):
            raise ValueError("checkpoint finality V3 cursor is not an exact successor")


class _AuthenticatedCheckpointFinalitySealV3:
    __slots__ = ()


_AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3 = _AuthenticatedCheckpointFinalitySealV3()


@final
class _AuthenticatedExactCheckpointFinalityTransitionV3:
    """Sealed V3 finality transition; intentionally not accepted by the V2 store."""

    __slots__ = (
        "_projection",
        "_exact_certificate_bytes",
        "_exact_finality_evidence_bytes",
        "_seal",
    )

    def __init__(
        self,
        projection: _AuthenticatedCheckpointFinalityProjectionV3,
        *,
        exact_certificate_bytes: bytes,
        exact_finality_evidence_bytes: bytes,
        seal: _AuthenticatedCheckpointFinalitySealV3,
    ) -> None:
        if type(projection) is not _AuthenticatedCheckpointFinalityProjectionV3:
            raise TypeError("checkpoint finality V3 projection has the wrong type")
        if seal is not _AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3:
            raise TypeError("checkpoint finality V3 requires its private seal")
        if type(exact_certificate_bytes) is not bytes or not exact_certificate_bytes:
            raise TypeError("checkpoint finality V3 certificate must be non-empty bytes")
        if (
            type(exact_finality_evidence_bytes) is not bytes
            or not exact_finality_evidence_bytes
        ):
            raise TypeError("checkpoint finality V3 evidence must be non-empty bytes")
        if len(exact_certificate_bytes) > MAX_FINALITY_CERTIFICATE_BYTES_V2:
            raise ValueError("checkpoint finality V3 certificate exceeds its byte bound")
        if len(exact_finality_evidence_bytes) > MAX_FINALITY_EVIDENCE_BYTES_V2:
            raise ValueError("checkpoint finality V3 evidence exceeds its byte bound")
        if _sha256_prefixed(exact_finality_evidence_bytes) != (
            projection.finality_evidence_root
        ):
            raise ValueError("checkpoint finality V3 evidence root mismatch")
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_exact_certificate_bytes", exact_certificate_bytes)
        object.__setattr__(
            self,
            "_exact_finality_evidence_bytes",
            exact_finality_evidence_bytes,
        )
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("checkpoint finality V3 transition cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("checkpoint finality V3 transition cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("checkpoint finality V3 transition cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("checkpoint finality V3 transition cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("checkpoint finality V3 transition cannot be serialized")

    @property
    def proof_receipt_authentication_established(self) -> bool:
        return False

    @property
    def application_domain_to_ledger_chain_binding_established(self) -> bool:
        return False

    @property
    def public_data_retrievability_established(self) -> bool:
        return False

    @property
    def canonical_conflicting_checkpoint_selection_established(self) -> bool:
        return False

    @property
    def durable_settlement_replay_reverified(self) -> bool:
        return False

    @property
    def exact_replay_material_authenticated(self) -> bool:
        return True

    @property
    def durable_settlement_replay_material_persisted(self) -> bool:
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


@final
class SpotV7ZenoLedgerCheckpointFinalityAdapterV2:
    """Authenticate one policy-pinned ZenoLedger checkpoint BLS quorum."""

    __slots__ = ("_policy",)

    _policy: _GovernedSpotV7OperationalPolicyV2

    def __init__(self, policy: object) -> None:
        object.__setattr__(self, "_policy", _require_operational_policy_v2(policy))

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SpotV7ZenoLedgerCheckpointFinalityAdapterV2 cannot be subclassed")

    @property
    def cryptographic_checkpoint_quorum_supported(self) -> bool:
        return True

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False

    def authenticate(
        self,
        *,
        settlement: object,
        prior_cursor: object,
        header: object,
        replay_observation: object,
        checkpoint: object,
        validator_set: object,
        proposer_id: object,
        proposer_key_id: object,
        proposer_envelope: object,
        registry: object,
        envelopes: object,
    ) -> _AuthenticatedExactCheckpointFinalityTransitionV2:
        """Verify exact BLS evidence, then derive and seal finality V2 facts."""

        settlement_value = _require_settlement_capability(settlement)
        cursor = _require_cursor(prior_cursor)
        replay = _require_replay_observation(replay_observation)
        snapshot = _snapshot_inputs(
            header=header,
            checkpoint=checkpoint,
            validator_set=validator_set,
            proposer_id=proposer_id,
            proposer_key_id=proposer_key_id,
            proposer_envelope=proposer_envelope,
            registry=registry,
            envelopes=envelopes,
        )
        candidate = settlement_value._candidate_for_atomic_store()
        policy_projection = self._policy._projection
        _require_policy_binding(candidate, policy_projection)
        try:
            self._policy._require_active_at_epoch_for_operational_use(candidate.epoch_id)
        except ValueError as exc:
            raise SpotV7ZenoLedgerFinalityBindingErrorV1(
                "operational_policy_inactive"
            ) from exc
        policy = self._policy._policy_for_atomic_store()
        _validate_checkpoint_structure(snapshot)
        _validate_header_app_hash(snapshot.header)
        _require_checkpoint_transition_binding(
            candidate=candidate,
            cursor=cursor,
            header=snapshot.header,
            checkpoint=snapshot.checkpoint,
            policy=policy,
        )
        scheduled_header_admission = _require_scheduled_header_admission(snapshot)
        _require_registry_and_external_policy_binding(
            header=snapshot.header,
            registry=snapshot.registry,
            policy=policy,
            expected_finality_protocol_id=derive_zeno_ledger_finality_protocol_id_v2(),
        )
        _require_replay_transition_binding(
            candidate=candidate,
            cursor=cursor,
            header=snapshot.header,
            policy=policy,
            replay=replay,
        )
        quorum = _authenticate_checkpoint_quorum_core(
            snapshot=snapshot,
            scheduled_header_admission=scheduled_header_admission,
        )
        evidence_bytes = _canonical_finality_evidence(
            candidate=candidate,
            cursor=cursor,
            snapshot=snapshot,
            replay_observation=replay,
            scheduled_header_admission=quorum.scheduled_header_admission,
            proposer_authorship_admission=quorum.proposer_authorship_admission,
            admission=quorum.live_quorum_admission,
        )
        return _derive_exact_finality_capability(
            candidate=candidate,
            policy=self._policy,
            cursor=cursor,
            checkpoint=snapshot.checkpoint,
            evidence_bytes=evidence_bytes,
        )


_FinalityPolicyV3: TypeAlias = (
    _GovernedSpotV7OperationalPolicyV2 | _GovernedSpotV7OperationalPolicyV3
)


def _require_finality_policy_v3(value: object) -> _FinalityPolicyV3:
    if type(value) is _GovernedSpotV7OperationalPolicyV2:
        return _require_operational_policy_v2(value)
    if type(value) is _GovernedSpotV7OperationalPolicyV3:
        return _require_governed_operational_policy_v3(value)
    raise TypeError("finality V3 requires an exact governed V2 or V3 policy")


def _finality_policy_projection_v3(
    policy: _FinalityPolicyV3,
) -> _GovernedOperationalPolicyProjectionV1:
    if isinstance(policy, _GovernedSpotV7OperationalPolicyV2):
        return policy._projection
    return policy._legacy_projection_for_finality_v3()


def _require_finality_policy_active_v3(
    policy: _FinalityPolicyV3,
    epoch: int,
) -> None:
    if isinstance(policy, _GovernedSpotV7OperationalPolicyV2):
        policy._require_active_at_epoch_for_operational_use(epoch)
        return
    policy._require_active_at_epoch_for_finality_v3(epoch)


def _base_store_policy_for_finality_v3(
    policy: _FinalityPolicyV3,
) -> _TestOnlySpotV7OperationalPolicyV1:
    if isinstance(policy, _GovernedSpotV7OperationalPolicyV2):
        return policy._policy_for_atomic_store()
    return policy._base_store_policy_for_finality_v3()


@final
class SpotV7ZenoLedgerCheckpointFinalityAdapterV3:
    """Authenticate finality for one exact sealed settlement-envelope replay."""

    __slots__ = ("_policy",)

    _policy: _GovernedSpotV7OperationalPolicyV2 | _GovernedSpotV7OperationalPolicyV3

    def __init__(self, policy: object) -> None:
        object.__setattr__(self, "_policy", _require_finality_policy_v3(policy))

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("SpotV7ZenoLedgerCheckpointFinalityAdapterV3 cannot be subclassed")

    @property
    def cryptographic_checkpoint_quorum_supported(self) -> bool:
        return True

    @property
    def proof_receipt_authentication_established(self) -> bool:
        return False

    @property
    def application_domain_to_ledger_chain_binding_established(self) -> bool:
        return False

    @property
    def public_data_retrievability_established(self) -> bool:
        return False

    @property
    def canonical_conflicting_checkpoint_selection_established(self) -> bool:
        return False

    @property
    def durable_settlement_replay_reverified(self) -> bool:
        return False

    @property
    def exact_replay_material_authenticated(self) -> bool:
        return True

    @property
    def durable_settlement_replay_material_persisted(self) -> bool:
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

    def authenticate(
        self,
        *,
        settlement: object,
        prior_cursor: object,
        settlement_replay_observation: object,
        checkpoint: object,
        validator_set: object,
        proposer_id: object,
        proposer_key_id: object,
        proposer_envelope: object,
        registry: object,
        envelopes: object,
    ) -> _AuthenticatedExactCheckpointFinalityTransitionV3:
        """Derive the header from sealed replay and authenticate exact BLS finality."""

        settlement_value = _require_settlement_capability(settlement)
        cursor = _require_cursor(prior_cursor)
        replay = _require_settlement_replay_observation_v2(
            settlement_replay_observation
        )
        snapshot = _snapshot_inputs(
            header=replay._header_for_finality_adapter(),
            checkpoint=checkpoint,
            validator_set=validator_set,
            proposer_id=proposer_id,
            proposer_key_id=proposer_key_id,
            proposer_envelope=proposer_envelope,
            registry=registry,
            envelopes=envelopes,
        )
        candidate = settlement_value._candidate_for_atomic_store()
        policy_projection = _finality_policy_projection_v3(self._policy)
        _require_policy_binding(candidate, policy_projection)
        try:
            _require_finality_policy_active_v3(self._policy, candidate.epoch_id)
        except ValueError as exc:
            raise SpotV7ZenoLedgerFinalityBindingErrorV1(
                "operational_policy_inactive"
            ) from exc
        policy = _base_store_policy_for_finality_v3(self._policy)
        _validate_checkpoint_structure(snapshot)
        _validate_header_app_hash(snapshot.header)
        _require_checkpoint_transition_binding(
            candidate=candidate,
            cursor=cursor,
            header=snapshot.header,
            checkpoint=snapshot.checkpoint,
            policy=policy,
        )
        _require_settlement_replay_transition_binding(
            candidate=candidate,
            cursor=cursor,
            header=snapshot.header,
            policy=policy,
            replay=replay,
        )
        scheduled_header_admission = _require_scheduled_header_admission(snapshot)
        _require_registry_and_external_policy_binding(
            header=snapshot.header,
            registry=snapshot.registry,
            policy=policy,
            expected_finality_protocol_id=derive_zeno_ledger_finality_protocol_id_v3(),
        )
        quorum = _authenticate_checkpoint_quorum_core(
            snapshot=snapshot,
            scheduled_header_admission=scheduled_header_admission,
        )
        evidence_bytes = _canonical_finality_evidence_v3(
            candidate=candidate,
            cursor=cursor,
            snapshot=snapshot,
            settlement_replay_observation=replay,
            scheduled_header_admission=quorum.scheduled_header_admission,
            proposer_authorship_admission=quorum.proposer_authorship_admission,
            admission=quorum.live_quorum_admission,
        )
        return _derive_exact_finality_capability_v3(
            candidate=candidate,
            policy=self._policy,
            cursor=cursor,
            checkpoint=snapshot.checkpoint,
            evidence_bytes=evidence_bytes,
        )


def _validate_checkpoint_structure(snapshot: _FinalityInputSnapshotV1) -> None:
    validate_checkpoint_header_binding_v0(snapshot.checkpoint, snapshot.header)
    if snapshot.checkpoint["signature_set"] != []:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("embedded_signature_set")
    if snapshot.checkpoint["signature_set_root"] != _ZERO_ROOT:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("embedded_signature_set_root")


def _validate_header_app_hash(header: Mapping[str, Any]) -> None:
    expected = compute_app_hash_v0(
        {
            "chain_id": header["chain_id"],
            "height": header["height"],
            "post_state_root": header["post_state_root"],
            "evidence_root": header["evidence_root"],
            "config_digest": header["config_digest"],
            "module_versions_digest": header["module_versions_digest"],
        }
    )
    if header["app_hash"] != expected:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("app_hash")


def _require_scheduled_header_admission(
    snapshot: _FinalityInputSnapshotV1,
) -> dict[str, Any]:
    try:
        return build_scheduled_header_admission_v0(
            header=snapshot.header,
            validator_set=snapshot.validator_set,
            proposer_id=snapshot.proposer_id,
            key_id=snapshot.proposer_key_id,
        )
    except (TypeError, ValueError) as exc:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("scheduled_header_admission") from exc


def _require_proposer_authorship(
    snapshot: _FinalityInputSnapshotV1,
) -> dict[str, Any]:
    """Authenticate the scheduled proposer over the exact canonical header."""

    try:
        duty = build_proposer_duty_v0(
            validator_set=snapshot.validator_set,
            height=int(snapshot.header["height"]),
        )
        proposer = duty["proposer"]
        if type(proposer) is not dict:
            raise TypeError("scheduled proposer must be an exact dict")
        if (
            proposer.get("validator_id") != snapshot.proposer_id
            or proposer.get("key_id") != snapshot.proposer_key_id
        ):
            raise ValueError("proposer identity does not match scheduled duty")
        envelope = snapshot.proposer_envelope
        if (
            envelope.get("signer_id") != snapshot.proposer_id
            or envelope.get("key_id") != snapshot.proposer_key_id
        ):
            raise ValueError("proposer envelope identity mismatch")
        header_hash = canonical_header_hash_v0(snapshot.header)
        authorship_payload_hash = derive_zeno_ledger_proposer_authorship_payload_hash_v1(
            chain_id=snapshot.header["chain_id"],
            height=snapshot.header["height"],
            header_hash=header_hash,
            validator_set_hash=snapshot.validator_set["validator_set_hash"],
            duty_hash=duty["duty_hash"],
        )
        public_key = _require_nonempty_string(
            proposer.get("public_key"),
            name="scheduled proposer public key",
        )
        validate_bls_signed_artifact_envelope_v0(
            envelope=envelope,
            expected_payload_kind="checkpoint",
            expected_payload_hash=authorship_payload_hash,
            expected_public_key=public_key,
        )
        body = {
            "schema": SPOT_V7_ZENO_LEDGER_PROPOSER_AUTHORSHIP_ADMISSION_SCHEMA_V1,
            "ok": True,
            "status": "accepted",
            "chain_id": snapshot.header["chain_id"],
            "height": snapshot.header["height"],
            "header_hash": header_hash,
            "authorship_payload_hash": authorship_payload_hash,
            "validator_set_hash": snapshot.validator_set["validator_set_hash"],
            "duty_hash": duty["duty_hash"],
            "proposer_id": snapshot.proposer_id,
            "key_id": snapshot.proposer_key_id,
            "public_key": public_key,
            "envelope_hash": envelope["envelope_hash"],
        }
        return {
            **body,
            "admission_hash": hash_v0(
                "zrpf_spot_v7_proposer_authorship_admission_v1",
                body,
            ),
        }
    except (KeyError, RuntimeError, TypeError, ValueError) as exc:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("proposer_authorship") from exc


def _authenticate_checkpoint_quorum_core(
    *,
    snapshot: _FinalityInputSnapshotV1,
    scheduled_header_admission: dict[str, Any],
) -> _AuthenticatedCheckpointQuorumCoreV1:
    """Authenticate proposer and live quorum once after protocol-specific binding."""

    proposer_authorship_admission = _require_proposer_authorship(snapshot)
    admission = build_live_checkpoint_quorum_admission_v0(
        header=snapshot.header,
        checkpoint=snapshot.checkpoint,
        registry=snapshot.registry,
        envelopes=snapshot.envelopes,
    )
    return _AuthenticatedCheckpointQuorumCoreV1(
        scheduled_header_admission=scheduled_header_admission,
        proposer_authorship_admission=proposer_authorship_admission,
        live_quorum_admission=admission,
    )


def _require_checkpoint_transition_binding(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    cursor: ZenoLedgerCheckpointFinalityCursorV1,
    header: Mapping[str, Any],
    checkpoint: Mapping[str, Any],
    policy: _TestOnlySpotV7OperationalPolicyV1,
) -> None:
    policy_genesis_sequence = policy.genesis_application_checkpoint_sequence
    policy_genesis_hash = policy.genesis_application_checkpoint_hash
    if cursor.sequence < policy_genesis_sequence:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("prior_before_genesis")
    if cursor.sequence == policy_genesis_sequence and cursor.checkpoint_hash != policy_genesis_hash:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("genesis_checkpoint_hash")
    if cursor.sequence == MAX_U64:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("checkpoint_sequence_overflow")
    expected_sequence = cursor.sequence + 1
    checks = (
        (header["height"] == expected_sequence, "checkpoint_sequence"),
        (candidate.epoch_id == expected_sequence, "checkpoint_epoch"),
        (header["prev_header_hash"] == cursor.checkpoint_hash, "prior_checkpoint_hash"),
        (header["pre_state_root"] == candidate.pre_state_root, "pre_state_root"),
        (header["post_state_root"] == candidate.post_state_root, "post_state_root"),
        (header["data_availability_root"] == candidate.data_root, "data_root"),
        (
            header["proof_journal_hash"] == _candidate_journal_hash(candidate),
            "proof_journal_hash",
        ),
        (checkpoint["post_state_root"] == candidate.post_state_root, "post_state_root"),
        (
            checkpoint["proof_journal_hash"] == _candidate_journal_hash(candidate),
            "proof_journal_hash",
        ),
    )
    _require_checks(checks)


def _require_replay_transition_binding(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    cursor: ZenoLedgerCheckpointFinalityCursorV1,
    header: Mapping[str, Any],
    policy: _TestOnlySpotV7OperationalPolicyV1,
    replay: _AuthenticatedReplayBoundBlockObservationV1,
) -> None:
    projection = replay._projection_for_finality_adapter()
    replay_header = replay._header_for_finality_adapter()
    expected_parent_header_hash = (
        None
        if cursor.sequence == policy.genesis_application_checkpoint_sequence
        else cursor.checkpoint_hash
    )
    checks = (
        (projection.body_root == header["body_root"], "replay_body_root"),
        (projection.config_digest == header["config_digest"], "replay_config_digest"),
        (projection.height == candidate.epoch_id, "replay_epoch"),
        (projection.pre_state_root == candidate.pre_state_root, "replay_pre_state_root"),
        (projection.post_state_root == candidate.post_state_root, "replay_post_state_root"),
        (
            projection.body_committed_proof_journal_hash
            == _candidate_journal_hash(candidate),
            "replay_proof_receipt_journal",
        ),
        (
            projection.parent_header_hash == expected_parent_header_hash,
            "replay_parent_state_continuity",
        ),
        (replay_header == header, "replay_header"),
        (projection.header_hash == canonical_header_hash_v0(dict(header)), "replay_header"),
    )
    _require_checks(checks)


def _require_settlement_replay_transition_binding(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    cursor: ZenoLedgerCheckpointFinalityCursorV1,
    header: Mapping[str, Any],
    policy: _TestOnlySpotV7OperationalPolicyV1,
    replay: _AuthenticatedSpotV7SettlementReplayObservationV2,
) -> None:
    projection = replay._projection_for_finality_adapter()
    expected_parent_header_hash = (
        None
        if (
            cursor.sequence == policy.genesis_application_checkpoint_sequence
            and cursor.checkpoint_hash == _ZERO_ROOT
        )
        else cursor.checkpoint_hash
    )
    expected_effect_ids_root = hash_v0(
        SPOT_V7_SETTLEMENT_EFFECT_IDS_ROOT_DOMAIN_V1,
        {"effect_ids": [row.effect_id for row in candidate.asset_effects]},
    )
    checks = (
        (projection.chain_id == header["chain_id"], "replay_chain_id"),
        (projection.height == candidate.epoch_id, "replay_epoch"),
        (projection.header_hash == canonical_header_hash_v0(dict(header)), "replay_header"),
        (projection.body_root == header["body_root"], "replay_body_root"),
        (projection.config_digest == header["config_digest"], "replay_config_digest"),
        (
            projection.candidate_settlement_commitment
            == _derive_capability_commitment(candidate),
            "replay_candidate_settlement",
        ),
        (
            projection.proof_journal_hash == _candidate_journal_hash(candidate),
            "replay_proof_receipt_journal",
        ),
        (projection.receipt_accepted is True, "replay_receipt_acceptance"),
        (
            projection.settlement_effect_plan_commitment
            == candidate.settlement_effect_plan_commitment,
            "replay_settlement_effect_plan",
        ),
        (projection.pre_state_root == candidate.pre_state_root, "replay_pre_state_root"),
        (
            projection.post_state_root == candidate.post_state_root,
            "replay_post_state_root",
        ),
        (
            projection.economic_action_id == candidate.economic_action_id,
            "replay_economic_action",
        ),
        (
            projection.authorization_nullifier == candidate.authorization_nullifier,
            "replay_authorization_nullifier",
        ),
        (
            projection.authorization_grant_spend_nullifier
            == candidate.authorization_grant_spend_nullifier,
            "replay_authorization_grant_spend_nullifier",
        ),
        (
            projection.cell_transitions_root == candidate.cell_transitions_root,
            "replay_cell_transitions",
        ),
        (
            projection.asset_effect_ids_root == expected_effect_ids_root,
            "replay_asset_effect_ids",
        ),
        (
            projection.parent_header_hash == expected_parent_header_hash,
            "replay_parent_state_continuity",
        ),
    )
    _require_checks(checks)


def _require_registry_and_external_policy_binding(
    *,
    header: Mapping[str, Any],
    registry: dict[str, Any],
    policy: _TestOnlySpotV7OperationalPolicyV1,
    expected_finality_protocol_id: str,
) -> None:
    validate_signer_registry_v0(registry)
    signers = registry["signers"]
    if (
        type(signers) is not list
        or not signers
        or len(signers) > _MAX_FINALITY_QUORUM_SIGNERS_V1
    ):
        raise ValueError("signer registry count is outside the governed bound")
    chain_id = _require_nonempty_string(header["chain_id"], name="header.chain_id")
    registry_hash = _require_hash(registry["registry_hash"], name="registry hash")
    expected_external_policy = derive_zeno_ledger_external_finality_policy_hash_v2(
        chain_id=chain_id,
        config_digest=_require_hash(header["config_digest"], name="header config digest"),
        sequencer_set_hash=_require_hash(
            header["sequencer_set_hash"],
            name="header sequencer set hash",
        ),
    )
    checks = (
        (
            policy.finality_verifier_set_root == registry_hash,
            "verifier_set_root",
        ),
        (
            policy.finality_network_id == derive_zeno_ledger_finality_network_id_v1(chain_id),
            "finality_network",
        ),
        (
            policy.finality_protocol_id == expected_finality_protocol_id,
            "finality_protocol",
        ),
        (
            policy.external_finality_policy_hash == expected_external_policy,
            "external_finality_policy",
        ),
    )
    _require_checks(checks)
    active_weight = _active_weight(signers)
    threshold = _require_positive_u64(registry["threshold"], name="registry threshold")
    if threshold * 3 <= active_weight * 2:
        raise SpotV7ZenoLedgerFinalityBindingErrorV1("quorum_intersection")


def _active_weight(signers: Sequence[object]) -> int:
    total = 0
    for index, signer in enumerate(signers):
        if type(signer) is not dict:
            raise TypeError(f"registry.signers[{index}] must be an exact dict")
        if signer.get("status") == "active":
            weight = _require_positive_u64(
                signer.get("weight"),
                name=f"registry.signers[{index}].weight",
            )
            total += weight
            if total > MAX_U64:
                raise ValueError("active signer weight exceeds u64")
    if total == 0:
        raise ValueError("signer registry has no active weight")
    return total


def _canonical_finality_evidence(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    cursor: ZenoLedgerCheckpointFinalityCursorV1,
    snapshot: _FinalityInputSnapshotV1,
    replay_observation: _AuthenticatedReplayBoundBlockObservationV1,
    scheduled_header_admission: Mapping[str, Any],
    proposer_authorship_admission: Mapping[str, Any],
    admission: Mapping[str, Any],
) -> bytes:
    body = {
        "schema": SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2,
        "application_binding": {
            "application_id": candidate.application_id,
            "chain_or_domain_id": candidate.chain_or_domain_id,
            "epoch_id": candidate.epoch_id,
            "post_state_root": candidate.post_state_root,
            "proof_journal_hash": _candidate_journal_hash(candidate),
        },
        "prior_application_checkpoint": {
            "sequence": cursor.sequence,
            "checkpoint_hash": cursor.checkpoint_hash,
        },
        "replay_bound_observation": (
            replay_observation._canonical_projection_for_finality_adapter()
        ),
        "header": snapshot.header,
        "checkpoint": snapshot.checkpoint,
        "validator_set": snapshot.validator_set,
        "scheduled_header_admission": dict(scheduled_header_admission),
        "proposer_envelope": snapshot.proposer_envelope,
        "proposer_authorship_admission": dict(proposer_authorship_admission),
        "registry": snapshot.registry,
        "envelopes": list(snapshot.envelopes),
        "live_quorum_admission": dict(admission),
    }
    encoded = canonical_json_bytes_v0(body)
    if not encoded or len(encoded) > MAX_FINALITY_EVIDENCE_BYTES_V2:
        raise ValueError("canonical finality evidence exceeds checkpoint-finality V2 bound")
    return encoded


def _canonical_finality_evidence_v3(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    cursor: ZenoLedgerCheckpointFinalityCursorV1,
    snapshot: _FinalityInputSnapshotV1,
    settlement_replay_observation: _AuthenticatedSpotV7SettlementReplayObservationV2,
    scheduled_header_admission: Mapping[str, Any],
    proposer_authorship_admission: Mapping[str, Any],
    admission: Mapping[str, Any],
) -> bytes:
    body = {
        "schema": SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V3,
        "application_binding": {
            "application_id": candidate.application_id,
            "chain_or_domain_id": candidate.chain_or_domain_id,
            "epoch_id": candidate.epoch_id,
            "verified_program_id": candidate.verified_program_id,
            "verified_profile_id": candidate.verified_profile_id,
            "verified_program_manifest_root": candidate.verified_program_manifest_root,
            "candidate_settlement_commitment": _derive_capability_commitment(candidate),
            "settlement_effect_plan_commitment": (
                candidate.settlement_effect_plan_commitment
            ),
            "pre_state_root": candidate.pre_state_root,
            "post_state_root": candidate.post_state_root,
            "economic_action_id": candidate.economic_action_id,
            "authorization_nullifier": candidate.authorization_nullifier,
            "authorization_grant_spend_nullifier": (
                candidate.authorization_grant_spend_nullifier
            ),
            "cell_transitions_root": candidate.cell_transitions_root,
            "proof_journal_hash": _candidate_journal_hash(candidate),
        },
        "prior_application_checkpoint": {
            "sequence": cursor.sequence,
            "checkpoint_hash": cursor.checkpoint_hash,
        },
        "settlement_replay_observation": (
            settlement_replay_observation._canonical_projection_for_finality_adapter()
        ),
        "header": snapshot.header,
        "checkpoint": snapshot.checkpoint,
        "validator_set": snapshot.validator_set,
        "scheduled_header_admission": dict(scheduled_header_admission),
        "proposer_envelope": snapshot.proposer_envelope,
        "proposer_authorship_admission": dict(proposer_authorship_admission),
        "registry": snapshot.registry,
        "envelopes": list(snapshot.envelopes),
        "live_quorum_admission": dict(admission),
        "claims": {
            "exact_settlement_envelope_replay_bound": True,
            "exact_header_derived_from_sealed_replay": True,
            "candidate_effect_and_state_bindings_checked": True,
            "cryptographic_checkpoint_quorum_supported": True,
            "proof_receipt_authentication_established": False,
            "application_domain_to_ledger_chain_binding_established": False,
            "public_data_retrievability_established": False,
            "canonical_conflicting_checkpoint_selection_established": False,
            "exact_replay_material_authenticated": True,
            "replay_material_commitment_bound": True,
            "durable_settlement_replay_material_persisted": False,
            "durable_settlement_replay_reverified": False,
            "hostile_same_interpreter_resistance_established": False,
            "release_authority": False,
            "settlement_authority": False,
            "production_authority": False,
        },
    }
    encoded = canonical_json_bytes_v0(body)
    if not encoded or len(encoded) > MAX_FINALITY_EVIDENCE_BYTES_V2:
        raise ValueError("canonical finality evidence exceeds checkpoint-finality V3 bound")
    return encoded


def _derive_exact_finality_capability(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    policy: _GovernedSpotV7OperationalPolicyV2,
    cursor: ZenoLedgerCheckpointFinalityCursorV1,
    checkpoint: Mapping[str, Any],
    evidence_bytes: bytes,
) -> _AuthenticatedExactCheckpointFinalityTransitionV2:
    store_policy = policy._policy_for_atomic_store()
    store_settlement = _seal_test_only_spot_v7_settlement_v1(candidate)
    artifacts = _build_test_only_checkpoint_finality_artifacts_v2(
        policy=store_policy,
        settlement=store_settlement,
        prior_application_checkpoint_sequence=cursor.sequence,
        prior_application_checkpoint_hash=cursor.checkpoint_hash,
        next_application_checkpoint_hash=_require_hash(
            checkpoint["header_hash"],
            name="checkpoint header hash",
        ),
        exact_finality_evidence_bytes=evidence_bytes,
    )
    projection = _AuthenticatedCheckpointFinalityProjectionV2(
        application_id=store_policy.application_id,
        chain_or_domain_id=store_policy.chain_or_domain_id,
        epoch_id=artifacts.epoch_id,
        proof_journal_hash=artifacts.proof_journal_hash,
        post_state_root=artifacts.post_state_root,
        policy_root=artifacts.policy_root,
        certificate_root=artifacts.certificate_root,
        finality_evidence_root=artifacts.finality_evidence_root,
        prior_application_checkpoint_sequence=(artifacts.prior_application_checkpoint_sequence),
        prior_application_checkpoint_hash=artifacts.prior_application_checkpoint_hash,
        next_application_checkpoint_sequence=(artifacts.next_application_checkpoint_sequence),
        next_application_checkpoint_hash=artifacts.next_application_checkpoint_hash,
    )
    return _AuthenticatedExactCheckpointFinalityTransitionV2(
        projection,
        exact_certificate_bytes=artifacts.exact_certificate_bytes,
        exact_finality_evidence_bytes=artifacts.exact_finality_evidence_bytes,
        seal=_AUTHENTICATED_EXACT_CHECKPOINT_FINALITY_SEAL_V2,
    )


def _derive_exact_finality_capability_v3(
    *,
    candidate: _SpotV7SettlementCandidateInputV1,
    policy: _GovernedSpotV7OperationalPolicyV2,
    cursor: ZenoLedgerCheckpointFinalityCursorV1,
    checkpoint: Mapping[str, Any],
    evidence_bytes: bytes,
) -> _AuthenticatedExactCheckpointFinalityTransitionV3:
    store_policy = policy._policy_for_atomic_store()
    store_settlement = _seal_test_only_spot_v7_settlement_v1(candidate)
    artifacts = _build_test_only_checkpoint_finality_artifacts_v2(
        policy=store_policy,
        settlement=store_settlement,
        prior_application_checkpoint_sequence=cursor.sequence,
        prior_application_checkpoint_hash=cursor.checkpoint_hash,
        next_application_checkpoint_hash=_require_hash(
            checkpoint["header_hash"],
            name="checkpoint header hash",
        ),
        exact_finality_evidence_bytes=evidence_bytes,
    )
    projection = _AuthenticatedCheckpointFinalityProjectionV3(
        application_id=store_policy.application_id,
        chain_or_domain_id=store_policy.chain_or_domain_id,
        epoch_id=artifacts.epoch_id,
        proof_journal_hash=artifacts.proof_journal_hash,
        post_state_root=artifacts.post_state_root,
        policy_root=artifacts.policy_root,
        certificate_root=artifacts.certificate_root,
        finality_evidence_root=artifacts.finality_evidence_root,
        prior_application_checkpoint_sequence=(
            artifacts.prior_application_checkpoint_sequence
        ),
        prior_application_checkpoint_hash=artifacts.prior_application_checkpoint_hash,
        next_application_checkpoint_sequence=(
            artifacts.next_application_checkpoint_sequence
        ),
        next_application_checkpoint_hash=artifacts.next_application_checkpoint_hash,
    )
    return _AuthenticatedExactCheckpointFinalityTransitionV3(
        projection,
        exact_certificate_bytes=artifacts.exact_certificate_bytes,
        exact_finality_evidence_bytes=artifacts.exact_finality_evidence_bytes,
        seal=_AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    )


def _require_cursor(value: object) -> ZenoLedgerCheckpointFinalityCursorV1:
    if type(value) is not ZenoLedgerCheckpointFinalityCursorV1:
        raise TypeError("prior_cursor must be exact ZenoLedgerCheckpointFinalityCursorV1")
    return value


def _candidate_journal_hash(candidate: _SpotV7SettlementCandidateInputV1) -> str:
    return "0x" + hashlib.sha256(candidate.exact_v7_journal_bytes).hexdigest()


def _sha256_prefixed(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _require_checks(checks: Sequence[tuple[bool, str]]) -> None:
    for accepted, code in checks:
        if not accepted:
            raise SpotV7ZenoLedgerFinalityBindingErrorV1(code)


__all__ = [
    "SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V2",
    "SPOT_V7_ZENO_LEDGER_FINALITY_EVIDENCE_SCHEMA_V3",
    "SPOT_V7_ZENO_LEDGER_PROPOSER_AUTHORSHIP_ADMISSION_SCHEMA_V1",
    "SpotV7ZenoLedgerCheckpointFinalityAdapterV2",
    "SpotV7ZenoLedgerCheckpointFinalityAdapterV3",
    "SpotV7ZenoLedgerFinalityBindingErrorV1",
    "ZenoLedgerCheckpointFinalityCursorV1",
    "derive_zeno_ledger_external_finality_policy_hash_v2",
    "derive_zeno_ledger_finality_network_id_v1",
    "derive_zeno_ledger_finality_protocol_id_v2",
    "derive_zeno_ledger_finality_protocol_id_v3",
    "derive_zeno_ledger_proposer_authorship_payload_hash_v1",
]
