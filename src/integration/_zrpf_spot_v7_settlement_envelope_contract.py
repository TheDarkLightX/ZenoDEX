"""Private types for authority-false Spot V7 settlement-envelope replay."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import TYPE_CHECKING, Any, NoReturn, SupportsIndex, final

from src.core.dex import DexState
from src.integration.zeno_ledger_replay import (
    load_replay_snapshot_v0,
    parse_replay_engine_config_v0,
    replay_engine_config_digest_v0,
)
from src.integration.zeno_ledger_v0 import (
    ZERO_ROOT_V0,
    canonical_body_root_v0,
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
    dex_state_root_v0,
    hash_v0,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import _hash_bytes

if TYPE_CHECKING:
    from src.integration._zrpf_spot_v7_settlement_replay_packet import (
        _DurableSpotV7SettlementReplayPacketV2,
    )

SPOT_V7_SETTLEMENT_ENVELOPE_SCHEMA_V1 = "zenodex/zrpf/spot_v7/settlement_envelope/v1"
SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1 = "restricted_singleton_spot_state_root_v5"
SPOT_V7_SETTLEMENT_ENVELOPE_RECEIPT_SCHEMA_V1 = (
    "zenodex/zrpf/spot_v7/settlement_envelope_receipt/v1"
)
SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V1 = (
    "zenodex/zrpf/spot_v7/settlement_envelope_replay_observation/v1"
)
SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V2 = (
    "zenodex/zrpf/spot_v7/settlement_envelope_replay_observation/v2"
)
SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_PROFILE_V2 = "exact_config_and_pre_state_retained_replay_v2"

ENVELOPE_PROPOSAL_HASH_DOMAIN_V1 = "zrpf_spot_v7_settlement_envelope_proposal_v1"
ENVELOPE_RECEIPT_HASH_DOMAIN_V1 = "zrpf_spot_v7_settlement_envelope_receipt_v1"
SPOT_V7_SETTLEMENT_EFFECT_IDS_ROOT_DOMAIN_V1 = "zrpf_spot_v7_settlement_envelope_effect_ids_v1"
SPOT_V7_SETTLEMENT_REPLAY_MATERIAL_ROOT_DOMAIN_V2 = "zrpf_spot_v7_settlement_replay_material_v2"
_MAX_EXACT_JSON_OBJECT_BYTES_V2 = 24 * 1_024 * 1_024
_MAX_EXACT_JSON_OBJECT_DEPTH_V2 = 64


class SpotV7SettlementEnvelopeReplayErrorV1(ValueError):
    """Stable fail-closed rejection at the bounded replay boundary."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_SETTLEMENT_ENVELOPE_REPLAY_REJECTED: {code}")


@dataclass(frozen=True, slots=True)
class _SpotV7SettlementReplayProjectionV1:
    chain_id: str
    height: int
    header_hash: str
    parent_header_hash: str | None
    body_root: str
    config_digest: str
    candidate_settlement_commitment: str
    proof_journal_hash: str
    envelope_sha256: str
    envelope_proposal_hash: str
    receipt_hash: str
    receipt_accepted: bool
    settlement_effect_plan_commitment: str
    pre_state_root: str
    post_state_root: str
    economic_action_id: str
    authorization_nullifier: str
    authorization_grant_spend_nullifier: str
    cell_transitions_root: str
    asset_effect_ids_root: str
    observation_evidence_root: str

    def __post_init__(self) -> None:
        if type(self.chain_id) is not str or not self.chain_id:
            raise ValueError("settlement replay chain_id must be non-empty")
        if type(self.height) is not int or isinstance(self.height, bool) or self.height < 0:
            raise ValueError("settlement replay height must be non-negative")
        if type(self.receipt_accepted) is not bool:
            raise TypeError("settlement replay receipt_accepted must be bool")
        excluded = {"chain_id", "height", "parent_header_hash", "receipt_accepted"}
        for name, value in asdict(self).items():
            if name not in excluded:
                _hash_bytes(value, name=f"settlement replay {name}")
        if self.parent_header_hash is not None:
            _hash_bytes(
                self.parent_header_hash,
                name="settlement replay parent_header_hash",
            )


@dataclass(frozen=True, slots=True)
class _SpotV7SettlementReplayProjectionV2(_SpotV7SettlementReplayProjectionV1):
    """V1 replay facts plus exact retained-material commitments."""

    config_document_sha256: str
    pre_state_snapshot_sha256: str
    replay_material_root: str

    def __post_init__(self) -> None:
        _SpotV7SettlementReplayProjectionV1.__post_init__(self)
        for name, value in (
            ("config_document_sha256", self.config_document_sha256),
            ("pre_state_snapshot_sha256", self.pre_state_snapshot_sha256),
            ("replay_material_root", self.replay_material_root),
        ):
            _hash_bytes(value, name=f"settlement replay {name}")


@dataclass(frozen=True, slots=True)
class _ExactSpotV7SettlementReplayMaterialV2:
    """Immutable data only; possession does not establish replay authority."""

    exact_config_document_bytes: bytes
    exact_pre_state_snapshot_bytes: bytes

    def __post_init__(self) -> None:
        for name, value in (
            ("config document", self.exact_config_document_bytes),
            ("pre-state snapshot", self.exact_pre_state_snapshot_bytes),
        ):
            if type(value) is not bytes or not value:
                raise TypeError(f"exact settlement replay {name} must be non-empty bytes")


@dataclass(frozen=True, slots=True)
class _EnvelopeEvaluationV1:
    envelope_bytes: bytes
    proposal_hash: str
    receipt: dict[str, Any]
    post_state: DexState | None


class _SettlementReplayObservationSealV1:
    __slots__ = ()


_SETTLEMENT_REPLAY_OBSERVATION_SEAL_V1 = _SettlementReplayObservationSealV1()


class _SettlementReplayObservationSealV2:
    __slots__ = ()


_SETTLEMENT_REPLAY_OBSERVATION_SEAL_V2 = _SettlementReplayObservationSealV2()


class _NonTransferableSettlementReplayV1:
    __slots__ = ()

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("Spot V7 settlement replay observation cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("Spot V7 settlement replay observation cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("Spot V7 settlement replay observation cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("Spot V7 settlement replay observation cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("Spot V7 settlement replay observation cannot be serialized")


@final
class _AuthenticatedSpotV7SettlementReplayObservationV1(_NonTransferableSettlementReplayV1):
    """Private exact replay observation with every authority claim disabled."""

    __slots__ = (
        "_projection",
        "_exact_header_bytes",
        "_exact_body_bytes",
        "_exact_envelope_bytes",
        "_exact_receipt_bytes",
        "_exact_evidence_bytes",
        "_seal",
    )

    _projection: _SpotV7SettlementReplayProjectionV1
    _exact_header_bytes: bytes
    _exact_body_bytes: bytes
    _exact_envelope_bytes: bytes
    _exact_receipt_bytes: bytes
    _exact_evidence_bytes: bytes
    _seal: _SettlementReplayObservationSealV1

    def __init__(
        self,
        projection: _SpotV7SettlementReplayProjectionV1,
        *,
        exact_header_bytes: bytes,
        exact_body_bytes: bytes,
        exact_envelope_bytes: bytes,
        exact_receipt_bytes: bytes,
        exact_evidence_bytes: bytes,
        seal: _SettlementReplayObservationSealV1,
    ) -> None:
        if type(projection) is not _SpotV7SettlementReplayProjectionV1:
            raise TypeError("settlement replay projection has the wrong type")
        if seal is not _SETTLEMENT_REPLAY_OBSERVATION_SEAL_V1:
            raise TypeError("settlement replay observation requires its private seal")
        exact_values = (
            ("header", exact_header_bytes),
            ("body", exact_body_bytes),
            ("envelope", exact_envelope_bytes),
            ("receipt", exact_receipt_bytes),
            ("evidence", exact_evidence_bytes),
        )
        for name, value in exact_values:
            if type(value) is not bytes or not value:
                raise TypeError(f"exact settlement replay {name} must be non-empty bytes")
        _require_exact_artifact_bindings(
            projection,
            header_bytes=exact_header_bytes,
            body_bytes=exact_body_bytes,
            envelope_bytes=exact_envelope_bytes,
            receipt_bytes=exact_receipt_bytes,
            evidence_bytes=exact_evidence_bytes,
        )
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_exact_header_bytes", exact_header_bytes)
        object.__setattr__(self, "_exact_body_bytes", exact_body_bytes)
        object.__setattr__(self, "_exact_envelope_bytes", exact_envelope_bytes)
        object.__setattr__(self, "_exact_receipt_bytes", exact_receipt_bytes)
        object.__setattr__(self, "_exact_evidence_bytes", exact_evidence_bytes)
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _SETTLEMENT_REPLAY_OBSERVATION_SEAL_V1

    def _projection_for_finality_adapter(self) -> _SpotV7SettlementReplayProjectionV1:
        if not self._has_private_seal():
            raise TypeError("settlement replay observation lacks its private seal")
        return self._projection

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def application_domain_to_ledger_chain_binding_established(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


@final
class _AuthenticatedSpotV7SettlementReplayObservationV2(_NonTransferableSettlementReplayV1):
    """Private replay observation retaining exact history-replay inputs."""

    __slots__ = (
        "_durable_packet",
        "_seal",
    )

    _durable_packet: _DurableSpotV7SettlementReplayPacketV2
    _seal: _SettlementReplayObservationSealV2

    def __init__(
        self,
        projection: _SpotV7SettlementReplayProjectionV2,
        *,
        exact_header_bytes: bytes,
        exact_body_bytes: bytes,
        exact_envelope_bytes: bytes,
        exact_receipt_bytes: bytes,
        exact_evidence_bytes: bytes,
        exact_config_document_bytes: bytes,
        exact_pre_state_snapshot_bytes: bytes,
        seal: _SettlementReplayObservationSealV2,
    ) -> None:
        if type(projection) is not _SpotV7SettlementReplayProjectionV2:
            raise TypeError("settlement replay V2 projection has the wrong type")
        if seal is not _SETTLEMENT_REPLAY_OBSERVATION_SEAL_V2:
            raise TypeError("settlement replay V2 observation requires its private seal")
        from src.integration._zrpf_spot_v7_settlement_replay_packet import (
            _new_durable_spot_v7_settlement_replay_packet_v2,
            _UntrustedPersistedSpotV7SettlementReplayInputsV2,
        )

        packet = _new_durable_spot_v7_settlement_replay_packet_v2(
            _UntrustedPersistedSpotV7SettlementReplayInputsV2(
                exact_projection_bytes=canonical_json_bytes_v0(asdict(projection)),
                exact_header_bytes=exact_header_bytes,
                exact_body_bytes=exact_body_bytes,
                exact_envelope_bytes=exact_envelope_bytes,
                exact_receipt_bytes=exact_receipt_bytes,
                exact_evidence_bytes=exact_evidence_bytes,
                exact_config_document_bytes=exact_config_document_bytes,
                exact_pre_state_snapshot_bytes=exact_pre_state_snapshot_bytes,
            )
        )
        object.__setattr__(self, "_durable_packet", packet)
        object.__setattr__(self, "_seal", seal)

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _SETTLEMENT_REPLAY_OBSERVATION_SEAL_V2

    def _header_for_finality_adapter(self) -> dict[str, Any]:
        _require_settlement_replay_observation_v2(self)
        persisted = self._durable_packet._persisted_inputs_for_storage()
        return _decode_exact_json_object(
            persisted.exact_header_bytes,
            name="sealed settlement replay header",
        )

    def _projection_for_finality_adapter(self) -> _SpotV7SettlementReplayProjectionV2:
        _require_settlement_replay_observation_v2(self)
        return self._durable_packet._projection_for_history_reverification()

    def _canonical_projection_for_finality_adapter(self) -> dict[str, Any]:
        _require_settlement_replay_observation_v2(self)
        return asdict(self._durable_packet._projection_for_history_reverification())

    def _durable_replay_packet_for_history_reverification(
        self,
    ) -> _DurableSpotV7SettlementReplayPacketV2:
        _require_settlement_replay_observation_v2(self)
        return self._durable_packet

    def _exact_replay_material_for_history_reverification(
        self,
    ) -> _ExactSpotV7SettlementReplayMaterialV2:
        _require_settlement_replay_observation_v2(self)
        persisted = self._durable_packet._persisted_inputs_for_storage()
        return _ExactSpotV7SettlementReplayMaterialV2(
            exact_config_document_bytes=persisted.exact_config_document_bytes,
            exact_pre_state_snapshot_bytes=persisted.exact_pre_state_snapshot_bytes,
        )

    @property
    def exact_replay_material_authenticated(self) -> bool:
        _require_settlement_replay_observation_v2(self)
        return True

    @property
    def durable_settlement_replay_reverification_material_retained(self) -> bool:
        _require_settlement_replay_observation_v2(self)
        return True

    @property
    def durable_settlement_replay_reverified(self) -> bool:
        return False

    @property
    def application_domain_to_ledger_chain_binding_established(self) -> bool:
        return False

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _require_exact_artifact_bindings(
    projection: _SpotV7SettlementReplayProjectionV1,
    *,
    header_bytes: bytes,
    body_bytes: bytes,
    envelope_bytes: bytes,
    receipt_bytes: bytes,
    evidence_bytes: bytes,
) -> None:
    header = _decode_exact_json_object(header_bytes, name="sealed header")
    body = _decode_exact_json_object(body_bytes, name="sealed body")
    envelope = _decode_exact_json_object(envelope_bytes, name="sealed envelope")
    receipt = _decode_exact_json_object(receipt_bytes, name="sealed receipt")
    evidence = _decode_exact_json_object(evidence_bytes, name="sealed replay evidence")
    if canonical_header_hash_v0(header) != projection.header_hash:
        raise ValueError("exact header bytes disagree with replay projection")
    if canonical_body_root_v0(body) != projection.body_root:
        raise ValueError("exact body bytes disagree with replay projection")
    if _sha256(envelope_bytes) != projection.envelope_sha256:
        raise ValueError("exact envelope bytes disagree with replay projection")
    if hash_v0(ENVELOPE_RECEIPT_HASH_DOMAIN_V1, receipt) != projection.receipt_hash:
        raise ValueError("exact receipt bytes disagree with replay projection")
    if _sha256(evidence_bytes) != projection.observation_evidence_root:
        raise ValueError("exact evidence bytes disagree with replay projection")
    _require_header_projection_binding(projection, header)
    _require_body_envelope_binding(projection, body, envelope_bytes)
    _require_envelope_projection_binding(projection, envelope, receipt_bytes)
    _require_receipt_projection_binding(projection, receipt)
    _require_evidence_projection_binding(projection, evidence)


def _require_header_projection_binding(
    projection: _SpotV7SettlementReplayProjectionV1,
    header: dict[str, Any],
) -> None:
    _require_exact_fields(
        header,
        {
            "chain_id": projection.chain_id,
            "height": projection.height,
            "prev_header_hash": projection.parent_header_hash or ZERO_ROOT_V0,
            "body_root": projection.body_root,
            "config_digest": projection.config_digest,
            "proof_journal_hash": projection.proof_journal_hash,
            "pre_state_root": projection.pre_state_root,
            "post_state_root": projection.post_state_root,
        },
        name="sealed header",
    )


def _require_body_envelope_binding(
    projection: _SpotV7SettlementReplayProjectionV1,
    body: dict[str, Any],
    envelope_bytes: bytes,
) -> None:
    envelopes = body.get("settlement_envelopes")
    if type(envelopes) is not list or len(envelopes) != 1:
        raise ValueError("sealed body must contain one exact settlement envelope")
    if canonical_json_bytes_v0(envelopes[0]) != envelope_bytes:
        raise ValueError("sealed body envelope disagrees with exact envelope bytes")
    evidence = body.get("evidence")
    if type(evidence) is not dict:
        raise ValueError("sealed body evidence must be an exact object")
    proof_receipts = evidence.get("proof_receipts")
    if type(proof_receipts) is not list or len(proof_receipts) != 1:
        raise ValueError("sealed body must contain one proof receipt projection")
    proof_receipt = proof_receipts[0]
    if type(proof_receipt) is not dict:
        raise ValueError("sealed body proof receipt projection must be an exact object")
    _require_exact_fields(
        proof_receipt,
        {"proof_journal_hash": projection.proof_journal_hash},
        name="sealed body proof receipt projection",
    )


def _require_envelope_projection_binding(
    projection: _SpotV7SettlementReplayProjectionV1,
    envelope: dict[str, Any],
    receipt_bytes: bytes,
) -> None:
    _require_exact_fields(
        envelope,
        {
            "schema": SPOT_V7_SETTLEMENT_ENVELOPE_SCHEMA_V1,
            "profile": SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1,
        },
        name="sealed envelope",
    )
    proposal = envelope.get("proposal")
    committed_receipt = envelope.get("expected_receipt")
    if type(proposal) is not dict or type(committed_receipt) is not dict:
        raise ValueError("sealed envelope proposal and receipt must be exact objects")
    if canonical_json_bytes_v0(committed_receipt) != receipt_bytes:
        raise ValueError("sealed envelope receipt disagrees with exact receipt bytes")
    _require_exact_fields(
        proposal,
        {
            "candidate_settlement_commitment": (projection.candidate_settlement_commitment),
            "proof_journal_sha256": projection.proof_journal_hash,
            "settlement_effect_plan_commitment": (projection.settlement_effect_plan_commitment),
            "pre_state_root": projection.pre_state_root,
            "post_state_root": projection.post_state_root,
            "economic_action_id": projection.economic_action_id,
            "authorization_nullifier": projection.authorization_nullifier,
            "authorization_grant_spend_nullifier": (projection.authorization_grant_spend_nullifier),
            "cell_transitions_root": projection.cell_transitions_root,
        },
        name="sealed envelope proposal",
    )
    if hash_v0(ENVELOPE_PROPOSAL_HASH_DOMAIN_V1, proposal) != projection.envelope_proposal_hash:
        raise ValueError("sealed envelope proposal hash disagrees with projection")
    effects = proposal.get("asset_effects")
    if type(effects) is not list:
        raise ValueError("sealed envelope asset effects must be an exact list")
    effect_ids: list[str] = []
    for effect in effects:
        if type(effect) is not dict or type(effect.get("effect_id")) is not str:
            raise ValueError("sealed envelope asset effect identity is malformed")
        effect_ids.append(effect["effect_id"])
    effect_ids_root = hash_v0(
        SPOT_V7_SETTLEMENT_EFFECT_IDS_ROOT_DOMAIN_V1,
        {"effect_ids": effect_ids},
    )
    if effect_ids_root != projection.asset_effect_ids_root:
        raise ValueError("sealed envelope effect IDs disagree with projection")


def _require_receipt_projection_binding(
    projection: _SpotV7SettlementReplayProjectionV1,
    receipt: dict[str, Any],
) -> None:
    _require_exact_fields(
        receipt,
        {
            "schema": SPOT_V7_SETTLEMENT_ENVELOPE_RECEIPT_SCHEMA_V1,
            "profile": SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1,
            "envelope_proposal_hash": projection.envelope_proposal_hash,
            "candidate_settlement_commitment": (projection.candidate_settlement_commitment),
            "proof_journal_sha256": projection.proof_journal_hash,
            "settlement_effect_plan_commitment": (projection.settlement_effect_plan_commitment),
            "economic_action_id": projection.economic_action_id,
            "accepted": projection.receipt_accepted,
            "reject_code": None,
            "state_changed": projection.pre_state_root != projection.post_state_root,
            "pre_state_root": projection.pre_state_root,
            "post_state_root": projection.post_state_root,
        },
        name="sealed receipt",
    )


def _require_evidence_projection_binding(
    projection: _SpotV7SettlementReplayProjectionV1,
    evidence: dict[str, Any],
) -> None:
    expected_schema = SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V1
    if type(projection) is _SpotV7SettlementReplayProjectionV2:
        expected_schema = SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V2
    _require_exact_fields(
        evidence,
        {
            "schema": expected_schema,
            "candidate_settlement_commitment": (projection.candidate_settlement_commitment),
            "header_hash": projection.header_hash,
            "body_root": projection.body_root,
            "envelope_sha256": projection.envelope_sha256,
            "receipt_hash": projection.receipt_hash,
        },
        name="sealed replay evidence",
    )
    claims = evidence.get("claims")
    if type(claims) is not dict:
        raise ValueError("sealed replay evidence claims must be an exact object")
    for field in (
        "application_domain_to_ledger_chain_binding_established",
        "proof_receipt_authentication_established",
        "settlement_authority",
        "release_authority",
        "production_authority",
    ):
        if claims.get(field) is not False:
            raise ValueError(f"sealed replay evidence claim must remain false: {field}")
    if type(projection) is _SpotV7SettlementReplayProjectionV2:
        _require_v2_evidence_projection_binding(projection, evidence, claims)


def _require_v2_evidence_projection_binding(
    projection: _SpotV7SettlementReplayProjectionV2,
    evidence: dict[str, Any],
    claims: dict[str, Any],
) -> None:
    _require_exact_fields(
        evidence,
        {
            "profile": SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_PROFILE_V2,
            "config_digest": projection.config_digest,
            "config_document_sha256": projection.config_document_sha256,
            "pre_state_root": projection.pre_state_root,
            "pre_state_snapshot_sha256": projection.pre_state_snapshot_sha256,
            "replay_material_root": projection.replay_material_root,
        },
        name="sealed replay V2 evidence",
    )
    _require_exact_fields(
        claims,
        {
            "exact_replay_material_authenticated": True,
            "durable_settlement_replay_reverification_material_retained": True,
            "durable_settlement_replay_reverified": False,
        },
        name="sealed replay V2 evidence claims",
    )


def _require_exact_fields(
    value: dict[str, Any],
    expected: dict[str, object],
    *,
    name: str,
) -> None:
    for field, expected_value in expected.items():
        if field not in value or not _exact_json_equal(value[field], expected_value):
            raise ValueError(f"{name} field disagrees with replay projection: {field}")


def _exact_json_equal(left: object, right: object) -> bool:
    return canonical_json_bytes_v0({"value": left}) == canonical_json_bytes_v0({"value": right})


def _require_exact_replay_material_bindings_v2(
    projection: _SpotV7SettlementReplayProjectionV2,
    *,
    config_document_bytes: bytes,
    pre_state_snapshot_bytes: bytes,
) -> None:
    if _sha256(config_document_bytes) != projection.config_document_sha256:
        raise ValueError("exact config bytes disagree with replay projection")
    if _sha256(pre_state_snapshot_bytes) != projection.pre_state_snapshot_sha256:
        raise ValueError("exact pre-state bytes disagree with replay projection")
    config_document = _decode_exact_json_object(
        config_document_bytes,
        name="sealed replay config document",
    )
    config, canonical_config = parse_replay_engine_config_v0(config_document)
    if canonical_json_bytes_v0(canonical_config) != config_document_bytes:
        raise ValueError("sealed replay config document is not canonical")
    if replay_engine_config_digest_v0(canonical_config) != projection.config_digest:
        raise ValueError("sealed replay config digest disagrees with projection")
    if config.chain_id != projection.chain_id:
        raise ValueError("sealed replay config chain disagrees with projection")
    pre_snapshot = _decode_exact_json_object(
        pre_state_snapshot_bytes,
        name="sealed replay pre-state snapshot",
    )
    pre_state, canonical_snapshot = load_replay_snapshot_v0(pre_snapshot)
    if canonical_json_bytes_v0(canonical_snapshot) != pre_state_snapshot_bytes:
        raise ValueError("sealed replay pre-state snapshot is not canonical")
    if dex_state_root_v0(pre_state) != projection.pre_state_root:
        raise ValueError("sealed replay pre-state root disagrees with projection")
    expected_material_root = _derive_replay_material_root_v2(
        chain_id=projection.chain_id,
        height=projection.height,
        candidate_settlement_commitment=projection.candidate_settlement_commitment,
        envelope_sha256=projection.envelope_sha256,
        config_digest=projection.config_digest,
        config_document_sha256=projection.config_document_sha256,
        pre_state_root=projection.pre_state_root,
        pre_state_snapshot_sha256=projection.pre_state_snapshot_sha256,
    )
    if expected_material_root != projection.replay_material_root:
        raise ValueError("exact replay material root disagrees with projection")


def _derive_replay_material_root_v2(
    *,
    chain_id: str,
    height: int,
    candidate_settlement_commitment: str,
    envelope_sha256: str,
    config_digest: str,
    config_document_sha256: str,
    pre_state_root: str,
    pre_state_snapshot_sha256: str,
) -> str:
    return hash_v0(
        SPOT_V7_SETTLEMENT_REPLAY_MATERIAL_ROOT_DOMAIN_V2,
        {
            "schema": SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V2,
            "profile": SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_PROFILE_V2,
            "chain_id": chain_id,
            "height": height,
            "candidate_settlement_commitment": candidate_settlement_commitment,
            "envelope_sha256": envelope_sha256,
            "config_digest": config_digest,
            "config_document_sha256": config_document_sha256,
            "pre_state_root": pre_state_root,
            "pre_state_snapshot_sha256": pre_state_snapshot_sha256,
        },
    )


def _require_settlement_replay_observation_v2(
    value: object,
) -> _AuthenticatedSpotV7SettlementReplayObservationV2:
    if type(value) is not _AuthenticatedSpotV7SettlementReplayObservationV2:
        raise TypeError("replay observation must be the exact private V2 observation")
    if not value._has_private_seal():
        raise TypeError("replay observation V2 lacks its module-private seal")
    return value


def _decode_exact_json_object(value: bytes, *, name: str) -> dict[str, Any]:
    if type(value) is not bytes or not value or len(value) > _MAX_EXACT_JSON_OBJECT_BYTES_V2:
        raise ValueError(f"{name} exceeds the exact JSON byte bound")
    _require_bounded_json_nesting(value, name=name)
    try:
        decoded = json.loads(value)
        canonical = canonical_json_bytes_v0(decoded)
    except (TypeError, ValueError, RecursionError) as exc:
        raise ValueError(f"{name} is not a bounded JSON object") from exc
    if type(decoded) is not dict or canonical != value:
        raise ValueError(f"{name} is not an exact canonical JSON object")
    return decoded


def _require_bounded_json_nesting(value: bytes, *, name: str) -> None:
    depth = 0
    in_string = False
    escaped = False
    for byte in value:
        if in_string:
            if escaped:
                escaped = False
            elif byte == 0x5C:
                escaped = True
            elif byte == 0x22:
                in_string = False
            continue
        if byte == 0x22:
            in_string = True
        elif byte in (0x5B, 0x7B):
            depth += 1
            if depth > _MAX_EXACT_JSON_OBJECT_DEPTH_V2:
                raise ValueError(f"{name} exceeds the exact JSON nesting bound")
        elif byte in (0x5D, 0x7D):
            depth -= 1
            if depth < 0:
                raise ValueError(f"{name} has invalid JSON nesting")
    if depth != 0 or in_string:
        raise ValueError(f"{name} has invalid JSON nesting")


def _sha256(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()
