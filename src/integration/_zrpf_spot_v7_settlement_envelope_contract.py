"""Private types for authority-false Spot V7 settlement-envelope replay."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Any, NoReturn, SupportsIndex, final

from src.core.dex import DexState
from src.integration.zeno_ledger_v0 import (
    canonical_body_root_v0,
    canonical_header_hash_v0,
    canonical_json_bytes_v0,
    hash_v0,
)
from src.integration.zrpf_spot_v7_atomic_settlement_types import _hash_bytes

SPOT_V7_SETTLEMENT_ENVELOPE_SCHEMA_V1 = "zenodex/zrpf/spot_v7/settlement_envelope/v1"
SPOT_V7_SETTLEMENT_ENVELOPE_PROFILE_V1 = "restricted_singleton_spot_state_root_v5"
SPOT_V7_SETTLEMENT_ENVELOPE_RECEIPT_SCHEMA_V1 = (
    "zenodex/zrpf/spot_v7/settlement_envelope_receipt/v1"
)
SPOT_V7_SETTLEMENT_REPLAY_OBSERVATION_SCHEMA_V1 = (
    "zenodex/zrpf/spot_v7/settlement_envelope_replay_observation/v1"
)

ENVELOPE_PROPOSAL_HASH_DOMAIN_V1 = "zrpf_spot_v7_settlement_envelope_proposal_v1"
ENVELOPE_RECEIPT_HASH_DOMAIN_V1 = "zrpf_spot_v7_settlement_envelope_receipt_v1"


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
class _EnvelopeEvaluationV1:
    envelope_bytes: bytes
    proposal_hash: str
    receipt: dict[str, Any]
    post_state: DexState | None


class _SettlementReplayObservationSealV1:
    __slots__ = ()


_SETTLEMENT_REPLAY_OBSERVATION_SEAL_V1 = _SettlementReplayObservationSealV1()


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


def _require_exact_artifact_bindings(
    projection: _SpotV7SettlementReplayProjectionV1,
    *,
    header_bytes: bytes,
    body_bytes: bytes,
    envelope_bytes: bytes,
    receipt_bytes: bytes,
    evidence_bytes: bytes,
) -> None:
    if _sha256(envelope_bytes) != projection.envelope_sha256:
        raise ValueError("exact envelope bytes disagree with replay projection")
    receipt = _decode_exact_json_object(receipt_bytes, name="receipt")
    if hash_v0(ENVELOPE_RECEIPT_HASH_DOMAIN_V1, receipt) != projection.receipt_hash:
        raise ValueError("exact receipt bytes disagree with replay projection")
    if _sha256(evidence_bytes) != projection.observation_evidence_root:
        raise ValueError("exact evidence bytes disagree with replay projection")
    header = _decode_exact_json_object(header_bytes, name="sealed header")
    if canonical_header_hash_v0(header) != projection.header_hash:
        raise ValueError("exact header bytes disagree with replay projection")
    body = _decode_exact_json_object(body_bytes, name="sealed body")
    if canonical_body_root_v0(body) != projection.body_root:
        raise ValueError("exact body bytes disagree with replay projection")


def _decode_exact_json_object(value: bytes, *, name: str) -> dict[str, Any]:
    decoded = json.loads(value)
    if type(decoded) is not dict or canonical_json_bytes_v0(decoded) != value:
        raise ValueError(f"{name} is not an exact canonical JSON object")
    return decoded


def _sha256(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()
