"""Private immutable packet for exact Spot V7 current-record replay persistence.

The packet authenticates internal byte-to-projection consistency only. It is
data for a later deterministic replay and carries no settlement authority.
For a non-genesis record, the exact parent header remains a separately supplied,
hash-bound history prerequisite and is not retained by this packet.
"""

from __future__ import annotations

from dataclasses import dataclass, fields
from typing import NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_settlement_envelope_codec import (
    MAX_ENVELOPE_BYTES_V1,
    MAX_HEADER_OR_CONFIG_BYTES_V1,
    MAX_LEDGER_BODY_BYTES_V1,
    MAX_PRE_STATE_SNAPSHOT_BYTES_V1,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    _decode_exact_json_object,
    _require_exact_artifact_bindings,
    _require_exact_replay_material_bindings_v2,
    _SpotV7SettlementReplayProjectionV2,
)

MAX_REPLAY_PROJECTION_BYTES_V2 = 64 * 1_024
MAX_REPLAY_RECEIPT_BYTES_V2 = MAX_ENVELOPE_BYTES_V1
MAX_REPLAY_EVIDENCE_BYTES_V2 = 512 * 1_024


@dataclass(frozen=True, slots=True)
class _UntrustedPersistedSpotV7SettlementReplayInputsV2:
    """Bounded persisted data. Construction does not establish replay validity."""

    exact_projection_bytes: bytes
    exact_header_bytes: bytes
    exact_body_bytes: bytes
    exact_envelope_bytes: bytes
    exact_receipt_bytes: bytes
    exact_evidence_bytes: bytes
    exact_config_document_bytes: bytes
    exact_pre_state_snapshot_bytes: bytes

    def __post_init__(self) -> None:
        limits = (
            ("projection", self.exact_projection_bytes, MAX_REPLAY_PROJECTION_BYTES_V2),
            ("header", self.exact_header_bytes, MAX_HEADER_OR_CONFIG_BYTES_V1),
            ("body", self.exact_body_bytes, MAX_LEDGER_BODY_BYTES_V1),
            ("envelope", self.exact_envelope_bytes, MAX_ENVELOPE_BYTES_V1),
            ("receipt", self.exact_receipt_bytes, MAX_REPLAY_RECEIPT_BYTES_V2),
            ("evidence", self.exact_evidence_bytes, MAX_REPLAY_EVIDENCE_BYTES_V2),
            (
                "config document",
                self.exact_config_document_bytes,
                MAX_HEADER_OR_CONFIG_BYTES_V1,
            ),
            (
                "pre-state snapshot",
                self.exact_pre_state_snapshot_bytes,
                MAX_PRE_STATE_SNAPSHOT_BYTES_V1,
            ),
        )
        for name, value, maximum_bytes in limits:
            if type(value) is not bytes or not value or len(value) > maximum_bytes:
                raise TypeError(
                    f"persisted settlement replay {name} must be non-empty bounded bytes"
                )


class _DurableReplayPacketSealV2:
    __slots__ = ()


_DURABLE_REPLAY_PACKET_SEAL_V2 = _DurableReplayPacketSealV2()


class _NonTransferableDurableReplayPacketV2:
    __slots__ = ()

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("durable Spot V7 replay packet cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("durable Spot V7 replay packet cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("durable Spot V7 replay packet cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("durable Spot V7 replay packet cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("durable Spot V7 replay packet cannot be serialized")


@final
class _DurableSpotV7SettlementReplayPacketV2(_NonTransferableDurableReplayPacketV2):
    """Sealed packet retaining one exact current-record replay input graph."""

    __slots__ = ("_inputs", "_projection", "_seal")

    _inputs: _UntrustedPersistedSpotV7SettlementReplayInputsV2
    _projection: _SpotV7SettlementReplayProjectionV2
    _seal: _DurableReplayPacketSealV2

    def __init__(
        self,
        inputs: _UntrustedPersistedSpotV7SettlementReplayInputsV2,
        *,
        seal: _DurableReplayPacketSealV2,
    ) -> None:
        if type(inputs) is not _UntrustedPersistedSpotV7SettlementReplayInputsV2:
            raise TypeError("durable replay inputs have the wrong type")
        if seal is not _DURABLE_REPLAY_PACKET_SEAL_V2:
            raise TypeError("durable replay packet requires its module-private seal")
        projection = _decode_exact_projection_v2(inputs.exact_projection_bytes)
        _require_packet_bindings(projection, inputs)
        object.__setattr__(self, "_inputs", inputs)
        object.__setattr__(self, "_projection", projection)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("durable Spot V7 replay packet cannot be subclassed")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _DURABLE_REPLAY_PACKET_SEAL_V2

    def _persisted_inputs_for_storage(
        self,
    ) -> _UntrustedPersistedSpotV7SettlementReplayInputsV2:
        _require_durable_spot_v7_settlement_replay_packet_v2(self)
        return self._inputs

    def _projection_for_history_reverification(
        self,
    ) -> _SpotV7SettlementReplayProjectionV2:
        _require_durable_spot_v7_settlement_replay_packet_v2(self)
        return self._projection

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def release_authority(self) -> bool:
        return False

    @property
    def production_authority(self) -> bool:
        return False


def _new_durable_spot_v7_settlement_replay_packet_v2(
    inputs: _UntrustedPersistedSpotV7SettlementReplayInputsV2,
) -> _DurableSpotV7SettlementReplayPacketV2:
    return _DurableSpotV7SettlementReplayPacketV2(
        inputs,
        seal=_DURABLE_REPLAY_PACKET_SEAL_V2,
    )


def _load_untrusted_durable_spot_v7_settlement_replay_packet_v2(
    value: object,
) -> _DurableSpotV7SettlementReplayPacketV2:
    if type(value) is not _UntrustedPersistedSpotV7SettlementReplayInputsV2:
        raise TypeError("persisted replay inputs have the wrong type")
    try:
        return _new_durable_spot_v7_settlement_replay_packet_v2(value)
    except RecursionError as exc:
        raise ValueError("persisted replay input exceeds JSON nesting limits") from exc


def _require_durable_spot_v7_settlement_replay_packet_v2(
    value: object,
) -> _DurableSpotV7SettlementReplayPacketV2:
    if type(value) is not _DurableSpotV7SettlementReplayPacketV2:
        raise TypeError("durable replay packet must be the exact private V2 packet")
    if not value._has_private_seal():
        raise TypeError("durable replay packet lacks its module-private seal")
    return value


def _decode_exact_projection_v2(raw: bytes) -> _SpotV7SettlementReplayProjectionV2:
    if type(raw) is not bytes or not raw or len(raw) > MAX_REPLAY_PROJECTION_BYTES_V2:
        raise ValueError("persisted replay projection is not bounded bytes")
    try:
        document = _decode_exact_json_object(raw, name="persisted replay projection")
    except RecursionError as exc:
        raise ValueError("persisted replay projection exceeds JSON nesting limits") from exc
    expected_fields = {field.name for field in fields(_SpotV7SettlementReplayProjectionV2)}
    if set(document) != expected_fields:
        raise ValueError("persisted replay projection fields are not exact")
    try:
        return _SpotV7SettlementReplayProjectionV2(**document)
    except (TypeError, ValueError) as exc:
        raise ValueError("persisted replay projection is invalid") from exc


def _require_packet_bindings(
    projection: _SpotV7SettlementReplayProjectionV2,
    inputs: _UntrustedPersistedSpotV7SettlementReplayInputsV2,
) -> None:
    _require_exact_artifact_bindings(
        projection,
        header_bytes=inputs.exact_header_bytes,
        body_bytes=inputs.exact_body_bytes,
        envelope_bytes=inputs.exact_envelope_bytes,
        receipt_bytes=inputs.exact_receipt_bytes,
        evidence_bytes=inputs.exact_evidence_bytes,
    )
    _require_exact_replay_material_bindings_v2(
        projection,
        config_document_bytes=inputs.exact_config_document_bytes,
        pre_state_snapshot_bytes=inputs.exact_pre_state_snapshot_bytes,
    )
