"""Fail-closed re-verification of persisted Spot V7 settlement replay bytes."""

from __future__ import annotations

from typing import Any, NoReturn, SupportsIndex, final

from src.integration._zrpf_spot_v7_settlement_envelope_codec import (
    MAX_HEADER_OR_CONFIG_BYTES_V1,
)
from src.integration._zrpf_spot_v7_settlement_envelope_contract import (
    SpotV7SettlementEnvelopeReplayErrorV1,
    _decode_exact_json_object,
)
from src.integration._zrpf_spot_v7_settlement_envelope_replay import (
    SpotV7SettlementEnvelopeReplayAdapterV2,
)
from src.integration._zrpf_spot_v7_settlement_replay_packet import (
    _DurableSpotV7SettlementReplayPacketV2,
    _load_untrusted_durable_spot_v7_settlement_replay_packet_v2,
    _require_durable_spot_v7_settlement_replay_packet_v2,
    _UntrustedPersistedSpotV7SettlementReplayInputsV2,
)


class SpotV7SettlementDurableReplayErrorV2(ValueError):
    """Stable rejection from persisted exact-byte replay verification."""

    def __init__(self, code: str) -> None:
        self.code = code
        super().__init__(f"SPOT_V7_SETTLEMENT_DURABLE_REPLAY_REJECTED: {code}")


class _DurableReplayResultSealV2:
    __slots__ = ()


_DURABLE_REPLAY_RESULT_SEAL_V2 = _DurableReplayResultSealV2()


class _NonTransferableDurableReplayResultV2:
    __slots__ = ()

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise TypeError("durably reverified Spot V7 replay result cannot be mutated")

    def __copy__(self) -> NoReturn:
        raise TypeError("durably reverified Spot V7 replay result cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("durably reverified Spot V7 replay result cannot be deep-copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("durably reverified Spot V7 replay result cannot be serialized")

    def __reduce_ex__(self, _protocol: SupportsIndex) -> NoReturn:
        raise TypeError("durably reverified Spot V7 replay result cannot be serialized")


@final
class _DurablyReverifiedSpotV7SettlementReplayV2(_NonTransferableDurableReplayResultV2):
    """Authority-neutral fact that the retained current record re-executed.

    A non-genesis parent header is an external hash-bound history prerequisite;
    it is checked during replay and is not retained in the current-record packet.
    """

    __slots__ = ("_packet", "_seal")

    _packet: _DurableSpotV7SettlementReplayPacketV2
    _seal: _DurableReplayResultSealV2

    def __init__(
        self,
        packet: _DurableSpotV7SettlementReplayPacketV2,
        *,
        seal: _DurableReplayResultSealV2,
    ) -> None:
        packet_value = _require_durable_spot_v7_settlement_replay_packet_v2(packet)
        if seal is not _DURABLE_REPLAY_RESULT_SEAL_V2:
            raise TypeError("durable replay result requires its module-private seal")
        object.__setattr__(self, "_packet", packet_value)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("durably reverified Spot V7 replay result cannot be subclassed")

    def _has_private_seal(self) -> bool:
        return getattr(self, "_seal", None) is _DURABLE_REPLAY_RESULT_SEAL_V2

    def _durable_replay_packet_for_history_commit(
        self,
    ) -> _DurableSpotV7SettlementReplayPacketV2:
        _require_durably_reverified_spot_v7_settlement_replay_v2(self)
        return self._packet

    @property
    def exact_replay_material_authenticated(self) -> bool:
        _require_durably_reverified_spot_v7_settlement_replay_v2(self)
        return True

    @property
    def durable_settlement_replay_reverification_material_retained(self) -> bool:
        _require_durably_reverified_spot_v7_settlement_replay_v2(self)
        return True

    @property
    def durable_settlement_replay_reverified(self) -> bool:
        _require_durably_reverified_spot_v7_settlement_replay_v2(self)
        return True

    @property
    def proof_receipt_authentication_established(self) -> bool:
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


def _reverify_persisted_spot_v7_settlement_replay_v2(
    *,
    settlement: object,
    persisted: object,
    exact_parent_header_bytes: bytes | None = None,
) -> _DurablyReverifiedSpotV7SettlementReplayV2:
    """Re-execute one retained current-record graph under a governed candidate.

    The returned result proves only that these retained bytes re-executed under
    the supplied governed candidate and, for non-genesis records, the separately
    supplied exact parent header. Parent-history retention, proof-receipt,
    finality, release, settlement, and production authority remain external.
    """

    if type(persisted) is not _UntrustedPersistedSpotV7SettlementReplayInputsV2:
        raise TypeError("persisted replay inputs have the wrong type")
    try:
        retained_packet = _load_untrusted_durable_spot_v7_settlement_replay_packet_v2(persisted)
    except (TypeError, ValueError) as exc:
        raise SpotV7SettlementDurableReplayErrorV2("persisted_packet_binding") from exc

    config_document = _decode_persisted_object(
        persisted.exact_config_document_bytes,
        name="persisted replay config document",
    )
    header = _decode_persisted_object(
        persisted.exact_header_bytes,
        name="persisted replay header",
    )
    body = _decode_persisted_object(
        persisted.exact_body_bytes,
        name="persisted replay body",
    )
    pre_state_snapshot = _decode_persisted_object(
        persisted.exact_pre_state_snapshot_bytes,
        name="persisted replay pre-state snapshot",
    )
    parent_header = _decode_optional_parent_header(exact_parent_header_bytes)

    try:
        observation = SpotV7SettlementEnvelopeReplayAdapterV2(config_document).authenticate(
            settlement=settlement,
            header=header,
            body=body,
            pre_snapshot=pre_state_snapshot,
            parent_header=parent_header,
        )
    except SpotV7SettlementEnvelopeReplayErrorV1 as exc:
        raise SpotV7SettlementDurableReplayErrorV2("exact_replay_rejected") from exc
    replayed_packet = observation._durable_replay_packet_for_history_reverification()
    if (
        replayed_packet._persisted_inputs_for_storage()
        != retained_packet._persisted_inputs_for_storage()
    ):
        raise SpotV7SettlementDurableReplayErrorV2("replayed_packet_mismatch")
    return _DurablyReverifiedSpotV7SettlementReplayV2(
        replayed_packet,
        seal=_DURABLE_REPLAY_RESULT_SEAL_V2,
    )


def _require_durably_reverified_spot_v7_settlement_replay_v2(
    value: object,
) -> _DurablyReverifiedSpotV7SettlementReplayV2:
    if type(value) is not _DurablyReverifiedSpotV7SettlementReplayV2:
        raise TypeError("durable replay result must be the exact private V2 result")
    if not value._has_private_seal():
        raise TypeError("durable replay result lacks its module-private seal")
    return value


def _decode_persisted_object(raw: bytes, *, name: str) -> dict[str, Any]:
    try:
        return _decode_exact_json_object(raw, name=name)
    except (TypeError, ValueError, RecursionError) as exc:
        raise SpotV7SettlementDurableReplayErrorV2("persisted_packet_binding") from exc


def _decode_optional_parent_header(raw: bytes | None) -> dict[str, Any] | None:
    if raw is None:
        return None
    if type(raw) is not bytes or not raw or len(raw) > MAX_HEADER_OR_CONFIG_BYTES_V1:
        raise SpotV7SettlementDurableReplayErrorV2("parent_header")
    try:
        return _decode_exact_json_object(raw, name="persisted replay parent header")
    except (TypeError, ValueError, RecursionError) as exc:
        raise SpotV7SettlementDurableReplayErrorV2("parent_header") from exc
