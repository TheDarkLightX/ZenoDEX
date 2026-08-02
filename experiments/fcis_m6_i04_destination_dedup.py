"""Research-only destination deduplication contract for FCIS M6 I04.

The module models the observable destination contract with an immutable
receipt table. It does not perform network IO, authorize production effects,
or prove that an external destination implements any of the modeled modes.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from src.core import fcis_durable_retraction as dra


class I04Error(ValueError):
    """Typed validation failure in the isolated I04 model."""


MAX_DESTINATION_RECEIPTS_V1: Final = 8_192


def _digest(value: object, label: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise I04Error(f"{label} must be 64 lowercase hexadecimal characters")
    return value


def _bounded_text(value: object, label: str) -> str:
    if type(value) is not str:
        raise I04Error(f"{label} must be an exact string")
    if not value or len(value.encode("utf-8")) > dra.MAX_TEXT_BYTES:
        raise I04Error(f"{label} is empty or exceeds its byte bound")
    return value


class I04DedupModeV1(Enum):
    """Accepted external deduplication mechanisms."""

    NATIVE_IDEMPOTENCY_KEY = "native_idempotency_key"
    QUERY_BY_EFFECT_ID = "query_by_effect_id"
    APPLICATION_RECEIPT_TABLE = "application_receipt_table"


class I04DedupCodeV1(Enum):
    INVALID_CONTRACT = "invalid_contract"
    UNMOUNTABLE = "unmountable"
    INVALID_EFFECT = "invalid_effect"
    DESTINATION_MISMATCH = "destination_mismatch"
    ADAPTER_PROFILE_MISMATCH = "adapter_profile_mismatch"
    PAYLOAD_CONFLICT = "payload_conflict"
    CAPACITY_EXCEEDED = "capacity_exceeded"
    STATE_INVALID = "state_invalid"


@dataclass(frozen=True, slots=True)
class I04DedupRejectV1:
    code: I04DedupCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not I04DedupCodeV1:
            raise I04Error("dedup rejection code has the wrong exact type")
        if type(self.path) is not tuple or any(type(item) is not str for item in self.path):
            raise I04Error("dedup rejection path has the wrong exact type")


@dataclass(frozen=True, slots=True)
class I04DedupContractCandidateV1:
    """Untrusted contract declaration submitted to the local verifier."""

    destination: str
    adapter_profile_root: str
    mode: object
    contract_root: str

    def __post_init__(self) -> None:
        _bounded_text(self.destination, "destination")
        _digest(self.adapter_profile_root, "adapter_profile_root")
        _digest(self.contract_root, "contract_root")


@dataclass(frozen=True, slots=True)
class I04VerifiedDedupContractV1:
    """Verifier-produced contract witness consumed by the model adapter."""

    destination: str
    adapter_profile_root: str
    mode: I04DedupModeV1
    contract_root: str

    def __post_init__(self) -> None:
        _bounded_text(self.destination, "destination")
        _digest(self.adapter_profile_root, "adapter_profile_root")
        if type(self.mode) is not I04DedupModeV1:
            raise I04Error("dedup mode has the wrong exact type")
        _digest(self.contract_root, "contract_root")
        if self.contract_root != derive_dedup_contract_root(
            self.destination,
            self.adapter_profile_root,
            self.mode,
        ):
            raise I04Error("dedup contract root is not canonical")


I04ContractResultV1: TypeAlias = I04VerifiedDedupContractV1 | I04DedupRejectV1


def derive_dedup_contract_root(
    destination: str,
    adapter_profile_root: str,
    mode: I04DedupModeV1,
) -> str:
    """Derive the canonical contract root from the declared mechanism."""

    _bounded_text(destination, "destination")
    _digest(adapter_profile_root, "adapter_profile_root")
    if type(mode) is not I04DedupModeV1:
        raise I04Error("dedup mode has the wrong exact type")
    return cast(
        str,
        dra.tagged_digest(
            f"i04/dedup-contract/v1/{destination}/{adapter_profile_root}/{mode.value}"
        ),
    )


def verify_dedup_contract_v1(candidate: object) -> I04ContractResultV1:
    """Verify a candidate and return a controlled contract witness or reject."""

    if type(candidate) is not I04DedupContractCandidateV1:
        return I04DedupRejectV1(I04DedupCodeV1.INVALID_CONTRACT, ("candidate",))
    try:
        candidate.__post_init__()
    except (I04Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return I04DedupRejectV1(I04DedupCodeV1.INVALID_CONTRACT, ("candidate",))
    if type(candidate.mode) is not I04DedupModeV1:
        return I04DedupRejectV1(I04DedupCodeV1.UNMOUNTABLE, ("mode",))
    expected_root = derive_dedup_contract_root(
        candidate.destination,
        candidate.adapter_profile_root,
        candidate.mode,
    )
    if candidate.contract_root != expected_root:
        return I04DedupRejectV1(I04DedupCodeV1.UNMOUNTABLE, ("contract_root",))
    return I04VerifiedDedupContractV1(
        destination=candidate.destination,
        adapter_profile_root=candidate.adapter_profile_root,
        mode=candidate.mode,
        contract_root=expected_root,
    )


class I04DeliveryOutcomeV1(Enum):
    ACCEPTED = "accepted"
    ALREADY_ACCEPTED = "already_accepted"


@dataclass(frozen=True, slots=True)
class I04DestinationReceiptV1:
    """Destination-generated result for one effect identity."""

    effect_id: str
    destination: str
    payload_root: str
    destination_receipt_root: str
    outcome: I04DeliveryOutcomeV1

    def __post_init__(self) -> None:
        _digest(self.effect_id, "effect_id")
        _bounded_text(self.destination, "destination")
        _digest(self.payload_root, "payload_root")
        _digest(self.destination_receipt_root, "destination_receipt_root")
        if type(self.outcome) is not I04DeliveryOutcomeV1:
            raise I04Error("delivery outcome has the wrong exact type")


@dataclass(frozen=True, slots=True)
class I04DestinationRecordV1:
    """Immutable application-owned record of one accepted effect."""

    effect_id: str
    destination: str
    payload_root: str
    destination_receipt_root: str

    def __post_init__(self) -> None:
        _digest(self.effect_id, "effect_id")
        _bounded_text(self.destination, "destination")
        _digest(self.payload_root, "payload_root")
        _digest(self.destination_receipt_root, "destination_receipt_root")


@dataclass(frozen=True, slots=True)
class I04DestinationStateV1:
    records: tuple[I04DestinationRecordV1, ...] = ()

    def __post_init__(self) -> None:
        if type(self.records) is not tuple:
            raise I04Error("destination records must be an exact tuple")
        if len(self.records) > MAX_DESTINATION_RECEIPTS_V1:
            raise I04Error(
                "destination records exceed the closed capacity bound "
                f"{MAX_DESTINATION_RECEIPTS_V1}"
            )
        if any(type(record) is not I04DestinationRecordV1 for record in self.records):
            raise I04Error("destination record has the wrong exact type")
        if tuple(sorted(self.records, key=lambda record: record.effect_id)) != self.records:
            raise I04Error("destination records must be canonically ordered")
        effect_ids = tuple(record.effect_id for record in self.records)
        if len(set(effect_ids)) != len(effect_ids):
            raise I04Error("destination effect identities must be unique")


I04DeliveryResultV1: TypeAlias = I04DestinationReceiptV1 | I04DedupRejectV1


def _reject(code: I04DedupCodeV1, *path: str) -> I04DedupRejectV1:
    return I04DedupRejectV1(code=code, path=tuple(path))


def _destination_receipt_root(
    contract: I04VerifiedDedupContractV1,
    effect: dra.OutboxEffectV1,
) -> str:
    return cast(
        str,
        dra.tagged_digest(
            "i04/destination-receipt/v1/"
            f"{contract.contract_root}/{effect.effect_id}/"
            f"{effect.destination}/{effect.payload_root}"
        ),
    )


def _deliver_against_record_table(
    contract: I04VerifiedDedupContractV1,
    state: I04DestinationStateV1,
    effect: dra.OutboxEffectV1,
) -> tuple[I04DestinationStateV1, I04DeliveryResultV1]:
    records = {record.effect_id: record for record in state.records}
    existing = records.get(effect.effect_id)
    if existing is not None:
        if existing.destination != effect.destination:
            return state, _reject(I04DedupCodeV1.DESTINATION_MISMATCH, "effect_id")
        if existing.payload_root != effect.payload_root:
            return state, _reject(I04DedupCodeV1.PAYLOAD_CONFLICT, "effect_id")
        return state, I04DestinationReceiptV1(
            effect_id=existing.effect_id,
            destination=existing.destination,
            payload_root=existing.payload_root,
            destination_receipt_root=existing.destination_receipt_root,
            outcome=I04DeliveryOutcomeV1.ALREADY_ACCEPTED,
        )
    if len(state.records) >= MAX_DESTINATION_RECEIPTS_V1:
        return state, _reject(I04DedupCodeV1.CAPACITY_EXCEEDED, "records")
    record = I04DestinationRecordV1(
        effect_id=effect.effect_id,
        destination=effect.destination,
        payload_root=effect.payload_root,
        destination_receipt_root=_destination_receipt_root(contract, effect),
    )
    next_state = I04DestinationStateV1(
        records=tuple(sorted((*state.records, record), key=lambda item: item.effect_id))
    )
    return next_state, I04DestinationReceiptV1(
        effect_id=record.effect_id,
        destination=record.destination,
        payload_root=record.payload_root,
        destination_receipt_root=record.destination_receipt_root,
        outcome=I04DeliveryOutcomeV1.ACCEPTED,
    )


def deliver_effect_v1(
    contract: object,
    state: object,
    effect: object,
) -> tuple[I04DestinationStateV1, I04DeliveryResultV1]:
    """Apply one effect to the deterministic destination model."""

    if type(contract) is not I04VerifiedDedupContractV1:
        return I04DestinationStateV1(), _reject(I04DedupCodeV1.UNMOUNTABLE, "contract")
    if type(state) is not I04DestinationStateV1:
        return I04DestinationStateV1(), _reject(I04DedupCodeV1.STATE_INVALID, "state")
    if type(effect) is not dra.OutboxEffectV1:
        return state, _reject(I04DedupCodeV1.INVALID_EFFECT, "effect")
    exact_contract = contract
    exact_state = state
    exact_effect = cast(dra.OutboxEffectV1, effect)
    try:
        exact_effect.__post_init__()
        exact_state.__post_init__()
    except (dra.DurableRetractionError, I04Error, TypeError, ValueError):
        return exact_state, _reject(I04DedupCodeV1.INVALID_EFFECT, "effect_or_state")
    if exact_effect.destination != exact_contract.destination:
        return exact_state, _reject(I04DedupCodeV1.DESTINATION_MISMATCH, "destination")
    if exact_effect.adapter_profile_root != exact_contract.adapter_profile_root:
        return exact_state, _reject(
            I04DedupCodeV1.ADAPTER_PROFILE_MISMATCH,
            "adapter_profile_root",
        )
    mode: object = exact_contract.mode
    if mode is I04DedupModeV1.NATIVE_IDEMPOTENCY_KEY:
        return _deliver_against_record_table(exact_contract, exact_state, exact_effect)
    if mode is I04DedupModeV1.QUERY_BY_EFFECT_ID:
        return _deliver_against_record_table(exact_contract, exact_state, exact_effect)
    if mode is I04DedupModeV1.APPLICATION_RECEIPT_TABLE:
        return _deliver_against_record_table(exact_contract, exact_state, exact_effect)
    return exact_state, _reject(I04DedupCodeV1.UNMOUNTABLE, "mode")


__all__ = (
    "I04ContractResultV1",
    "I04DedupCodeV1",
    "I04DedupContractCandidateV1",
    "I04DedupModeV1",
    "I04DedupRejectV1",
    "I04DeliveryOutcomeV1",
    "I04DeliveryResultV1",
    "I04DestinationReceiptV1",
    "I04DestinationRecordV1",
    "I04DestinationStateV1",
    "I04Error",
    "I04VerifiedDedupContractV1",
    "MAX_DESTINATION_RECEIPTS_V1",
    "deliver_effect_v1",
    "derive_dedup_contract_root",
    "verify_dedup_contract_v1",
)
