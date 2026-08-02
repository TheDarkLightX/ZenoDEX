"""Research-only destination deduplication contract for FCIS M6 I04.

The module models the observable destination contract with an immutable
receipt table. It does not perform network IO, authorize production effects,
or prove that an external destination implements any of the modeled modes.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from enum import Enum
from typing import Final, TypeAlias, cast
from weakref import WeakValueDictionary

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
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise I04Error(f"{label} must be valid UTF-8") from exc
    if not encoded or len(encoded) > dra.MAX_TEXT_BYTES:
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


@dataclass(frozen=True, slots=True, weakref_slot=True)
class I04VerifiedDedupContractV1:
    """Verifier-produced contract witness consumed by the model adapter."""

    destination: str
    adapter_profile_root: str
    mode: I04DedupModeV1
    contract_root: str
    _construction_token: InitVar[object | None] = None

    def __post_init__(self, _construction_token: object | None) -> None:
        if _construction_token is not _I04_CONTRACT_CONSTRUCTION_TOKEN_V1:
            raise I04Error("verified dedup contract construction is verifier-owned")
        self._validate_fields()

    def _validate_fields(self) -> None:
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


_I04_CONTRACT_CONSTRUCTION_TOKEN_V1 = object()
_I04_VERIFIED_CONTRACTS_V1: WeakValueDictionary[int, I04VerifiedDedupContractV1] = (
    WeakValueDictionary()
)
_I04_VERIFIED_CONTRACT_SNAPSHOTS_V1: dict[int, tuple[object, ...]] = {}


def _verified_contract_snapshot_v1(
    contract: I04VerifiedDedupContractV1,
) -> tuple[object, ...]:
    return (
        contract.destination,
        contract.adapter_profile_root,
        contract.mode,
        contract.contract_root,
    )


def _mint_verified_contract_v1(
    *,
    destination: str,
    adapter_profile_root: str,
    mode: I04DedupModeV1,
    contract_root: str,
) -> I04VerifiedDedupContractV1:
    contract = I04VerifiedDedupContractV1(
        destination=destination,
        adapter_profile_root=adapter_profile_root,
        mode=mode,
        contract_root=contract_root,
        _construction_token=_I04_CONTRACT_CONSTRUCTION_TOKEN_V1,
    )
    identity = id(contract)
    _I04_VERIFIED_CONTRACTS_V1[identity] = contract
    _I04_VERIFIED_CONTRACT_SNAPSHOTS_V1[identity] = _verified_contract_snapshot_v1(contract)
    return contract


def _is_registered_verified_contract_v1(value: object) -> bool:
    if type(value) is not I04VerifiedDedupContractV1:
        return False
    contract = value
    registered = _I04_VERIFIED_CONTRACTS_V1.get(id(contract))
    if registered is not contract:
        return False
    try:
        contract._validate_fields()
        return _I04_VERIFIED_CONTRACT_SNAPSHOTS_V1.get(id(contract)) == (
            _verified_contract_snapshot_v1(contract)
        )
    except (AttributeError, I04Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return False


def is_verified_dedup_contract_v1(value: object) -> bool:
    """Return whether ``value`` is a live, verifier-minted contract witness.

    Consumers use this predicate at their own point of use.  Calling the
    witness dataclass initializer again would require the private mint token
    and would therefore reject an otherwise valid verifier-produced value.
    """

    return _is_registered_verified_contract_v1(value)


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
    return _mint_verified_contract_v1(
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
        for record in self.records:
            if type(record) is not I04DestinationRecordV1:
                raise I04Error("destination record has the wrong exact type")
            record.__post_init__()
        if tuple(sorted(self.records, key=lambda record: record.effect_id)) != self.records:
            raise I04Error("destination records must be canonically ordered")
        effect_ids = tuple(record.effect_id for record in self.records)
        if len(set(effect_ids)) != len(effect_ids):
            raise I04Error("destination effect identities must be unique")


@dataclass(frozen=True, slots=True)
class I04DeliveryAcceptV1:
    """One accepted destination transition with its exact successor and receipt."""

    next_state: I04DestinationStateV1
    receipt: I04DestinationReceiptV1

    def __post_init__(self) -> None:
        if type(self.next_state) is not I04DestinationStateV1:
            raise I04Error("delivery successor has the wrong exact type")
        if type(self.receipt) is not I04DestinationReceiptV1:
            raise I04Error("delivery receipt has the wrong exact type")
        self.next_state.__post_init__()
        self.receipt.__post_init__()
        record = next(
            (item for item in self.next_state.records if item.effect_id == self.receipt.effect_id),
            None,
        )
        if record is None:
            raise I04Error("delivery successor does not contain the receipt effect")
        if (
            record.destination != self.receipt.destination
            or record.payload_root != self.receipt.payload_root
            or record.destination_receipt_root != self.receipt.destination_receipt_root
        ):
            raise I04Error("delivery successor and receipt do not agree")


I04DeliveryResultV1: TypeAlias = I04DeliveryAcceptV1 | I04DedupRejectV1


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
) -> I04DeliveryResultV1:
    records = {record.effect_id: record for record in state.records}
    existing = records.get(effect.effect_id)
    if existing is not None:
        if existing.destination != effect.destination:
            return _reject(I04DedupCodeV1.DESTINATION_MISMATCH, "effect_id")
        if existing.payload_root != effect.payload_root:
            return _reject(I04DedupCodeV1.PAYLOAD_CONFLICT, "effect_id")
        return I04DeliveryAcceptV1(
            next_state=state,
            receipt=I04DestinationReceiptV1(
                effect_id=existing.effect_id,
                destination=existing.destination,
                payload_root=existing.payload_root,
                destination_receipt_root=existing.destination_receipt_root,
                outcome=I04DeliveryOutcomeV1.ALREADY_ACCEPTED,
            ),
        )
    if len(state.records) >= MAX_DESTINATION_RECEIPTS_V1:
        return _reject(I04DedupCodeV1.CAPACITY_EXCEEDED, "records")
    record = I04DestinationRecordV1(
        effect_id=effect.effect_id,
        destination=effect.destination,
        payload_root=effect.payload_root,
        destination_receipt_root=_destination_receipt_root(contract, effect),
    )
    next_state = I04DestinationStateV1(
        records=tuple(sorted((*state.records, record), key=lambda item: item.effect_id))
    )
    return I04DeliveryAcceptV1(
        next_state=next_state,
        receipt=I04DestinationReceiptV1(
            effect_id=record.effect_id,
            destination=record.destination,
            payload_root=record.payload_root,
            destination_receipt_root=record.destination_receipt_root,
            outcome=I04DeliveryOutcomeV1.ACCEPTED,
        ),
    )


def deliver_effect_v1(
    contract: object,
    state: object,
    effect: object,
) -> I04DeliveryResultV1:
    """Apply one effect to the deterministic destination model."""

    if type(state) is not I04DestinationStateV1:
        return _reject(I04DedupCodeV1.STATE_INVALID, "state")
    exact_contract = cast(I04VerifiedDedupContractV1, contract)
    exact_state = state
    try:
        exact_state.__post_init__()
    except (I04Error, TypeError, ValueError):
        return _reject(I04DedupCodeV1.STATE_INVALID, "state")
    if not _is_registered_verified_contract_v1(contract):
        return _reject(I04DedupCodeV1.UNMOUNTABLE, "contract")
    if type(effect) is not dra.OutboxEffectV1:
        return _reject(I04DedupCodeV1.INVALID_EFFECT, "effect")
    exact_effect = cast(dra.OutboxEffectV1, effect)
    try:
        exact_effect.__post_init__()
    except (dra.DurableRetractionError, I04Error, TypeError, ValueError):
        return _reject(I04DedupCodeV1.INVALID_EFFECT, "effect")
    if exact_effect.destination != exact_contract.destination:
        return _reject(I04DedupCodeV1.DESTINATION_MISMATCH, "destination")
    if exact_effect.adapter_profile_root != exact_contract.adapter_profile_root:
        return _reject(
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
    return _reject(I04DedupCodeV1.UNMOUNTABLE, "mode")


__all__ = (
    "I04ContractResultV1",
    "I04DedupCodeV1",
    "I04DedupContractCandidateV1",
    "I04DedupModeV1",
    "I04DedupRejectV1",
    "I04DeliveryAcceptV1",
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
    "is_verified_dedup_contract_v1",
    "verify_dedup_contract_v1",
)
