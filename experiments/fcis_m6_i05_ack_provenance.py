"""Research-only acknowledgment provenance verification for FCIS M6 I05."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias, cast

from experiments.fcis_m6_i04_destination_dedup import (
    I04DedupRejectV1,
    I04DestinationReceiptV1,
    I04DestinationStateV1,
    I04VerifiedDedupContractV1,
    deliver_effect_v1,
)
from src.core import fcis_durable_retraction as dra


class I05Error(ValueError):
    """Typed validation failure in the isolated I05 model."""


def _digest(value: object, label: str) -> str:
    if (
        type(value) is not str
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise I05Error(f"{label} must be 64 lowercase hexadecimal characters")
    return value


def _bounded_text(value: object, label: str) -> str:
    if type(value) is not str:
        raise I05Error(f"{label} must be an exact string")
    if not value or len(value.encode("utf-8")) > dra.MAX_TEXT_BYTES:
        raise I05Error(f"{label} is empty or exceeds its byte bound")
    return value


I05_VERIFIER_PROFILE_ROOT: Final[str] = cast(
    str,
    dra.tagged_digest("i05/destination-ack-verifier/v1"),
)


class I05AckCodeV1(Enum):
    INVALID_CANDIDATE = "invalid_candidate"
    EFFECT_MISMATCH = "effect_mismatch"
    DESTINATION_MISMATCH = "destination_mismatch"
    ADAPTER_PROFILE_MISMATCH = "adapter_profile_mismatch"
    VERIFIER_PROFILE_MISMATCH = "verifier_profile_mismatch"
    DELIVERY_MISSING = "delivery_missing"
    RECEIPT_MISMATCH = "receipt_mismatch"
    SUBJECT_MISMATCH = "subject_mismatch"


@dataclass(frozen=True, slots=True)
class I05AckRejectV1:
    code: I05AckCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not I05AckCodeV1:
            raise I05Error("ack rejection code has the wrong exact type")
        if type(self.path) is not tuple or any(type(item) is not str for item in self.path):
            raise I05Error("ack rejection path has the wrong exact type")


@dataclass(frozen=True, slots=True)
class I05AckCandidateV1:
    """Untrusted acknowledgment data submitted to the local verifier."""

    effect: object
    contract: object
    delivery_state: object
    receipt: object
    adapter_profile_root: str
    verifier_profile_root: str
    subject_root: str

    def __post_init__(self) -> None:
        _digest(self.adapter_profile_root, "adapter_profile_root")
        _digest(self.verifier_profile_root, "verifier_profile_root")
        _digest(self.subject_root, "subject_root")


@dataclass(frozen=True, slots=True)
class I05VerifiedAckV1:
    """Verifier-produced acknowledgment bound to destination evidence."""

    effect_id: str
    destination: str
    payload_root: str
    destination_receipt_root: str
    adapter_profile_root: str
    verifier_profile_root: str
    subject_root: str

    def __post_init__(self) -> None:
        _digest(self.effect_id, "effect_id")
        _bounded_text(self.destination, "destination")
        _digest(self.payload_root, "payload_root")
        _digest(self.destination_receipt_root, "destination_receipt_root")
        _digest(self.adapter_profile_root, "adapter_profile_root")
        _digest(self.verifier_profile_root, "verifier_profile_root")
        _digest(self.subject_root, "subject_root")
        if self.subject_root != derive_ack_subject_root(
            effect_id=self.effect_id,
            destination=self.destination,
            payload_root=self.payload_root,
            destination_receipt_root=self.destination_receipt_root,
            adapter_profile_root=self.adapter_profile_root,
            verifier_profile_root=self.verifier_profile_root,
        ):
            raise I05Error("ack subject root is not canonical")


I05AckResultV1: TypeAlias = I05VerifiedAckV1 | I05AckRejectV1


def derive_ack_subject_root(
    *,
    effect_id: str,
    destination: str,
    payload_root: str,
    destination_receipt_root: str,
    adapter_profile_root: str,
    verifier_profile_root: str,
) -> str:
    """Derive the exact acknowledgment subject from all provenance fields."""

    _digest(effect_id, "effect_id")
    _bounded_text(destination, "destination")
    _digest(payload_root, "payload_root")
    _digest(destination_receipt_root, "destination_receipt_root")
    _digest(adapter_profile_root, "adapter_profile_root")
    _digest(verifier_profile_root, "verifier_profile_root")
    return cast(
        str,
        dra.tagged_digest(
            "i05/ack-subject/v1/"
            f"{effect_id}/{destination}/{payload_root}/"
            f"{destination_receipt_root}/{adapter_profile_root}/"
            f"{verifier_profile_root}"
        ),
    )


def _reject(code: I05AckCodeV1, *path: str) -> I05AckRejectV1:
    return I05AckRejectV1(code=code, path=tuple(path))


def verify_ack_provenance_v1(candidate: object) -> I05AckResultV1:
    """Verify destination delivery, receipt ancestry, and subject binding."""

    if type(candidate) is not I05AckCandidateV1:
        return _reject(I05AckCodeV1.INVALID_CANDIDATE, "candidate")
    try:
        candidate.__post_init__()
    except (I05Error, TypeError, ValueError, ArithmeticError, OverflowError):
        return _reject(I05AckCodeV1.INVALID_CANDIDATE, "candidate")
    if type(candidate.effect) is not dra.OutboxEffectV1:
        return _reject(I05AckCodeV1.INVALID_CANDIDATE, "effect")
    if type(candidate.contract) is not I04VerifiedDedupContractV1:
        return _reject(I05AckCodeV1.INVALID_CANDIDATE, "contract")
    if type(candidate.delivery_state) is not I04DestinationStateV1:
        return _reject(I05AckCodeV1.INVALID_CANDIDATE, "delivery_state")
    if type(candidate.receipt) is not I04DestinationReceiptV1:
        return _reject(I05AckCodeV1.INVALID_CANDIDATE, "receipt")
    effect = cast(dra.OutboxEffectV1, candidate.effect)
    contract = cast(I04VerifiedDedupContractV1, candidate.contract)
    delivery_state = cast(I04DestinationStateV1, candidate.delivery_state)
    receipt = cast(I04DestinationReceiptV1, candidate.receipt)
    try:
        effect.__post_init__()
        contract.__post_init__()
        delivery_state.__post_init__()
        receipt.__post_init__()
    except (dra.DurableRetractionError, I05Error, ValueError, TypeError):
        return _reject(I05AckCodeV1.INVALID_CANDIDATE, "typed_fields")
    if effect.destination != contract.destination or receipt.destination != effect.destination:
        return _reject(I05AckCodeV1.DESTINATION_MISMATCH, "destination")
    if effect.adapter_profile_root != contract.adapter_profile_root:
        return _reject(I05AckCodeV1.ADAPTER_PROFILE_MISMATCH, "effect")
    if candidate.adapter_profile_root != effect.adapter_profile_root:
        return _reject(I05AckCodeV1.ADAPTER_PROFILE_MISMATCH, "candidate")
    if candidate.verifier_profile_root != I05_VERIFIER_PROFILE_ROOT:
        return _reject(I05AckCodeV1.VERIFIER_PROFILE_MISMATCH, "verifier")
    if receipt.effect_id != effect.effect_id or receipt.payload_root != effect.payload_root:
        return _reject(I05AckCodeV1.EFFECT_MISMATCH, "receipt")

    expected_state, expected_result = deliver_effect_v1(
        contract,
        I04DestinationStateV1(),
        effect,
    )
    if isinstance(expected_result, I04DedupRejectV1):
        return _reject(I05AckCodeV1.RECEIPT_MISMATCH, "destination_contract")
    expected_record = next(
        (record for record in expected_state.records if record.effect_id == effect.effect_id),
        None,
    )
    actual_record = next(
        (record for record in delivery_state.records if record.effect_id == effect.effect_id),
        None,
    )
    if actual_record is None:
        return _reject(I05AckCodeV1.DELIVERY_MISSING, "effect_id")
    if expected_record is None or actual_record != expected_record:
        return _reject(I05AckCodeV1.RECEIPT_MISMATCH, "delivery_record")
    if receipt.destination_receipt_root != expected_result.destination_receipt_root:
        return _reject(I05AckCodeV1.RECEIPT_MISMATCH, "receipt_root")
    expected_subject = derive_ack_subject_root(
        effect_id=effect.effect_id,
        destination=effect.destination,
        payload_root=effect.payload_root,
        destination_receipt_root=receipt.destination_receipt_root,
        adapter_profile_root=candidate.adapter_profile_root,
        verifier_profile_root=candidate.verifier_profile_root,
    )
    if candidate.subject_root != expected_subject:
        return _reject(I05AckCodeV1.SUBJECT_MISMATCH, "subject_root")
    return I05VerifiedAckV1(
        effect_id=effect.effect_id,
        destination=effect.destination,
        payload_root=effect.payload_root,
        destination_receipt_root=receipt.destination_receipt_root,
        adapter_profile_root=candidate.adapter_profile_root,
        verifier_profile_root=candidate.verifier_profile_root,
        subject_root=expected_subject,
    )


__all__ = (
    "I05AckCandidateV1",
    "I05AckCodeV1",
    "I05AckRejectV1",
    "I05AckResultV1",
    "I05Error",
    "I05_VERIFIER_PROFILE_ROOT",
    "I05VerifiedAckV1",
    "derive_ack_subject_root",
    "verify_ack_provenance_v1",
)
