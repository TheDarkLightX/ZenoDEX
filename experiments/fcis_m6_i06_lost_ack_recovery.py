"""Research-only lost-ack recovery model for FCIS M6 I06.

The model separates destination acceptance from local acknowledgment. A
simulated crash may lose the local response/ack while retaining the
destination's immutable receipt record. Recovery redelivers the same
``OutboxEffectV1`` and accepts only an ``ALREADY_ACCEPTED`` response whose
receipt passes the I05 provenance verifier. The local journal can therefore
contain one semantic acknowledgment even when delivery is attempted again.

No network, worker, filesystem, production datastore, or value-moving path is
implemented here.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, cast

from experiments.fcis_m6_i04_destination_dedup import (
    I04DedupRejectV1,
    I04DeliveryOutcomeV1,
    I04DestinationReceiptV1,
    I04DestinationStateV1,
    I04VerifiedDedupContractV1,
    deliver_effect_v1,
    is_verified_dedup_contract_v1,
)
from experiments.fcis_m6_i05_ack_provenance import (
    I05_VERIFIER_PROFILE_ROOT,
    I05AckCandidateV1,
    I05AckRejectV1,
    I05VerifiedAckV1,
    derive_ack_subject_root,
    verify_ack_provenance_v1,
)
from src.core import fcis_durable_retraction as dra


class I06Error(ValueError):
    """Typed validation failure in the isolated I06 model."""


def _u32(value: object, label: str) -> int:
    if type(value) is not int or value < 0 or value > dra.U32_MAX:
        raise I06Error(f"{label} must be an exact u32")
    return value


class I06PhaseV1(Enum):
    """The only phases in the one-effect lost-ack reference state."""

    READY = "ready"
    RESPONSE_LOST_AFTER_DESTINATION_ACCEPTANCE = "response_lost_after_destination_acceptance"
    ACK_DURABLE = "ack_durable"


class I06RecoveryOutcomeV1(Enum):
    """Observable recovery outcomes for a redelivery attempt."""

    REDELIVERED_ALREADY_ACCEPTED = "redelivered_already_accepted"
    ALREADY_DURABLE_NOOP = "already_durable_noop"


class I06RecoveryCodeV1(Enum):
    INVALID_STATE = "invalid_state"
    INVALID_PHASE = "invalid_phase"
    DESTINATION_REJECTED = "destination_rejected"
    EXPECTED_ALREADY_ACCEPTED = "expected_already_accepted"
    PROVENANCE_REJECTED = "provenance_rejected"
    ATTEMPT_OVERFLOW = "attempt_overflow"
    ACK_COLLISION = "ack_collision"


@dataclass(frozen=True, slots=True)
class I06RecoveryRejectV1:
    code: I06RecoveryCodeV1
    path: tuple[str, ...]

    def __post_init__(self) -> None:
        if type(self.code) is not I06RecoveryCodeV1:
            raise I06Error("recovery rejection code has the wrong exact type")
        if type(self.path) is not tuple or any(type(item) is not str for item in self.path):
            raise I06Error("recovery rejection path has the wrong exact type")


@dataclass(frozen=True, slots=True)
class I06AckJournalV1:
    """One immutable local acknowledgment write."""

    ack: I05VerifiedAckV1
    write_count: int = 1

    def __post_init__(self) -> None:
        if type(self.ack) is not I05VerifiedAckV1:
            raise I06Error("ack journal must contain a verified acknowledgment")
        self.ack.__post_init__()
        if _u32(self.write_count, "write_count") != 1:
            raise I06Error("the one-effect journal must contain exactly one write")


@dataclass(frozen=True, slots=True)
class I06DeliveryStateV1:
    """Immutable state for one committed effect and one destination."""

    effect: dra.OutboxEffectV1
    contract: I04VerifiedDedupContractV1
    destination_state: I04DestinationStateV1
    phase: I06PhaseV1
    delivery_attempts: int = 0
    ack_journal: I06AckJournalV1 | None = None

    def __post_init__(self) -> None:
        if type(self.effect) is not dra.OutboxEffectV1:
            raise I06Error("effect has the wrong exact type")
        if not is_verified_dedup_contract_v1(self.contract):
            raise I06Error("contract has the wrong exact type")
        if type(self.destination_state) is not I04DestinationStateV1:
            raise I06Error("destination_state has the wrong exact type")
        if type(self.phase) is not I06PhaseV1:
            raise I06Error("phase has the wrong exact type")
        self.effect.__post_init__()
        self.destination_state.__post_init__()
        if self.effect.destination != self.contract.destination:
            raise I06Error("effect and contract destinations differ")
        if self.effect.adapter_profile_root != self.contract.adapter_profile_root:
            raise I06Error("effect and contract adapter profiles differ")
        attempts = _u32(self.delivery_attempts, "delivery_attempts")
        if self.ack_journal is not None:
            if type(self.ack_journal) is not I06AckJournalV1:
                raise I06Error("ack_journal has the wrong exact type")
            self.ack_journal.__post_init__()

        effect_records = tuple(
            record
            for record in self.destination_state.records
            if record.effect_id == self.effect.effect_id
        )
        if self.phase is I06PhaseV1.READY:
            if attempts != 0 or self.ack_journal is not None:
                raise I06Error("ready state has delivery history")
            if self.destination_state.records:
                raise I06Error("ready state has destination records")
            return

        if len(effect_records) != 1 or len(self.destination_state.records) != 1:
            raise I06Error("active state must contain exactly one effect record")
        record = effect_records[0]
        if (
            record.destination != self.effect.destination
            or record.payload_root != self.effect.payload_root
        ):
            raise I06Error("destination record is crossed with the effect")

        if self.phase is I06PhaseV1.RESPONSE_LOST_AFTER_DESTINATION_ACCEPTANCE:
            if attempts != 1 or self.ack_journal is not None:
                raise I06Error("response-lost state must have one attempt and no ack")
            return

        if self.phase is I06PhaseV1.ACK_DURABLE:
            if attempts < 2 or self.ack_journal is None:
                raise I06Error("durable-ack state lacks a recovery attempt or journal")
            ack = self.ack_journal.ack
            if (
                ack.effect_id != self.effect.effect_id
                or ack.destination != self.effect.destination
                or ack.payload_root != self.effect.payload_root
                or ack.destination_receipt_root != record.destination_receipt_root
                or ack.adapter_profile_root != self.effect.adapter_profile_root
                or ack.verifier_profile_root != I05_VERIFIER_PROFILE_ROOT
            ):
                raise I06Error("ack journal is not bound to the destination record")
            return

        raise I06Error("unsupported I06 phase")


@dataclass(frozen=True, slots=True)
class I06RecoveryResultV1:
    outcome: I06RecoveryOutcomeV1
    state: I06DeliveryStateV1

    def __post_init__(self) -> None:
        if type(self.outcome) is not I06RecoveryOutcomeV1:
            raise I06Error("recovery outcome has the wrong exact type")
        self.state.__post_init__()


I06StateResultV1: TypeAlias = I06DeliveryStateV1 | I06RecoveryRejectV1
I06TransitionResultV1: TypeAlias = I06RecoveryResultV1 | I06RecoveryRejectV1


def _reject(code: I06RecoveryCodeV1, *path: str) -> I06RecoveryRejectV1:
    return I06RecoveryRejectV1(code=code, path=tuple(path))


def _validate_state(value: object) -> I06DeliveryStateV1 | I06RecoveryRejectV1:
    if type(value) is not I06DeliveryStateV1:
        return _reject(I06RecoveryCodeV1.INVALID_STATE, "state")
    state = value
    try:
        state.__post_init__()
    except (I06Error, dra.DurableRetractionError, TypeError, ValueError):
        return _reject(I06RecoveryCodeV1.INVALID_STATE, "state")
    return state


def new_delivery_state_v1(contract: object, effect: object) -> I06StateResultV1:
    """Create a ready state without accepting or synthesizing an effect."""

    if not is_verified_dedup_contract_v1(contract):
        return _reject(I06RecoveryCodeV1.INVALID_STATE, "contract")
    if type(effect) is not dra.OutboxEffectV1:
        return _reject(I06RecoveryCodeV1.INVALID_STATE, "effect")
    exact_contract = cast(I04VerifiedDedupContractV1, contract)
    exact_effect = cast(dra.OutboxEffectV1, effect)
    try:
        exact_effect.__post_init__()
        state = I06DeliveryStateV1(
            effect=exact_effect,
            contract=exact_contract,
            destination_state=I04DestinationStateV1(),
            phase=I06PhaseV1.READY,
        )
    except (I06Error, dra.DurableRetractionError, TypeError, ValueError):
        return _reject(I06RecoveryCodeV1.INVALID_STATE, "contract_or_effect")
    return state


def lose_response_after_destination_acceptance_v1(value: object) -> I06StateResultV1:
    """Commit destination acceptance, then lose the response before local ack."""

    validated = _validate_state(value)
    if isinstance(validated, I06RecoveryRejectV1):
        return validated
    state = validated
    if state.phase is not I06PhaseV1.READY:
        return _reject(I06RecoveryCodeV1.INVALID_PHASE, "crash_point")
    next_destination_state, result = deliver_effect_v1(
        state.contract,
        state.destination_state,
        state.effect,
    )
    if isinstance(result, I04DedupRejectV1):
        return _reject(I06RecoveryCodeV1.DESTINATION_REJECTED, result.code.value)
    if result.outcome is not I04DeliveryOutcomeV1.ACCEPTED:
        return _reject(I06RecoveryCodeV1.EXPECTED_ALREADY_ACCEPTED, "initial_delivery")
    try:
        return I06DeliveryStateV1(
            effect=state.effect,
            contract=state.contract,
            destination_state=next_destination_state,
            phase=I06PhaseV1.RESPONSE_LOST_AFTER_DESTINATION_ACCEPTANCE,
            delivery_attempts=1,
        )
    except (I06Error, dra.DurableRetractionError, TypeError, ValueError):
        return _reject(I06RecoveryCodeV1.INVALID_STATE, "destination_commit")


def _ack_candidate(
    state: I06DeliveryStateV1,
    receipt: I04DestinationReceiptV1,
    destination_state: I04DestinationStateV1,
) -> I05AckCandidateV1:
    subject_root = derive_ack_subject_root(
        effect_id=state.effect.effect_id,
        destination=state.effect.destination,
        payload_root=state.effect.payload_root,
        destination_receipt_root=receipt.destination_receipt_root,
        adapter_profile_root=state.effect.adapter_profile_root,
        verifier_profile_root=I05_VERIFIER_PROFILE_ROOT,
    )
    return I05AckCandidateV1(
        effect=state.effect,
        contract=state.contract,
        delivery_state=destination_state,
        receipt=receipt,
        adapter_profile_root=state.effect.adapter_profile_root,
        verifier_profile_root=I05_VERIFIER_PROFILE_ROOT,
        subject_root=subject_root,
    )


def _verified_redelivery_ack(
    state: I06DeliveryStateV1,
) -> I05VerifiedAckV1 | I06RecoveryRejectV1:
    next_destination_state, result = deliver_effect_v1(
        state.contract,
        state.destination_state,
        state.effect,
    )
    if isinstance(result, I04DedupRejectV1):
        return _reject(I06RecoveryCodeV1.DESTINATION_REJECTED, result.code.value)
    if result.outcome is not I04DeliveryOutcomeV1.ALREADY_ACCEPTED:
        return _reject(I06RecoveryCodeV1.EXPECTED_ALREADY_ACCEPTED, "redelivery")
    candidate = _ack_candidate(state, result, next_destination_state)
    verified = verify_ack_provenance_v1(candidate)
    if isinstance(verified, I05AckRejectV1):
        return _reject(
            I06RecoveryCodeV1.PROVENANCE_REJECTED,
            "ack",
            verified.code.value,
        )
    return verified


def redeliver_and_record_ack_v1(value: object) -> I06TransitionResultV1:
    """Redeliver one stable effect and durably record at most one local ack."""

    validated = _validate_state(value)
    if isinstance(validated, I06RecoveryRejectV1):
        return validated
    state = validated
    if state.phase not in (
        I06PhaseV1.RESPONSE_LOST_AFTER_DESTINATION_ACCEPTANCE,
        I06PhaseV1.ACK_DURABLE,
    ):
        return _reject(I06RecoveryCodeV1.INVALID_PHASE, "redelivery")
    if state.delivery_attempts >= dra.U32_MAX:
        return _reject(I06RecoveryCodeV1.ATTEMPT_OVERFLOW, "delivery_attempts")
    verified = _verified_redelivery_ack(state)
    if isinstance(verified, I06RecoveryRejectV1):
        return verified
    if state.phase is I06PhaseV1.RESPONSE_LOST_AFTER_DESTINATION_ACCEPTANCE:
        try:
            journal = I06AckJournalV1(ack=verified)
            next_state = I06DeliveryStateV1(
                effect=state.effect,
                contract=state.contract,
                destination_state=state.destination_state,
                phase=I06PhaseV1.ACK_DURABLE,
                delivery_attempts=state.delivery_attempts + 1,
                ack_journal=journal,
            )
        except (I06Error, dra.DurableRetractionError, TypeError, ValueError):
            return _reject(I06RecoveryCodeV1.INVALID_STATE, "ack_write")
        return I06RecoveryResultV1(
            outcome=I06RecoveryOutcomeV1.REDELIVERED_ALREADY_ACCEPTED,
            state=next_state,
        )

    if state.ack_journal is None:
        return _reject(I06RecoveryCodeV1.INVALID_STATE, "ack_journal")
    if verified != state.ack_journal.ack:
        return _reject(I06RecoveryCodeV1.ACK_COLLISION, "ack_journal")
    try:
        next_state = I06DeliveryStateV1(
            effect=state.effect,
            contract=state.contract,
            destination_state=state.destination_state,
            phase=I06PhaseV1.ACK_DURABLE,
            delivery_attempts=state.delivery_attempts + 1,
            ack_journal=state.ack_journal,
        )
    except (I06Error, dra.DurableRetractionError, TypeError, ValueError):
        return _reject(I06RecoveryCodeV1.INVALID_STATE, "redelivery")
    return I06RecoveryResultV1(
        outcome=I06RecoveryOutcomeV1.ALREADY_DURABLE_NOOP,
        state=next_state,
    )


__all__ = (
    "I06AckJournalV1",
    "I06DeliveryStateV1",
    "I06Error",
    "I06PhaseV1",
    "I06RecoveryCodeV1",
    "I06RecoveryOutcomeV1",
    "I06RecoveryRejectV1",
    "I06RecoveryResultV1",
    "I06StateResultV1",
    "I06TransitionResultV1",
    "lose_response_after_destination_acceptance_v1",
    "new_delivery_state_v1",
    "redeliver_and_record_ack_v1",
)
