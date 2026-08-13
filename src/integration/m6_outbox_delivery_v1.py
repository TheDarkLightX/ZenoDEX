"""Research-only Tau outbox delivery shell for the M6 durable ledger.

The durable ledger is the source of committed effects.  This adapter reads a
reopened, canonical ledger, selects one already-committed Tau withdrawal, and
hands the exact outbox atom to an external transport.  It never changes M6
state and it never creates acknowledgment authority.  A transport receipt
must still pass the normal core authority-verifier path before an acknowledgment
command can clear the withdrawal liability.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from threading import Lock
from typing import Callable, Mapping, Protocol, cast

from ..core.m6_safe_mount_types_v1 import (
    M6ApplicationStateV1,
    M6PromotionSubjectV1,
    OutboxAtomV1,
    TauWithdrawalStatusV1,
    _require_positive_int,
    _require_root,
    _require_token,
    hash_v1,
)
from .m6_durable_store_v1 import (
    M6DurableCorruptionError,
    M6DurableLedgerStoreV1,
    M6PublishedRecordV1,
)
from .m6_outbox_delivery_journal_v1 import (
    M6OutboxDeliveryAttemptStatusV1,
    M6OutboxDeliveryAttemptV1,
    M6OutboxDeliveryJournalError,
    M6OutboxDeliveryJournalV1,
)


class M6OutboxDeliveryStatusV1(str, Enum):
    DELIVERED = "delivered"
    ALREADY_DELIVERED = "already_delivered"
    NOT_COMMITTED = "not_committed"
    RETRYABLE_FAILURE = "retryable_failure"
    OUTCOME_UNKNOWN = "outcome_unknown"
    REJECTED = "rejected"


class M6TauTransportError(RuntimeError):
    """Typed pre-submit transport refusal that permits a later retry.

    This error is handled only from ``prepare``. Once ``deliver`` is entered,
    every exception is outcome-unknown and remains durably quarantined.
    """


@dataclass(frozen=True, slots=True)
class TauWithdrawalDeliveryReceiptV1:
    """Data-only transport receipt bound to one committed outbox atom."""

    effect_id: str
    tau_receipt_root: str
    source_state_root: str
    destination: str
    asset: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token(self.effect_id, name="delivery effect id")
        _require_root(self.tau_receipt_root, name="Tau delivery receipt root")
        _require_root(self.source_state_root, name="delivery source state root")
        _require_token(self.destination, name="delivery destination")
        _require_token(self.asset, name="delivery asset")
        _require_positive_int(self.amount_atoms, name="delivery amount")

    @property
    def receipt_root(self) -> str:
        return hash_v1("m6-tau-withdrawal-delivery-receipt-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "effect_id": self.effect_id,
            "tau_receipt_root": self.tau_receipt_root,
            "source_state_root": self.source_state_root,
            "destination": self.destination,
            "asset": self.asset,
            "amount_atoms": self.amount_atoms,
        }


class M6TauWithdrawalTransportV1(Protocol):
    """External transport port with a non-submitting readiness phase."""

    def prepare(self, effect: OutboxAtomV1) -> None:
        """Check readiness without submitting or moving destination value."""

    def deliver(self, effect: OutboxAtomV1) -> TauWithdrawalDeliveryReceiptV1: ...


@dataclass(frozen=True, slots=True)
class M6OutboxDeliveryResultV1:
    status: M6OutboxDeliveryStatusV1
    effect_id: str | None
    receipt: TauWithdrawalDeliveryReceiptV1 | None = None
    reason: str | None = None

    def __post_init__(self) -> None:
        if not isinstance(self.status, M6OutboxDeliveryStatusV1):
            raise TypeError("outbox delivery status is not closed")
        if self.effect_id is not None:
            _require_token(self.effect_id, name="delivery result effect id")
        successful = self.status in (
            M6OutboxDeliveryStatusV1.DELIVERED,
            M6OutboxDeliveryStatusV1.ALREADY_DELIVERED,
        )
        if successful and (self.effect_id is None or self.receipt is None):
            raise ValueError("successful delivery requires an effect and receipt")
        if successful and self.receipt is not None and self.receipt.effect_id != self.effect_id:
            raise ValueError("delivery result receipt is bound to another effect")
        if not successful and self.receipt is not None:
            raise ValueError("unsuccessful delivery cannot retain a receipt")


class M6OutboxDeliveryPortV1:
    """Fail-closed delivery shell over a ledger and durable attempt journal.

    The journal reserves an effect before transport. A process crash, untyped
    exception, malformed receipt, or receipt-binding mismatch leaves PENDING
    evidence that blocks automatic redelivery until explicit reconciliation.
    """

    def __init__(
        self,
        subject: M6PromotionSubjectV1,
        store: M6DurableLedgerStoreV1,
        journal: M6OutboxDeliveryJournalV1,
    ) -> None:
        if not isinstance(subject, M6PromotionSubjectV1):
            raise TypeError("delivery subject is not typed")
        if not isinstance(store, M6DurableLedgerStoreV1):
            raise TypeError("delivery source must be the M6 durable ledger store")
        if store.subject != subject:
            raise ValueError("delivery store promotion subject mismatch")
        if not isinstance(journal, M6OutboxDeliveryJournalV1):
            raise TypeError("delivery attempt journal is not typed")
        if journal.subject != subject:
            raise ValueError("delivery journal promotion subject mismatch")
        if journal.root.absolute() != m6_outbox_delivery_journal_path_v1(store).absolute():
            raise ValueError("delivery journal path is not bound to the durable ledger")
        self._subject = subject
        self._store = store
        self._journal = journal
        self._lock = Lock()

    @property
    def subject(self) -> M6PromotionSubjectV1:
        return self._subject

    def deliver(
        self,
        effect_id: str,
        transport: M6TauWithdrawalTransportV1,
    ) -> M6OutboxDeliveryResultV1:
        """Deliver only an effect found in a reopened committed publication."""

        try:
            _require_token(effect_id, name="delivery effect id")
        except (TypeError, ValueError):
            return M6OutboxDeliveryResultV1(
                M6OutboxDeliveryStatusV1.REJECTED,
                None,
                reason="effect id is malformed",
            )
        deliver = getattr(transport, "deliver", None)
        prepare = getattr(transport, "prepare", None)
        if not callable(prepare) or not callable(deliver):
            return M6OutboxDeliveryResultV1(
                M6OutboxDeliveryStatusV1.REJECTED,
                effect_id,
                reason="Tau transport does not expose prepare and deliver",
            )
        with self._lock:
            prepared = self._prepare_effect(effect_id)
            if isinstance(prepared, M6OutboxDeliveryResultV1):
                return prepared
            effect, effect_root = prepared
            reservation = self._reserve_effect(effect, effect_root)
            if isinstance(reservation, M6OutboxDeliveryResultV1):
                return reservation
            attempt, reserved = reservation
            if not reserved:
                return _result_from_existing_attempt(effect, attempt)
            readiness = self._prepare_transport(
                effect,
                effect_root,
                cast(Callable[[OutboxAtomV1], object], prepare),
            )
            if readiness is not None:
                return readiness
            return self._invoke_transport(
                effect,
                effect_root,
                cast(Callable[[OutboxAtomV1], object], deliver),
            )

    def _prepare_transport(
        self,
        effect: OutboxAtomV1,
        effect_root: str,
        prepare: Callable[[OutboxAtomV1], object],
    ) -> M6OutboxDeliveryResultV1 | None:
        try:
            readiness = prepare(effect)
        except M6TauTransportError:
            return self._record_retryable(effect, effect_root)
        except Exception:
            return _outcome_unknown(
                effect.effect_id,
                "Tau transport pre-submit phase failed unexpectedly",
            )
        if readiness is not None:
            return _outcome_unknown(
                effect.effect_id,
                "Tau transport pre-submit phase returned an invalid result",
            )
        return None

    def _prepare_effect(
        self,
        effect_id: str,
    ) -> tuple[OutboxAtomV1, str] | M6OutboxDeliveryResultV1:
        try:
            reopened = self._store.reopen()
        except M6DurableCorruptionError:
            return _rejected(effect_id, "durable ledger reopen failed")
        if reopened.subject != self._subject:
            return _rejected(effect_id, "reopened ledger promotion subject mismatch")
        matches = _find_committed_effect(reopened.records, effect_id)
        if isinstance(matches, str):
            return _rejected(effect_id, matches)
        if matches is None:
            return M6OutboxDeliveryResultV1(
                M6OutboxDeliveryStatusV1.NOT_COMMITTED,
                effect_id,
                reason="no committed outbox row matches effect id",
            )
        record, effect = matches
        if effect.effect_type != "tau_withdrawal":
            return _rejected(effect_id, "committed outbox effect type is not Tau withdrawal")
        if effect.source_state_root != record.pre_state_root:
            return _rejected(
                effect_id,
                "outbox source root is not bound to committed record",
            )
        terminal = _terminal_acknowledgment_receipt(reopened.state, effect)
        if isinstance(terminal, str):
            return _rejected(effect_id, terminal)
        if terminal is not None:
            return M6OutboxDeliveryResultV1(
                M6OutboxDeliveryStatusV1.ALREADY_DELIVERED,
                effect_id,
                receipt=terminal,
            )
        effect_root = hash_v1("m6-tau-withdrawal-outbox-effect-v1", effect.to_canonical())
        return effect, effect_root

    def _reserve_effect(
        self,
        effect: OutboxAtomV1,
        effect_root: str,
    ) -> tuple[M6OutboxDeliveryAttemptV1, bool] | M6OutboxDeliveryResultV1:
        try:
            return self._journal.reserve(
                effect_id=effect.effect_id,
                effect_root=effect_root,
            )
        except M6OutboxDeliveryJournalError:
            return _rejected(effect.effect_id, "durable delivery journal validation failed")

    def _invoke_transport(
        self,
        effect: OutboxAtomV1,
        effect_root: str,
        deliver: Callable[[OutboxAtomV1], object],
    ) -> M6OutboxDeliveryResultV1:
        try:
            receipt = deliver(effect)
        except Exception:
            # The call may have moved value before response loss. The durable
            # PENDING reservation quarantines every later retry.
            return _outcome_unknown(effect.effect_id, "Tau transport failed unexpectedly")
        if not isinstance(receipt, TauWithdrawalDeliveryReceiptV1):
            return _outcome_unknown(
                effect.effect_id,
                "Tau transport outcome lacks a typed receipt; reconciliation required",
            )
        receipt_reason = _receipt_binding_reason(effect, receipt)
        if receipt_reason is not None:
            return _outcome_unknown(effect.effect_id, receipt_reason)
        try:
            self._journal.mark_delivered(
                effect_id=effect.effect_id,
                effect_root=effect_root,
                receipt=receipt.to_canonical(),
            )
        except M6OutboxDeliveryJournalError:
            return _outcome_unknown(
                effect.effect_id,
                "Tau delivery receipt could not be persisted",
            )
        return M6OutboxDeliveryResultV1(
            M6OutboxDeliveryStatusV1.DELIVERED,
            effect.effect_id,
            receipt=receipt,
        )

    def _record_retryable(
        self,
        effect: OutboxAtomV1,
        effect_root: str,
    ) -> M6OutboxDeliveryResultV1:
        try:
            self._journal.mark_retryable(
                effect_id=effect.effect_id,
                effect_root=effect_root,
            )
        except M6OutboxDeliveryJournalError:
            return _outcome_unknown(
                effect.effect_id,
                "delivery retry state could not be persisted",
            )
        return M6OutboxDeliveryResultV1(
            M6OutboxDeliveryStatusV1.RETRYABLE_FAILURE,
            effect.effect_id,
            reason="Tau transport unavailable",
        )


def m6_outbox_delivery_journal_path_v1(store: M6DurableLedgerStoreV1) -> Path:
    """Return the one sibling journal path bound to a durable ledger path."""

    if not isinstance(store, M6DurableLedgerStoreV1):
        raise TypeError("delivery journal path requires an M6 durable ledger")
    return store.root.parent / f"{store.root.name}.outbox-delivery-v1"


def _rejected(effect_id: str, reason: str) -> M6OutboxDeliveryResultV1:
    return M6OutboxDeliveryResultV1(
        M6OutboxDeliveryStatusV1.REJECTED,
        effect_id,
        reason=reason,
    )


def _outcome_unknown(effect_id: str, reason: str) -> M6OutboxDeliveryResultV1:
    return M6OutboxDeliveryResultV1(
        M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN,
        effect_id,
        reason=reason,
    )


def _result_from_existing_attempt(
    effect: OutboxAtomV1,
    attempt: M6OutboxDeliveryAttemptV1,
) -> M6OutboxDeliveryResultV1:
    if attempt.status is M6OutboxDeliveryAttemptStatusV1.PENDING:
        return _outcome_unknown(
            effect.effect_id,
            "Tau delivery outcome is unknown; reconciliation required",
        )
    if attempt.status is not M6OutboxDeliveryAttemptStatusV1.DELIVERED:
        return _rejected(
            effect.effect_id,
            "delivery journal returned an invalid reservation state",
        )
    try:
        cached = _receipt_from_mapping(attempt.receipt_mapping())
    except (M6OutboxDeliveryJournalError, TypeError, ValueError):
        return _rejected(effect.effect_id, "durable delivery receipt is invalid")
    cached_reason = _receipt_binding_reason(effect, cached)
    if cached_reason is not None:
        return _rejected(effect.effect_id, cached_reason)
    return M6OutboxDeliveryResultV1(
        M6OutboxDeliveryStatusV1.ALREADY_DELIVERED,
        effect.effect_id,
        receipt=cached,
    )


def _find_committed_effect(
    records: tuple[M6PublishedRecordV1, ...],
    effect_id: str,
) -> tuple[M6PublishedRecordV1, OutboxAtomV1] | str | None:
    matches: list[tuple[M6PublishedRecordV1, OutboxAtomV1]] = []
    for record in records:
        for effect in record.outbox_atoms:
            if effect.effect_id == effect_id:
                matches.append((record, effect))
    if len(matches) > 1:
        return "effect id appears in multiple committed outbox rows"
    return matches[0] if matches else None


def _terminal_acknowledgment_receipt(
    state: M6ApplicationStateV1,
    effect: OutboxAtomV1,
) -> TauWithdrawalDeliveryReceiptV1 | str | None:
    """Project authoritative terminal acknowledgment into delivery evidence."""

    withdrawals = tuple(
        item for item in state.withdrawals if item.withdrawal_id == effect.effect_id
    )
    if len(withdrawals) != 1:
        return "committed outbox row lacks one matching withdrawal liability"
    withdrawal = withdrawals[0]
    if (
        withdrawal.asset != effect.asset
        or withdrawal.amount_atoms != effect.amount_atoms
        or withdrawal.source_state_root != effect.source_state_root
    ):
        return "committed outbox row conflicts with withdrawal liability"
    acknowledgments = tuple(
        item for item in state.acknowledgments if item.withdrawal_id == effect.effect_id
    )
    if withdrawal.status is TauWithdrawalStatusV1.PENDING:
        if acknowledgments:
            return "pending withdrawal already has terminal acknowledgment evidence"
        return None
    if withdrawal.status is not TauWithdrawalStatusV1.ACKNOWLEDGED:
        return "withdrawal status is not supported by the delivery shell"
    if len(acknowledgments) != 1:
        return "acknowledged withdrawal lacks one terminal acknowledgment"
    acknowledgment = acknowledgments[0]
    if acknowledgment.provenance_root != effect.source_state_root:
        return "withdrawal acknowledgment provenance conflicts with outbox row"
    return TauWithdrawalDeliveryReceiptV1(
        effect_id=effect.effect_id,
        tau_receipt_root=acknowledgment.tau_receipt_root,
        source_state_root=effect.source_state_root,
        destination=effect.destination,
        asset=effect.asset,
        amount_atoms=effect.amount_atoms,
    )


def _receipt_binding_reason(
    effect: OutboxAtomV1,
    receipt: TauWithdrawalDeliveryReceiptV1,
) -> str | None:
    bindings = (
        ("effect id", effect.effect_id, receipt.effect_id),
        ("source state root", effect.source_state_root, receipt.source_state_root),
        ("destination", effect.destination, receipt.destination),
        ("asset", effect.asset, receipt.asset),
        ("amount", effect.amount_atoms, receipt.amount_atoms),
    )
    for name, expected, actual in bindings:
        if expected != actual:
            return f"Tau delivery receipt {name} mismatch"
    return None


def _receipt_from_mapping(
    value: Mapping[str, object] | None,
) -> TauWithdrawalDeliveryReceiptV1:
    if value is None:
        raise TypeError("delivery receipt mapping is missing")
    expected = {
        "effect_id",
        "tau_receipt_root",
        "source_state_root",
        "destination",
        "asset",
        "amount_atoms",
    }
    if set(value) != expected:
        raise ValueError("delivery receipt fields are not closed")
    return TauWithdrawalDeliveryReceiptV1(
        effect_id=_require_token(value["effect_id"], name="journal receipt effect id"),
        tau_receipt_root=_require_root(
            value["tau_receipt_root"],
            name="journal Tau receipt root",
        ),
        source_state_root=_require_root(
            value["source_state_root"],
            name="journal receipt source root",
        ),
        destination=_require_token(
            value["destination"],
            name="journal receipt destination",
        ),
        asset=_require_token(value["asset"], name="journal receipt asset"),
        amount_atoms=_require_positive_int(
            value["amount_atoms"],
            name="journal receipt amount",
        ),
    )


__all__ = [
    "M6OutboxDeliveryPortV1",
    "M6OutboxDeliveryAttemptStatusV1",
    "M6OutboxDeliveryAttemptV1",
    "M6OutboxDeliveryJournalError",
    "M6OutboxDeliveryJournalV1",
    "M6OutboxDeliveryResultV1",
    "M6OutboxDeliveryStatusV1",
    "M6TauTransportError",
    "M6TauWithdrawalTransportV1",
    "TauWithdrawalDeliveryReceiptV1",
    "m6_outbox_delivery_journal_path_v1",
]
