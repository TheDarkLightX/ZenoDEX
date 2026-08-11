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
from threading import Lock
from typing import Protocol

from ..core.m6_safe_mount_types_v1 import (
    M6PromotionSubjectV1,
    OutboxAtomV1,
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


class M6OutboxDeliveryStatusV1(str, Enum):
    DELIVERED = "delivered"
    ALREADY_DELIVERED = "already_delivered"
    NOT_COMMITTED = "not_committed"
    RETRYABLE_FAILURE = "retryable_failure"
    REJECTED = "rejected"


class M6TauTransportError(RuntimeError):
    """Expected external transport failure that permits a later retry."""


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
    """External transport port; it must preserve effect identity on retry."""

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
    """Idempotent delivery shell over a canonical durable M6 ledger.

    The in-memory cache suppresses duplicate calls within one process.  A
    restarted process deliberately retries the same effect ID; the external
    transport must provide its own durable idempotency for exactly-once
    destination semantics.
    """

    def __init__(self, subject: M6PromotionSubjectV1, store: M6DurableLedgerStoreV1) -> None:
        if not isinstance(subject, M6PromotionSubjectV1):
            raise TypeError("delivery subject is not typed")
        if not isinstance(store, M6DurableLedgerStoreV1):
            raise TypeError("delivery source must be the M6 durable ledger store")
        if store.subject != subject:
            raise ValueError("delivery store promotion subject mismatch")
        self._subject = subject
        self._store = store
        self._delivered: dict[str, TauWithdrawalDeliveryReceiptV1] = {}
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
        if not callable(deliver):
            return M6OutboxDeliveryResultV1(
                M6OutboxDeliveryStatusV1.REJECTED,
                effect_id,
                reason="Tau transport does not expose deliver",
            )
        with self._lock:
            try:
                reopened = self._store.reopen()
            except M6DurableCorruptionError as exc:
                return M6OutboxDeliveryResultV1(
                    M6OutboxDeliveryStatusV1.REJECTED,
                    effect_id,
                    reason=f"durable ledger reopen failed: {exc}",
                )
            if reopened.subject != self._subject:
                return M6OutboxDeliveryResultV1(
                    M6OutboxDeliveryStatusV1.REJECTED,
                    effect_id,
                    reason="reopened ledger promotion subject mismatch",
                )
            matches = _find_committed_effect(reopened.records, effect_id)
            if isinstance(matches, str):
                return M6OutboxDeliveryResultV1(
                    M6OutboxDeliveryStatusV1.REJECTED,
                    effect_id,
                    reason=matches,
                )
            if matches is None:
                return M6OutboxDeliveryResultV1(
                    M6OutboxDeliveryStatusV1.NOT_COMMITTED,
                    effect_id,
                    reason="no committed outbox row matches effect id",
                )
            record, effect = matches
            if effect.effect_type != "tau_withdrawal":
                return M6OutboxDeliveryResultV1(
                    M6OutboxDeliveryStatusV1.REJECTED,
                    effect_id,
                    reason="committed outbox effect type is not Tau withdrawal",
                )
            if effect.source_state_root != record.pre_state_root:
                return M6OutboxDeliveryResultV1(
                    M6OutboxDeliveryStatusV1.REJECTED,
                    effect_id,
                    reason="outbox source root is not bound to committed record",
                )
            cached = self._delivered.get(effect_id)
            if cached is not None:
                cached_reason = _receipt_binding_reason(effect, cached)
                if cached_reason is not None:
                    return M6OutboxDeliveryResultV1(
                        M6OutboxDeliveryStatusV1.REJECTED,
                        effect_id,
                        reason=cached_reason,
                    )
                return M6OutboxDeliveryResultV1(
                    M6OutboxDeliveryStatusV1.ALREADY_DELIVERED,
                    effect_id,
                    receipt=cached,
                )
            try:
                receipt = deliver(effect)
            except M6TauTransportError as exc:
                return M6OutboxDeliveryResultV1(
                    M6OutboxDeliveryStatusV1.RETRYABLE_FAILURE,
                    effect_id,
                    reason=str(exc),
                )
            if not isinstance(receipt, TauWithdrawalDeliveryReceiptV1):
                return M6OutboxDeliveryResultV1(
                    M6OutboxDeliveryStatusV1.REJECTED,
                    effect_id,
                    reason="Tau transport returned an untyped receipt",
                )
            receipt_reason = _receipt_binding_reason(effect, receipt)
            if receipt_reason is not None:
                return M6OutboxDeliveryResultV1(
                    M6OutboxDeliveryStatusV1.REJECTED,
                    effect_id,
                    reason=receipt_reason,
                )
            self._delivered[effect_id] = receipt
            return M6OutboxDeliveryResultV1(
                M6OutboxDeliveryStatusV1.DELIVERED,
                effect_id,
                receipt=receipt,
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


__all__ = [
    "M6OutboxDeliveryPortV1",
    "M6OutboxDeliveryResultV1",
    "M6OutboxDeliveryStatusV1",
    "M6TauTransportError",
    "M6TauWithdrawalTransportV1",
    "TauWithdrawalDeliveryReceiptV1",
]
