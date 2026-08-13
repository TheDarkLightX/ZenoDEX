from __future__ import annotations

from dataclasses import dataclass, replace
from pathlib import Path
from threading import Event, Thread
from typing import Any

import pytest

from src.core.m6_safe_mount_transition_v1 import run_m6_transition_v1
from src.core.m6_safe_mount_types_v1 import (
    AcceptCandidateV1,
    EconomicAtomKindV1,
    EconomicAtomV1,
    GlobalCommandKindV1,
    GlobalCommandV1,
    M6PromotionSubjectV1,
    initial_application_state_v1,
)
from src.integration.m6_commit_port_v1 import CommitStatusV1
from src.integration.m6_durable_store_v1 import (
    M6DurableCorruptionError,
    M6DurableLedgerStoreV1,
)
from src.integration.m6_outbox_delivery_v1 import (
    M6OutboxDeliveryJournalError,
    M6OutboxDeliveryJournalV1,
    M6OutboxDeliveryPortV1,
    M6OutboxDeliveryResultV1,
    M6OutboxDeliveryStatusV1,
    M6TauTransportError,
    TauWithdrawalDeliveryReceiptV1,
    m6_outbox_delivery_journal_path_v1,
)
from tests.core.test_m6_safe_mount_v1 import _with_ack_evidence
from tests.integration.test_m6_durable_store_v1 import (
    _TEST_FINALITY_VERIFIER,
    _context,
    _finality_and_tau,
    _root,
    _subject,
)


@dataclass
class _StableReceiptTransport:
    calls: list[str]
    fail: bool = False
    malformed: bool = False
    tamper: bool = False
    unexpected: bool = False

    def prepare(self, _effect: Any) -> None:
        if self.fail:
            raise M6TauTransportError("Tau unavailable")

    def deliver(self, effect: Any) -> Any:
        self.calls.append(getattr(effect, "effect_id", "invalid"))
        if self.unexpected:
            raise RuntimeError("private transport credential")
        if self.malformed:
            return object()
        return TauWithdrawalDeliveryReceiptV1(
            effect_id=effect.effect_id,
            tau_receipt_root=_root(700),
            source_state_root=effect.source_state_root,
            destination=("wrong-destination" if self.tamper else effect.destination),
            asset=effect.asset,
            amount_atoms=effect.amount_atoms,
        )


@dataclass
class _BlockingReceiptTransport:
    calls: list[str]
    entered: Event
    release: Event

    def prepare(self, _effect: Any) -> None:
        return None

    def deliver(self, effect: Any) -> TauWithdrawalDeliveryReceiptV1:
        self.calls.append(effect.effect_id)
        self.entered.set()
        if not self.release.wait(5):
            raise RuntimeError("test transport release was not signaled")
        return TauWithdrawalDeliveryReceiptV1(
            effect_id=effect.effect_id,
            tau_receipt_root=_root(704),
            source_state_root=effect.source_state_root,
            destination=effect.destination,
            asset=effect.asset,
            amount_atoms=effect.amount_atoms,
        )


@dataclass
class _LateRefusalTransport:
    calls: list[str]

    def prepare(self, _effect: Any) -> None:
        return None

    def deliver(self, effect: Any) -> TauWithdrawalDeliveryReceiptV1:
        self.calls.append(effect.effect_id)
        raise M6TauTransportError("late refusal after submission")


def _withdrawal_store(tmp_path: Path) -> tuple[M6PromotionSubjectV1, M6DurableLedgerStoreV1, str]:
    subject = _subject()
    initial = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 10),),
    )
    store = M6DurableLedgerStoreV1.create(
        tmp_path / "ledger",
        subject,
        initial,
        finality_verifier=_TEST_FINALITY_VERIFIER,
    )
    command = GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL,
        command_id=_root(1_900),
        sender="alice",
        nonce=1,
        payload={
            "withdrawal_id": "delivery-1",
            "asset": "A",
            "amount_atoms": 2,
            "destination": "tau-alice",
        },
    )
    candidate = run_m6_transition_v1(subject, initial, _context(subject, initial, 1), command)
    assert isinstance(candidate, AcceptCandidateV1)
    finality, tau = _finality_and_tau(subject, candidate, "delivery-batch")
    committed = store.publish(candidate, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED
    assert committed.record is not None
    return subject, store, committed.record.outbox_atoms[0].effect_id


def _delivery_port(
    tmp_path: Path,
    subject: M6PromotionSubjectV1,
    store: M6DurableLedgerStoreV1,
) -> M6OutboxDeliveryPortV1:
    journal_path = m6_outbox_delivery_journal_path_v1(store)
    journal = (
        M6OutboxDeliveryJournalV1(journal_path, subject)
        if journal_path.exists()
        else M6OutboxDeliveryJournalV1.create(journal_path, subject)
    )
    return M6OutboxDeliveryPortV1(subject, store, journal)


def test_given_foreign_subject_when_reopening_delivery_journal_then_fail_closed(
    tmp_path: Path,
) -> None:
    subject = _subject()
    journal_path = tmp_path / "delivery-journal"
    M6OutboxDeliveryJournalV1.create(journal_path, subject)
    foreign_subject = replace(subject, deployment=_root(1_899))

    with pytest.raises(M6OutboxDeliveryJournalError, match="subject mismatch"):
        M6OutboxDeliveryJournalV1(journal_path, foreign_subject)


def test_given_unbound_journal_path_when_constructing_port_then_rejects(
    tmp_path: Path,
) -> None:
    subject, store, _ = _withdrawal_store(tmp_path)
    unbound = M6OutboxDeliveryJournalV1.create(tmp_path / "unbound-journal", subject)

    with pytest.raises(ValueError, match="path is not bound"):
        M6OutboxDeliveryPortV1(subject, store, unbound)


def test_given_no_committed_outbox_when_delivering_then_transport_is_never_called(tmp_path: Path) -> None:
    subject = _subject()
    store = M6DurableLedgerStoreV1.create(
        tmp_path / "ledger", subject, initial_application_state_v1(subject)
    )
    transport = _StableReceiptTransport([])

    result = _delivery_port(tmp_path, subject, store).deliver("missing-effect", transport)

    assert result.status is M6OutboxDeliveryStatusV1.NOT_COMMITTED
    assert transport.calls == []


@pytest.mark.parametrize("effect_id", ["bad id", "snowman-☃", "x" * 129])
def test_given_malformed_effect_id_when_delivering_then_typed_reject_without_transport(
    tmp_path: Path,
    effect_id: str,
) -> None:
    subject, store, _ = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])

    result = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    assert result.status is M6OutboxDeliveryStatusV1.REJECTED
    assert result.effect_id is None
    assert result.reason == "effect id is malformed"
    assert transport.calls == []


def test_given_committed_withdrawal_when_retried_then_one_process_delivery_is_idempotent(
    tmp_path: Path,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    port = _delivery_port(tmp_path, subject, store)

    first = port.deliver(effect_id, transport)
    second = port.deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert first.receipt is not None
    assert second.status is M6OutboxDeliveryStatusV1.ALREADY_DELIVERED
    assert second.receipt == first.receipt
    assert transport.calls == [effect_id]


def test_given_delivery_when_committed_then_ledger_state_and_head_remain_unchanged(
    tmp_path: Path,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    before = store.reopen()
    transport = _StableReceiptTransport([])

    result = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    after = store.reopen()
    assert result.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert after == before


def test_given_cached_delivery_when_reopen_fails_then_cache_cannot_bypass_canonical_source(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    port = _delivery_port(tmp_path, subject, store)
    first = port.deliver(effect_id, transport)

    def fail_reopen() -> object:
        raise M6DurableCorruptionError("reopen failed")

    monkeypatch.setattr(store, "reopen", fail_reopen)
    second = port.deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert second.status is M6OutboxDeliveryStatusV1.REJECTED
    assert transport.calls == [effect_id]


def test_given_mismatched_transport_receipt_when_retried_then_effect_is_quarantined(
    tmp_path: Path,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([], tamper=True)
    port = _delivery_port(tmp_path, subject, store)

    uncertain = port.deliver(effect_id, transport)
    transport.tamper = False
    retried = port.deliver(effect_id, transport)

    assert uncertain.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert retried.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert transport.calls == [effect_id]


def test_delivery_result_rejects_receipt_bound_to_another_effect() -> None:
    receipt = TauWithdrawalDeliveryReceiptV1(
        effect_id="effect-a",
        tau_receipt_root=_root(701),
        source_state_root=_root(702),
        destination="tau-alice",
        asset="A",
        amount_atoms=1,
    )

    with pytest.raises(ValueError, match="another effect"):
        M6OutboxDeliveryResultV1(
            M6OutboxDeliveryStatusV1.DELIVERED,
            "effect-b",
            receipt=receipt,
        )


def test_given_process_restart_when_redelivering_then_durable_receipt_suppresses_transport(
    tmp_path: Path,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    first = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    second = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert second.status is M6OutboxDeliveryStatusV1.ALREADY_DELIVERED
    assert second.receipt == first.receipt
    assert transport.calls == [effect_id]


def test_given_acknowledged_withdrawal_and_fresh_journal_then_transport_is_never_replayed(
    tmp_path: Path,
) -> None:
    """Canonical acknowledgment state closes delivery even if its journal is new."""

    # Arrange: publish a withdrawal and its provenance-bound Tau receipt before
    # constructing any delivery journal.
    subject, store, effect_id = _withdrawal_store(tmp_path)
    pending = store.reopen().state
    acknowledgment = GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        command_id=_root(1_901),
        sender="alice",
        nonce=2,
        payload={
            "withdrawal_id": effect_id,
            "ack_root": _root(1_902),
            "tau_receipt_root": _root(1_903),
        },
    )
    acknowledged = run_m6_transition_v1(
        subject,
        pending,
        _with_ack_evidence(
            subject,
            pending,
            acknowledgment,
            pending.withdrawals[0].source_state_root,
        ),
        acknowledgment,
    )
    assert isinstance(acknowledged, AcceptCandidateV1)
    finality, tau = _finality_and_tau(subject, acknowledged, "delivery-ack-batch")
    committed = store.publish(acknowledged, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED
    transport = _StableReceiptTransport([])

    # Act: a brand-new journal has no local success record for the effect.
    result = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    # Assert: the authoritative acknowledgment supplies terminal evidence and
    # the external transport cannot be called again.
    assert result.status is M6OutboxDeliveryStatusV1.ALREADY_DELIVERED
    assert result.receipt is not None
    assert result.receipt.tau_receipt_root == _root(1_903)
    assert transport.calls == []


@pytest.mark.parametrize("failure_mode", ["malformed", "unavailable"])
def test_given_delivery_failure_when_retried_then_no_false_success_is_cached(
    tmp_path: Path,
    failure_mode: str,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport(
        [], malformed=failure_mode == "malformed", fail=failure_mode == "unavailable"
    )
    port = _delivery_port(tmp_path, subject, store)

    failed = port.deliver(effect_id, transport)
    transport.malformed = False
    transport.fail = False
    retried = port.deliver(effect_id, transport)

    expected_failure = (
        M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
        if failure_mode == "malformed"
        else M6OutboxDeliveryStatusV1.RETRYABLE_FAILURE
    )
    assert failed.status is expected_failure
    expected_retry = (
        M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
        if failure_mode == "malformed"
        else M6OutboxDeliveryStatusV1.DELIVERED
    )
    assert retried.status is expected_retry
    assert len(transport.calls) == (1 if failure_mode == "malformed" else 1)


def test_given_post_effect_response_loss_when_retried_then_delivery_is_quarantined_without_duplication(
    tmp_path: Path,
) -> None:
    # Arrange: the transport records the value-moving call, then loses the
    # response through an untyped exception that may contain private detail.
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([], unexpected=True)
    # Act: a caller retries from a fresh port after the outcome became unknowable.
    failed = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)
    transport.unexpected = False
    retried = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    # Assert: the effect remains quarantined and reaches transport only once.
    assert failed.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert failed.reason == "Tau transport failed unexpectedly"
    assert "credential" not in failed.reason
    assert retried.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert transport.calls == [effect_id]


def test_given_typed_refusal_after_submit_when_retried_then_it_is_still_quarantined(
    tmp_path: Path,
) -> None:
    """Exception type cannot convert a post-submit outcome into retry authority."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _LateRefusalTransport([])

    first = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)
    second = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert second.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert transport.calls == [effect_id]


def test_given_concurrent_ports_when_one_reserved_then_only_one_transport_call_occurs(
    tmp_path: Path,
) -> None:
    """The durable reservation serializes effect authority across port objects."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _BlockingReceiptTransport([], Event(), Event())
    first_results: list[M6OutboxDeliveryResultV1] = []
    first_port = _delivery_port(tmp_path, subject, store)
    second_port = _delivery_port(tmp_path, subject, store)
    worker = Thread(
        target=lambda: first_results.append(first_port.deliver(effect_id, transport)),
        daemon=True,
    )

    worker.start()
    assert transport.entered.wait(5)
    concurrent = second_port.deliver(effect_id, transport)
    transport.release.set()
    worker.join(5)

    assert not worker.is_alive()
    assert len(first_results) == 1
    assert first_results[0].status is M6OutboxDeliveryStatusV1.DELIVERED
    assert concurrent.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert transport.calls == [effect_id]
