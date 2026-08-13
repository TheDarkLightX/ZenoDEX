from __future__ import annotations

import os
import shutil
import sys
from contextlib import contextmanager
from dataclasses import dataclass, replace
from pathlib import Path
from threading import Event, Thread
from typing import Any

import pytest

import src.integration.m6_durable_store_v1 as durable_store_module
import src.integration.m6_outbox_delivery_journal_v1 as journal_module
from src.core.m6_safe_mount_transition_v1 import run_m6_transition_v1
from src.core.m6_safe_mount_types_v1 import (
    ZRPF_COMMAND_COUNT_V1,
    AcceptCandidateV1,
    CommandArgumentV1,
    EconomicAtomKindV1,
    EconomicAtomV1,
    GlobalCommandKindV1,
    GlobalCommandV1,
    M6PromotionSubjectV1,
    initial_application_state_v1,
)
from src.core.m6_zrpf_v1 import (
    execute_direct_batch_v1,
    execute_zrpf_batch_v1,
    verify_zrpf_root_v1,
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
    TauWithdrawalDeliveryRequestV1,
    m6_outbox_delivery_journal_path_v1,
)
from tests.core.test_m6_safe_mount_v1 import _with_ack_evidence
from tests.integration.test_m6_durable_store_v1 import (
    _TEST_FINALITY_VERIFIER,
    _TEST_ZRPF_RECEIPT_VERIFIER,
    _command,
    _context,
    _finality_and_tau,
    _finality_and_tau_for_direct_batch,
    _root,
    _subject,
    _zrpf_finality_and_tau,
)


@dataclass
class _StableReceiptTransport:
    calls: list[str]
    fail: bool = False
    malformed: bool = False
    tamper: bool = False
    unexpected: bool = False

    def prepare(self, _effect: Any) -> None:
        raise AssertionError("advisory prepare callback must never execute")

    def deliver(self, effect: Any) -> Any:
        if self.fail:
            raise M6TauTransportError("Tau unavailable")
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
class _MutatingRequestTransport:
    calls: list[str]

    def deliver(self, request: Any) -> TauWithdrawalDeliveryReceiptV1:
        self.calls.append(request.effect_id)
        object.__setattr__(request, "destination", "tau-mallory")
        return TauWithdrawalDeliveryReceiptV1(
            effect_id=request.effect_id,
            tau_receipt_root=_root(7_001),
            source_state_root=request.source_state_root,
            destination=request.destination,
            asset=request.asset,
            amount_atoms=request.amount_atoms,
        )


@dataclass
class _MutatingReceiptTransport:
    calls: list[str]

    def deliver(self, request: Any) -> TauWithdrawalDeliveryReceiptV1:
        self.calls.append(request.effect_id)
        receipt = TauWithdrawalDeliveryReceiptV1(
            effect_id=request.effect_id,
            tau_receipt_root=_root(7_002),
            source_state_root=request.source_state_root,
            destination=request.destination,
            asset=request.asset,
            amount_atoms=request.amount_atoms,
        )

        class HostileEffectId(str):
            def __str__(self) -> str:
                raise RuntimeError("PRIVATE_RECEIPT_HOOK")

        object.__setattr__(receipt, "effect_id", HostileEffectId(receipt.effect_id))
        return receipt


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


@dataclass
class _EffectfulPrepareRefusalTransport:
    """Hostile rail that violates the advisory prepare contract."""

    applications: list[str]
    first: bool = True

    def prepare(self, effect: Any) -> None:
        if self.first:
            self.first = False
            self.applications.append(effect.effect_id)
            raise M6TauTransportError("claimed refusal after moving value")

    def deliver(self, effect: Any) -> TauWithdrawalDeliveryReceiptV1:
        self.applications.append(effect.effect_id)
        return TauWithdrawalDeliveryReceiptV1(
            effect_id=effect.effect_id,
            tau_receipt_root=_root(706),
            source_state_root=effect.source_state_root,
            destination=effect.destination,
            asset=effect.asset,
            amount_atoms=effect.amount_atoms,
        )


@dataclass
class _ReentrantLedgerTransport:
    store: M6DurableLedgerStoreV1
    observed_roots: list[str]

    def prepare(self, _effect: Any) -> None:
        raise AssertionError("advisory prepare callback must never execute")

    def deliver(self, effect: Any) -> TauWithdrawalDeliveryReceiptV1:
        self.observed_roots.append(self.store.reopen().state.state_root)
        return TauWithdrawalDeliveryReceiptV1(
            effect_id=effect.effect_id,
            tau_receipt_root=_root(707),
            source_state_root=effect.source_state_root,
            destination=effect.destination,
            asset=effect.asset,
            amount_atoms=effect.amount_atoms,
        )


class _AlwaysEqualText(str):
    def __eq__(self, _other: object) -> bool:
        return True

    def __ne__(self, _other: object) -> bool:
        return False


class _ExplodingText(str):
    def encode(self, *_args: object, **_kwargs: object) -> bytes:
        raise RuntimeError("private effect-id credential")


class _HostileTransportLookup:
    def __getattribute__(self, name: str) -> object:
        if name in {"prepare", "deliver"}:
            raise RuntimeError("private transport-interface credential")
        return super().__getattribute__(name)


class _EffectfulTransportLookup:
    """Hostile provider whose interface observation has an external effect."""

    def __init__(self, applications: list[str]) -> None:
        self.applications = applications
        self.first_lookup = True

    def __getattribute__(self, name: str) -> object:
        if name == "deliver":
            applications = object.__getattribute__(self, "applications")
            applications.append("lookup-effect")
            if object.__getattribute__(self, "first_lookup"):
                object.__setattr__(self, "first_lookup", False)
                raise M6TauTransportError("claimed refusal after lookup effect")
        return object.__getattribute__(self, name)

    def deliver(self, effect: Any) -> TauWithdrawalDeliveryReceiptV1:
        self.applications.append(effect.effect_id)
        return TauWithdrawalDeliveryReceiptV1(
            effect_id=effect.effect_id,
            tau_receipt_root=_root(709),
            source_state_root=effect.source_state_root,
            destination=effect.destination,
            asset=effect.asset,
            amount_atoms=effect.amount_atoms,
        )


@dataclass
class _HostileReceiptTransport:
    calls: list[str]

    def prepare(self, _effect: Any) -> None:
        return None

    def deliver(self, effect: Any) -> TauWithdrawalDeliveryReceiptV1:
        self.calls.append(effect.effect_id)
        return TauWithdrawalDeliveryReceiptV1(
            effect_id=effect.effect_id,
            tau_receipt_root=_root(704),
            source_state_root=effect.source_state_root,
            destination=_AlwaysEqualText("attacker-destination"),
            asset=effect.asset,
            amount_atoms=effect.amount_atoms,
        )


class _HostileReceiptSubclass(TauWithdrawalDeliveryReceiptV1):
    def to_canonical(self) -> dict[str, object]:
        raise RuntimeError("private transport credential")


@dataclass
class _HostileReceiptSubclassTransport:
    calls: list[str]

    def prepare(self, _effect: Any) -> None:
        return None

    def deliver(self, effect: Any) -> TauWithdrawalDeliveryReceiptV1:
        self.calls.append(effect.effect_id)
        return _HostileReceiptSubclass(
            effect_id=effect.effect_id,
            tau_receipt_root=_root(705),
            source_state_root=effect.source_state_root,
            destination=effect.destination,
            asset=effect.asset,
            amount_atoms=effect.amount_atoms,
        )


class _HostileStoreSubclass(M6DurableLedgerStoreV1):
    def reopen(self) -> object:
        raise RuntimeError("private forged-ledger credential")


class _HostileJournalSubclass(M6OutboxDeliveryJournalV1):
    @property
    def subject(self) -> M6PromotionSubjectV1:
        raise RuntimeError("private forged-journal credential")


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
    M6OutboxDeliveryJournalV1.create_for_store(store)
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
    journal = M6OutboxDeliveryJournalV1(journal_path, subject)
    return M6OutboxDeliveryPortV1(subject, store, journal)


def test_given_foreign_subject_when_reopening_delivery_journal_then_fail_closed(
    tmp_path: Path,
) -> None:
    subject = _subject()
    store = M6DurableLedgerStoreV1.create(
        tmp_path / "ledger",
        subject,
        initial_application_state_v1(subject),
    )
    journal = M6OutboxDeliveryJournalV1.create_for_store(store)
    foreign_subject = replace(subject, deployment=_root(1_899))

    with pytest.raises(M6OutboxDeliveryJournalError, match="subject mismatch"):
        M6OutboxDeliveryJournalV1(journal.root, foreign_subject)


def test_given_unbound_journal_path_when_constructing_port_then_rejects(
    tmp_path: Path,
) -> None:
    subject, store, _ = _withdrawal_store(tmp_path)
    other_store = M6DurableLedgerStoreV1.create(
        tmp_path / "other-ledger",
        subject,
        initial_application_state_v1(subject),
    )
    unbound = M6OutboxDeliveryJournalV1.create_for_store(other_store)

    with pytest.raises(ValueError, match="path is not bound"):
        M6OutboxDeliveryPortV1(subject, store, unbound)


def test_given_store_subclass_when_initializing_journal_then_override_is_not_invoked(
    tmp_path: Path,
) -> None:
    """Only the owned durable-store implementation can supply ledger truth."""

    subject = _subject()
    store = M6DurableLedgerStoreV1.create(
        tmp_path / "ledger",
        subject,
        initial_application_state_v1(subject),
    )
    hostile = _HostileStoreSubclass(store.root, subject)

    with pytest.raises(TypeError, match="requires an M6 durable ledger") as caught:
        M6OutboxDeliveryJournalV1.create_for_store(hostile)

    assert "credential" not in str(caught.value)


def test_given_adapter_subclasses_when_constructing_port_then_no_override_is_invoked(
    tmp_path: Path,
) -> None:
    """Caller-controlled adapters cannot impersonate owned shell types."""

    subject, store, _effect_id = _withdrawal_store(tmp_path)
    journal = M6OutboxDeliveryJournalV1(
        m6_outbox_delivery_journal_path_v1(store),
        subject,
    )
    hostile_store = _HostileStoreSubclass(store.root, subject)
    hostile_journal = object.__new__(_HostileJournalSubclass)

    with pytest.raises(TypeError, match="source must be") as store_error:
        M6OutboxDeliveryPortV1(subject, hostile_store, journal)
    with pytest.raises(TypeError, match="journal is not typed") as journal_error:
        M6OutboxDeliveryPortV1(subject, store, hostile_journal)

    assert "credential" not in str(store_error.value)
    assert "credential" not in str(journal_error.value)


def test_given_no_committed_outbox_when_delivering_then_transport_is_never_called(tmp_path: Path) -> None:
    subject = _subject()
    store = M6DurableLedgerStoreV1.create(
        tmp_path / "ledger", subject, initial_application_state_v1(subject)
    )
    M6OutboxDeliveryJournalV1.create_for_store(store)
    transport = _StableReceiptTransport([])
    before_state = store.reopen()
    journal_root = m6_outbox_delivery_journal_path_v1(store)
    before_files = {
        path.relative_to(journal_root): path.read_bytes()
        for path in journal_root.rglob("*")
        if path.is_file()
    }

    result = _delivery_port(tmp_path, subject, store).deliver("missing-effect", transport)

    assert result.status is M6OutboxDeliveryStatusV1.NOT_COMMITTED
    assert result.reason == "no committed outbox row matches effect id"
    assert transport.calls == []
    assert store.reopen() == before_state
    assert {
        path.relative_to(journal_root): path.read_bytes()
        for path in journal_root.rglob("*")
        if path.is_file()
    } == before_files


@pytest.mark.parametrize("effect_id", ["bad id", "snowman-☃", "x" * 129])
def test_given_malformed_effect_id_when_delivering_then_typed_reject_without_transport(
    tmp_path: Path,
    effect_id: str,
) -> None:
    subject, store, _ = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    before_state = store.reopen()
    journal_root = m6_outbox_delivery_journal_path_v1(store)
    before_files = {
        path.relative_to(journal_root): path.read_bytes()
        for path in journal_root.rglob("*")
        if path.is_file()
    }

    result = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    assert result.status is M6OutboxDeliveryStatusV1.REJECTED
    assert result.effect_id is None
    assert result.reason == "effect id is malformed"
    assert transport.calls == []
    assert store.reopen() == before_state
    assert {
        path.relative_to(journal_root): path.read_bytes()
        for path in journal_root.rglob("*")
        if path.is_file()
    } == before_files


def test_given_effect_id_subclass_when_delivering_then_override_is_not_invoked(
    tmp_path: Path,
) -> None:
    """The public effect coordinate is observed only as an exact string."""

    subject, store, _ = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])

    result = _delivery_port(tmp_path, subject, store).deliver(
        _ExplodingText("delivery-1"),
        transport,
    )

    assert result.status is M6OutboxDeliveryStatusV1.REJECTED
    assert result.reason == "effect id is malformed"
    assert "credential" not in result.reason
    assert transport.calls == []


def test_given_hostile_transport_lookup_when_delivering_then_error_is_stable(
    tmp_path: Path,
) -> None:
    """Adapter attribute failures cannot disclose provider exception details."""

    subject, store, effect_id = _withdrawal_store(tmp_path)

    result = _delivery_port(tmp_path, subject, store).deliver(
        effect_id,
        _HostileTransportLookup(),  # type: ignore[arg-type]
    )

    assert result.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert result.reason == "Tau transport interface cannot be observed"
    assert "credential" not in result.reason


def test_given_effectful_transport_lookup_when_retried_then_lookup_runs_only_after_reservation(
    tmp_path: Path,
) -> None:
    """RIPR: interface observation cannot mint fresh retry authority."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _EffectfulTransportLookup([])
    port = _delivery_port(tmp_path, subject, store)

    first = port.deliver(effect_id, transport)
    second = port.deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert first.reason == "Tau transport interface cannot be observed"
    assert second.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert transport.applications == ["lookup-effect"]


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


def test_given_hostile_receipt_scalar_when_delivered_then_no_false_success_is_recorded(
    tmp_path: Path,
) -> None:
    """Exact primitive receipt fields prevent attacker-controlled equality."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _HostileReceiptTransport([])

    result = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    assert result.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert transport.calls == [effect_id]


def test_given_receipt_subclass_when_delivered_then_provider_code_is_not_executed(
    tmp_path: Path,
) -> None:
    """A caller-controlled subclass is not an owned transport receipt type."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _HostileReceiptSubclassTransport([])

    result = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    assert result.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert result.reason == (
        "Tau transport outcome lacks an owned receipt; reconciliation required"
    )
    assert "credential" not in result.reason
    assert transport.calls == [effect_id]


@pytest.mark.parametrize(
    "transport_type",
    (_MutatingRequestTransport, _MutatingReceiptTransport),
)
def test_given_transport_mutates_callback_data_when_retried_then_original_effect_stays_quarantined(
    tmp_path: Path,
    transport_type: type[_MutatingRequestTransport] | type[_MutatingReceiptTransport],
) -> None:
    """RIPR: provider aliases cannot redefine receipt-binding expectations."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    original_effect = store.reopen().records[0].outbox_atoms[0]
    transport = transport_type([])
    port = _delivery_port(tmp_path, subject, store)

    first = port.deliver(effect_id, transport)
    second = port.deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert second.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert transport.calls == [effect_id]
    assert store.reopen().records[0].outbox_atoms[0] == original_effect
    assert "PRIVATE" not in (first.reason or "")


def test_transport_receives_detached_delivery_request_type(tmp_path: Path) -> None:
    """The imperative shell exposes a DTO rather than committed state storage."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    observed_types: list[type[object]] = []

    class RecordingTransport(_StableReceiptTransport):
        def deliver(self, effect: Any) -> Any:
            observed_types.append(type(effect))
            return super().deliver(effect)

    result = _delivery_port(tmp_path, subject, store).deliver(
        effect_id,
        RecordingTransport([]),
    )

    assert result.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert observed_types == [TauWithdrawalDeliveryRequestV1]


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


def test_given_hostile_prepare_callback_when_delivered_then_prepare_has_no_authority_or_execution(
    tmp_path: Path,
) -> None:
    """The removed advisory phase cannot execute provider-controlled effects."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _EffectfulPrepareRefusalTransport([])
    port = _delivery_port(tmp_path, subject, store)

    first = port.deliver(effect_id, transport)
    second = port.deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert second.status is M6OutboxDeliveryStatusV1.ALREADY_DELIVERED
    assert transport.applications == [effect_id]


def test_given_transport_reenters_ledger_when_delivering_then_it_completes_without_deadlock(
    tmp_path: Path,
) -> None:
    """External callbacks execute without holding the ledger publication lock."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    observed_roots: list[str] = []
    transport = _ReentrantLedgerTransport(store, observed_roots)
    results: list[M6OutboxDeliveryResultV1] = []
    worker = Thread(
        target=lambda: results.append(
            _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)
        ),
        daemon=True,
    )

    worker.start()
    worker.join(5)

    assert not worker.is_alive()
    assert len(results) == 1
    assert results[0].status is M6OutboxDeliveryStatusV1.DELIVERED
    assert observed_roots == [store.reopen().state.state_root]


def test_given_transport_reenters_same_effect_when_delivering_then_it_fails_typed_without_deadlock(
    tmp_path: Path,
) -> None:
    """A callback through the same port cannot wait on either local lock."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    inner_results: list[M6OutboxDeliveryResultV1] = []
    port: M6OutboxDeliveryPortV1

    class ReentrantEffectTransport:
        def deliver(self, effect: Any) -> TauWithdrawalDeliveryReceiptV1:
            inner_results.append(port.deliver(effect.effect_id, _StableReceiptTransport([])))
            return TauWithdrawalDeliveryReceiptV1(
                effect_id=effect.effect_id,
                tau_receipt_root=_root(708),
                source_state_root=effect.source_state_root,
                destination=effect.destination,
                asset=effect.asset,
                amount_atoms=effect.amount_atoms,
            )

    port = _delivery_port(tmp_path, subject, store)
    results: list[M6OutboxDeliveryResultV1] = []
    worker = Thread(
        target=lambda: results.append(
            port.deliver(
                effect_id,
                ReentrantEffectTransport(),
            )
        ),
        daemon=True,
    )
    worker.start()
    worker.join(5)

    assert not worker.is_alive()
    assert results[0].status is M6OutboxDeliveryStatusV1.DELIVERED
    assert inner_results[0].status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert inner_results[0].reason == "durable ledger submit guard failed"


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

    assert failed.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert retried.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert len(transport.calls) == (1 if failure_mode == "malformed" else 0)


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


def test_given_unknown_outcome_and_lost_journal_when_reinitialized_then_redelivery_stays_blocked(
    tmp_path: Path,
) -> None:
    """A missing journal after submission must never restore retry authority."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([], unexpected=True)
    first = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)
    assert first.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN

    journal_path = m6_outbox_delivery_journal_path_v1(store)
    shutil.rmtree(journal_path)
    transport.unexpected = False

    with pytest.raises(M6OutboxDeliveryJournalError, match="before the first committed block"):
        M6OutboxDeliveryJournalV1.create_for_store(store)

    assert transport.calls == [effect_id]


@pytest.mark.parametrize(
    ("initial_mode", "first_status", "initial_calls"),
    (
        ("pending", M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN, 1),
        ("unavailable", M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN, 0),
        ("delivered", M6OutboxDeliveryStatusV1.DELIVERED, 1),
    ),
)
def test_given_reserved_attempt_record_loss_when_reopened_then_redelivery_authority_is_not_recreated(
    tmp_path: Path,
    initial_mode: str,
    first_status: M6OutboxDeliveryStatusV1,
    initial_calls: int,
) -> None:
    """Losing any known attempt must fail closed while its anchor remains."""

    # Arrange: one effect has crossed a meaningful attempt-state boundary.
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport(
        [],
        unexpected=initial_mode == "pending",
        fail=initial_mode == "unavailable",
    )
    port = _delivery_port(tmp_path, subject, store)
    first = port.deliver(effect_id, transport)
    assert first.status is first_status
    assert len(transport.calls) == initial_calls
    attempts = tuple(
        (m6_outbox_delivery_journal_path_v1(store) / "attempts").glob("*.json")
    )
    assert len(attempts) == 1

    # Act: model isolated record loss while retaining the journal metadata.
    attempts[0].unlink()
    transport.unexpected = False
    transport.fail = False
    retried = port.deliver(effect_id, transport)

    # Assert: the missing record is corruption, never a fresh retry grant.
    assert retried.status is M6OutboxDeliveryStatusV1.REJECTED
    assert retried.reason == "durable delivery journal validation failed"
    assert len(transport.calls) == initial_calls


def test_given_stale_attempt_record_when_manifest_is_newer_then_redelivery_authority_is_not_recreated(
    tmp_path: Path,
) -> None:
    """An older valid attempt cannot replace the manifest-bound terminal state."""

    # Arrange: retain valid PENDING bytes, then progress the effect to DELIVERED.
    subject, store, effect_id = _withdrawal_store(tmp_path)
    journal_path = m6_outbox_delivery_journal_path_v1(store)
    stale_attempts: list[bytes] = []

    class CapturePendingTransport(_StableReceiptTransport):
        def deliver(self, effect: Any) -> Any:
            attempt_path = next((journal_path / "attempts").glob("*.json"))
            stale_attempts.append(attempt_path.read_bytes())
            return super().deliver(effect)

    transport = CapturePendingTransport([])
    port = _delivery_port(tmp_path, subject, store)
    delivered = port.deliver(effect_id, transport)
    assert delivered.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert len(stale_attempts) == 1
    attempt_path = next(
        (journal_path / "attempts").glob("*.json")
    )

    # Act: roll back only the attempt while retaining the newer manifest root.
    attempt_path.write_bytes(stale_attempts[0])
    retried = port.deliver(effect_id, transport)

    # Assert: canonical old bytes still fail their monotonic manifest binding.
    assert retried.status is M6OutboxDeliveryStatusV1.REJECTED
    assert retried.reason == "durable delivery journal validation failed"
    assert transport.calls == [effect_id]


def test_given_manifest_persistence_response_loss_when_retried_then_submission_stays_quarantined(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An uncertain manifest acknowledgment cannot produce retry authority."""

    # Arrange: inject response loss after the manifest replacement completed.
    subject, store, effect_id = _withdrawal_store(tmp_path)
    journal = M6OutboxDeliveryJournalV1(
        m6_outbox_delivery_journal_path_v1(store),
        subject,
    )
    port = M6OutboxDeliveryPortV1(subject, store, journal)
    transport = _StableReceiptTransport([])
    original_update = journal._update_attempt_manifest_unlocked

    def lose_manifest_acknowledgment(path: Path, attempt: object) -> None:
        original_update(path, attempt)  # type: ignore[arg-type]
        raise M6OutboxDeliveryJournalError("simulated manifest persistence response loss")

    monkeypatch.setattr(
        journal,
        "_update_attempt_manifest_unlocked",
        lose_manifest_acknowledgment,
    )

    # Act: reserve sees an error after both PENDING artifacts were installed.
    first = port.deliver(effect_id, transport)
    monkeypatch.setattr(
        journal,
        "_update_attempt_manifest_unlocked",
        original_update,
    )
    retried = M6OutboxDeliveryPortV1(subject, store, journal).deliver(
        effect_id,
        transport,
    )

    # Assert: no transport call occurred, and the durable PENDING state blocks retry.
    assert first.status is M6OutboxDeliveryStatusV1.REJECTED
    assert first.reason == "durable delivery journal validation failed"
    assert retried.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert transport.calls == []


def test_given_post_submit_fsync_failure_then_result_is_typed_unknown_and_retry_is_quarantined(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Every filesystem failure after submission remains a typed quarantine."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    real_fsync = os.fsync

    def fail_after_submit(descriptor: int) -> None:
        if transport.calls:
            raise OSError("private disk failure after external submission")
        real_fsync(descriptor)

    monkeypatch.setattr(journal_module.os, "fsync", fail_after_submit)
    first = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)
    monkeypatch.setattr(journal_module.os, "fsync", real_fsync)
    second = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert first.reason == "Tau delivery receipt could not be persisted"
    assert "private" not in first.reason
    assert second.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert transport.calls == [effect_id]


def test_given_float_corrupts_pending_attempt_after_submit_then_result_is_typed_unknown(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """RIPR: canonical re-encoding failures stay inside the journal algebra."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    port = _delivery_port(tmp_path, subject, store)
    journal = port._journal
    original_mark_delivered = journal.mark_delivered

    def corrupt_then_mark(**kwargs: object):
        journal._attempt_path(effect_id).write_bytes(b'{"x":1.5}')
        return original_mark_delivered(**kwargs)

    monkeypatch.setattr(journal, "mark_delivered", corrupt_then_mark)

    first = port.deliver(effect_id, transport)
    second = port.deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert second.status is M6OutboxDeliveryStatusV1.REJECTED
    assert transport.calls == [effect_id]
    assert "TypeError" not in (first.reason or "")


def test_given_journal_unlock_fails_then_descriptor_is_still_closed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """RIPR: lock cleanup is deterministic even when unlock reports failure."""

    subject, store, _effect_id = _withdrawal_store(tmp_path)
    journal = _delivery_port(tmp_path, subject, store)._journal
    real_flock = journal_module.fcntl.flock
    real_close = journal_module.os.close
    closed_descriptors: list[int] = []
    failed = False

    def fail_first_unlock(descriptor: int, operation: int) -> None:
        nonlocal failed
        if not failed and operation == journal_module.fcntl.LOCK_UN:
            failed = True
            raise OSError("private unlock detail")
        real_flock(descriptor, operation)

    def record_close(descriptor: int) -> None:
        closed_descriptors.append(descriptor)
        real_close(descriptor)

    monkeypatch.setattr(journal_module.fcntl, "flock", fail_first_unlock)
    monkeypatch.setattr(journal_module.os, "close", record_close)

    with pytest.raises(
        M6OutboxDeliveryJournalError,
        match="delivery journal lock cannot be released",
    ):
        with journal._locked():
            pass

    assert failed is True
    assert len(closed_descriptors) == 1


def test_given_post_submit_lease_unlock_failure_then_result_is_typed_and_retry_is_safe(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Lease cleanup failure cannot escape after an external effect."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    real_flock = durable_store_module.fcntl.flock
    failed = False

    def fail_submission_lease_unlock(descriptor: int, operation: int) -> None:
        nonlocal failed
        target = os.readlink(f"/proc/self/fd/{descriptor}")
        if (
            not failed
            and operation == durable_store_module.fcntl.LOCK_UN
            and "/submission-leases/" in target
        ):
            failed = True
            raise OSError("private lease cleanup detail")
        real_flock(descriptor, operation)

    monkeypatch.setattr(durable_store_module.fcntl, "flock", fail_submission_lease_unlock)
    first = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)
    monkeypatch.setattr(durable_store_module.fcntl, "flock", real_flock)
    second = _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert first.reason == "durable ledger submit guard failed"
    assert "private" not in first.reason
    assert second.status is M6OutboxDeliveryStatusV1.ALREADY_DELIVERED
    assert transport.calls == [effect_id]


def test_given_lease_setup_and_cleanup_failures_when_delivering_then_no_raw_oserror_escapes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A compounded pre-submit filesystem failure remains a typed shell result."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    port = _delivery_port(tmp_path, subject, store)
    real_open = durable_store_module.os.open
    real_close = durable_store_module.os.close
    lease_setup_failed = False
    close_failed = False

    def fail_lease_open(
        path: object,
        flags: int,
        mode: int = 0o777,
        *,
        dir_fd: int | None = None,
    ) -> int:
        nonlocal lease_setup_failed
        if (
            dir_fd is not None
            and isinstance(path, str)
            and len(path) == 69
            and path.endswith(".lock")
        ):
            lease_setup_failed = True
            raise OSError("private lease open detail")
        return real_open(path, flags, mode, dir_fd=dir_fd)  # type: ignore[arg-type]

    def fail_first_setup_close(descriptor: int) -> None:
        nonlocal close_failed
        real_close(descriptor)
        if lease_setup_failed and not close_failed:
            close_failed = True
            raise OSError("private lease close detail")

    monkeypatch.setattr(durable_store_module.os, "open", fail_lease_open)
    monkeypatch.setattr(durable_store_module.os, "close", fail_first_setup_close)

    result = port.deliver(effect_id, transport)

    assert result.status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert result.reason == "durable ledger submit guard failed"
    assert transport.calls == []


def test_given_attempt_capacity_neighbor_when_next_reservation_runs_then_it_fails_before_write(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """BVA: the maximum attempt count is accepted and its upper neighbor is not."""

    subject = _subject()
    store = M6DurableLedgerStoreV1.create(
        tmp_path / "ledger-capacity",
        subject,
        initial_application_state_v1(subject),
    )
    journal = M6OutboxDeliveryJournalV1.create_for_store(store)
    monkeypatch.setattr(journal_module, "_DELIVERY_JOURNAL_MAX_ATTEMPTS_V1", 1)
    first, reserved = journal.reserve(effect_id="effect-1", effect_root=_root(8_001))

    assert reserved is True
    assert first.effect_id == "effect-1"
    with pytest.raises(M6OutboxDeliveryJournalError, match="attempt capacity"):
        journal.reserve(effect_id="effect-2", effect_root=_root(8_002))

    reopened = M6OutboxDeliveryJournalV1(journal.root, subject)
    existing, reserved_again = reopened.reserve(
        effect_id="effect-1",
        effect_root=_root(8_001),
    )
    assert reserved_again is False
    assert existing.effect_id == "effect-1"


def test_given_ack_commits_after_delivery_snapshot_when_submit_gate_runs_then_transport_is_not_called(
    tmp_path: Path,
) -> None:
    """A terminal acknowledgment wins when it commits before submit admission."""

    class SnapshotBarrierPort(M6OutboxDeliveryPortV1):
        def __init__(self, *args: object, snapshot_seen: Event, release: Event) -> None:
            super().__init__(*args)  # type: ignore[arg-type]
            self.snapshot_seen = snapshot_seen
            self.release = release

        def _prepare_effect(self, effect_id: str) -> object:
            prepared = super()._prepare_effect(effect_id)
            self.snapshot_seen.set()
            if not self.release.wait(5):
                raise RuntimeError("test submit gate was not released")
            return prepared

    # Arrange: pause delivery immediately after its first committed snapshot.
    subject, store, effect_id = _withdrawal_store(tmp_path)
    journal = M6OutboxDeliveryJournalV1(
        m6_outbox_delivery_journal_path_v1(store),
        subject,
    )
    snapshot_seen = Event()
    release = Event()
    port = SnapshotBarrierPort(
        subject,
        store,
        journal,
        snapshot_seen=snapshot_seen,
        release=release,
    )
    transport = _StableReceiptTransport([])
    results: list[M6OutboxDeliveryResultV1] = []
    worker = Thread(target=lambda: results.append(port.deliver(effect_id, transport)))
    worker.start()
    assert snapshot_seen.wait(5)

    # Act: commit a provenance-bound acknowledgment before submit admission.
    pending = store.reopen().state
    acknowledgment = GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        command_id=_root(1_911),
        sender="alice",
        nonce=2,
        payload={
            "withdrawal_id": effect_id,
            "ack_root": _root(1_912),
            "tau_receipt_root": _root(1_913),
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
    finality, tau = _finality_and_tau(subject, acknowledged, "delivery-race-ack-batch")
    committed = store.publish(acknowledged, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED
    release.set()
    worker.join(5)

    # Assert: submit admission observes the terminal state and touches no rail.
    assert not worker.is_alive()
    assert len(results) == 1
    assert results[0].status is M6OutboxDeliveryStatusV1.ALREADY_DELIVERED
    assert results[0].receipt is not None
    assert results[0].receipt.tau_receipt_root == _root(1_913)
    assert transport.calls == []


def test_given_submission_in_flight_when_same_effect_ack_publishes_then_ack_fails_fast(
    tmp_path: Path,
) -> None:
    """The per-effect lease rejects a crossed acknowledgment without waiting."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    pending = store.reopen().state
    acknowledgment = GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        command_id=_root(8_050),
        sender="alice",
        nonce=2,
        payload={
            "withdrawal_id": effect_id,
            "ack_root": _root(8_051),
            "tau_receipt_root": _root(8_052),
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
    finality, tau = _finality_and_tau(subject, acknowledged, "in-flight-ack-batch")
    transport = _BlockingReceiptTransport([], Event(), Event())
    delivery_results: list[M6OutboxDeliveryResultV1] = []
    commit_results: list[object] = []

    delivery_worker = Thread(
        target=lambda: delivery_results.append(
            _delivery_port(tmp_path, subject, store).deliver(effect_id, transport)
        ),
        daemon=True,
    )

    def publish_acknowledgment() -> None:
        commit_results.append(store.publish(acknowledged, finality, tau))

    commit_worker = Thread(target=publish_acknowledgment, daemon=True)
    delivery_worker.start()
    assert transport.entered.wait(5)
    commit_worker.start()

    # Unrelated reads and the crossed acknowledgment both complete without
    # waiting on an external callback.
    assert store.reopen().state.state_root == pending.state_root
    commit_worker.join(5)
    assert not commit_worker.is_alive()
    assert len(commit_results) == 1
    assert commit_results[0].status is CommitStatusV1.FINALITY_REJECTED  # type: ignore[union-attr]
    assert commit_results[0].reason == "external effect submission is already in progress"  # type: ignore[union-attr]
    transport.release.set()
    delivery_worker.join(5)

    assert not delivery_worker.is_alive()
    assert delivery_results[0].status is M6OutboxDeliveryStatusV1.DELIVERED
    retry = store.publish(acknowledged, finality, tau)
    assert retry.status is CommitStatusV1.COMMITTED
    assert transport.calls == [effect_id]


@pytest.mark.parametrize("publication_mode", ("direct", "direct_batch", "zrpf"))
def test_given_ack_publish_cleanup_fails_after_commit_then_result_is_terminal(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    publication_mode: str,
) -> None:
    """Stateful RIPR: post-commit shell cleanup cannot erase commit observability."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    pending = store.reopen().state
    acknowledgment = GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        command_id=_root(8_053),
        sender="alice",
        nonce=2,
        payload={
            "withdrawal_id": effect_id,
            "ack_root": _root(8_054),
            "tau_receipt_root": _root(8_055),
        },
    )
    contexts = []
    commands = []
    current = pending
    command_count = (
        1
        if publication_mode == "direct"
        else 2
        if publication_mode == "direct_batch"
        else ZRPF_COMMAND_COUNT_V1
    )
    accepted: AcceptCandidateV1 | None = None
    for offset in range(command_count):
        command = acknowledgment if offset == 0 else _command(
            offset + 2,
            auction_id=f"cleanup-batch-{offset}",
        )
        context = (
            _with_ack_evidence(
                subject,
                current,
                acknowledgment,
                pending.withdrawals[0].source_state_root,
            )
            if offset == 0
            else _context(subject, current, offset + 2)
        )
        candidate = run_m6_transition_v1(subject, current, context, command)
        assert isinstance(candidate, AcceptCandidateV1)
        contexts.append(context)
        commands.append(command)
        current = candidate.post_state
        if offset == 0:
            accepted = candidate
    assert accepted is not None
    direct = (
        None
        if publication_mode == "direct"
        else execute_direct_batch_v1(subject, pending, tuple(contexts), tuple(commands))
    )
    verified = None
    if publication_mode == "direct":
        finality, tau = _finality_and_tau(subject, accepted, "ack-cleanup-failure")
    elif publication_mode == "direct_batch":
        assert direct is not None
        finality, tau = _finality_and_tau_for_direct_batch(subject, pending, direct)
    else:
        batch = execute_zrpf_batch_v1(subject, pending, tuple(contexts), tuple(commands))
        verified = verify_zrpf_root_v1(
            subject,
            batch,
            receipt_verifier=_TEST_ZRPF_RECEIPT_VERIFIER,
        )
        finality, tau = _zrpf_finality_and_tau(subject, pending, verified)
    real_leases = store._acknowledgment_submission_leases
    lease_round = 0

    @contextmanager
    def fail_after_second_lease(commands: tuple[GlobalCommandV1, ...]):
        nonlocal lease_round
        lease_round += 1
        with real_leases(commands) as available:
            yield available
        if lease_round == 2:
            raise M6DurableCorruptionError("external effect lease cleanup failed")

    monkeypatch.setattr(store, "_acknowledgment_submission_leases", fail_after_second_lease)

    result = (
        store.publish(accepted, finality, tau)
        if publication_mode == "direct"
        else store.publish_direct_batch(direct, finality, tau)
        if publication_mode == "direct_batch"
        else store.publish_zrpf(verified, finality, tau)
    )

    assert result.status is CommitStatusV1.ALREADY_COMMITTED
    assert result.record is not None
    assert store.reopen().records[-1] == result.record
    assert store.reopen().state.withdrawals[0].status.value == "acknowledged"


def test_given_ack_command_subclass_when_publication_reads_lease_id_then_hooks_cannot_bypass_it(
    tmp_path: Path,
) -> None:
    """The lease coordinate and replay command must come from one owned value."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    pending = store.reopen().state
    acknowledgment = GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        command_id=_root(8_055),
        sender="alice",
        nonce=2,
        payload={
            "withdrawal_id": effect_id,
            "ack_root": _root(8_056),
            "tau_receipt_root": _root(8_057),
        },
    )
    accepted = run_m6_transition_v1(
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
    assert isinstance(accepted, AcceptCandidateV1)
    finality, tau = _finality_and_tau(subject, accepted, "hostile-ack-command-batch")

    class HostileAcknowledgment(GlobalCommandV1):
        lookups = 0

        def payload_value(
            self,
            key: str,
            default: str | int | None = None,
        ) -> str | int | None:
            if key == "withdrawal_id":
                type(self).lookups += 1
                if type(self).lookups == 1:
                    return "decoy-withdrawal"
            return super().payload_value(key, default)

    hostile_command = HostileAcknowledgment(
        kind=acknowledgment.kind,
        command_id=acknowledgment.command_id,
        sender=acknowledgment.sender,
        nonce=acknowledgment.nonce,
        payload=acknowledgment.payload,
        created_height=acknowledgment.created_height,
    )
    hostile_candidate = replace(accepted, command=hostile_command)

    with store.external_effect_submission_lease(effect_id):
        with pytest.raises(TypeError, match="exact owned command"):
            store.publish(hostile_candidate, finality, tau)

    assert HostileAcknowledgment.lookups == 0
    assert store.reopen().state == pending


def test_given_ack_argument_subclass_when_publication_reads_lease_id_then_hooks_cannot_bypass_it(
    tmp_path: Path,
) -> None:
    """Nested payload values are owned before lease extraction."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    pending = store.reopen().state
    acknowledgment = GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        command_id=_root(8_058),
        sender="alice",
        nonce=2,
        payload={
            "withdrawal_id": effect_id,
            "ack_root": _root(8_059),
            "tau_receipt_root": _root(8_060),
        },
    )
    accepted = run_m6_transition_v1(
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
    assert isinstance(accepted, AcceptCandidateV1)
    finality, tau = _finality_and_tau(subject, accepted, "hostile-ack-argument-batch")

    class HostileArgument(CommandArgumentV1):
        lookups = 0

        def __getattribute__(self, name: str) -> object:
            if name == "value":
                type(self).lookups += 1
                if type(self).lookups == 1:
                    return "decoy-withdrawal"
            return super().__getattribute__(name)

    hostile_payload = tuple(
        HostileArgument(argument.key, argument.value)
        if argument.key == "withdrawal_id"
        else argument
        for argument in acknowledgment.payload
    )
    HostileArgument.lookups = 0
    object.__setattr__(accepted.command, "payload", hostile_payload)

    with store.external_effect_submission_lease(effect_id):
        with pytest.raises(TypeError, match="exact owned commands"):
            store.publish(accepted, finality, tau)

    assert HostileArgument.lookups == 0
    assert store.reopen().state == pending


@pytest.mark.parametrize("publication_mode", ("direct_batch", "zrpf"))
def test_given_submission_lease_when_batch_contains_same_effect_ack_then_batch_fails_fast(
    tmp_path: Path,
    publication_mode: str,
) -> None:
    """Every durable commit entrypoint honors the same acknowledgment lease."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    initial = store.reopen().state
    acknowledgment = GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
        command_id=_root(8_060),
        sender="alice",
        nonce=2,
        payload={
            "withdrawal_id": effect_id,
            "ack_root": _root(8_061),
            "tau_receipt_root": _root(8_062),
        },
    )
    contexts = []
    commands = []
    current = initial
    command_count = 2 if publication_mode == "direct_batch" else ZRPF_COMMAND_COUNT_V1
    for offset in range(command_count):
        command = acknowledgment if offset == 0 else _command(
            offset + 2,
            auction_id=f"lease-batch-{offset}",
        )
        context = (
            _with_ack_evidence(
                subject,
                current,
                acknowledgment,
                initial.withdrawals[0].source_state_root,
            )
            if offset == 0
            else _context(subject, current, offset + 2)
        )
        candidate = run_m6_transition_v1(subject, current, context, command)
        assert isinstance(candidate, AcceptCandidateV1)
        contexts.append(context)
        commands.append(command)
        current = candidate.post_state

    direct = execute_direct_batch_v1(subject, initial, tuple(contexts), tuple(commands))
    if publication_mode == "direct_batch":
        finality, tau = _finality_and_tau_for_direct_batch(subject, initial, direct)
    else:
        batch = execute_zrpf_batch_v1(subject, initial, tuple(contexts), tuple(commands))
        verified = verify_zrpf_root_v1(
            subject,
            batch,
            receipt_verifier=_TEST_ZRPF_RECEIPT_VERIFIER,
        )
        finality, tau = _zrpf_finality_and_tau(subject, initial, verified)

    with store.external_effect_submission_lease(effect_id):
        result = (
            store.publish_direct_batch(direct, finality, tau)
            if publication_mode == "direct_batch"
            else store.publish_zrpf(verified, finality, tau)
        )

    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason == "external effect submission is already in progress"
    assert store.reopen().state == initial


def test_given_second_ack_lease_acquisition_fails_then_first_lease_is_released_immediately(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Stateful RIPR: every partial acquisition unwinds before propagation."""

    subject = _subject()
    store = M6DurableLedgerStoreV1.create(
        tmp_path / "partial-lease-ledger",
        subject,
        initial_application_state_v1(subject),
    )
    events: list[str] = []

    @contextmanager
    def controlled_lease(effect_id: str):
        events.append(f"enter:{effect_id}")
        if effect_id == "effect-b":
            raise M6DurableCorruptionError("second lease unavailable")
        try:
            yield
        finally:
            events.append(f"exit:{effect_id}")

    commands = tuple(
        GlobalCommandV1(
            kind=GlobalCommandKindV1.TAU_WITHDRAWAL_ACK,
            command_id=_root(8_070 + index),
            sender="alice",
            nonce=index,
            payload={
                "withdrawal_id": effect_id,
                "ack_root": _root(8_080 + index),
                "tau_receipt_root": _root(8_090 + index),
            },
        )
        for index, effect_id in enumerate(("effect-a", "effect-b"), start=1)
    )
    monkeypatch.setattr(store, "external_effect_submission_lease", controlled_lease)

    retained_traceback = None
    with pytest.raises(M6DurableCorruptionError, match="second lease unavailable"):
        try:
            with store._acknowledgment_submission_leases(commands):
                raise AssertionError("all leases unexpectedly acquired")
        except M6DurableCorruptionError:
            retained_traceback = sys.exc_info()[2]
            assert events == ["enter:effect-a", "enter:effect-b", "exit:effect-a"]
            raise

    assert retained_traceback is not None


def test_given_journal_creation_holds_genesis_guard_when_publish_races_then_publish_waits(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Journal initialization and the first publication have one linear order."""

    subject = _subject()
    initial = replace(
        initial_application_state_v1(subject),
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 10),
        ),
    )
    store = M6DurableLedgerStoreV1.create(
        tmp_path / "ledger-create-race",
        subject,
        initial,
        finality_verifier=_TEST_FINALITY_VERIFIER,
    )
    command = GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL,
        command_id=_root(8_100),
        sender="alice",
        nonce=1,
        payload={
            "withdrawal_id": "creation-race-effect",
            "asset": "A",
            "amount_atoms": 1,
            "destination": "tau-alice",
        },
    )
    candidate = run_m6_transition_v1(
        subject,
        initial,
        _context(subject, initial, 1),
        command,
    )
    assert isinstance(candidate, AcceptCandidateV1)
    finality, tau = _finality_and_tau(subject, candidate, "journal-create-race")
    entered = Event()
    release = Event()
    publish_done = Event()
    journals: list[M6OutboxDeliveryJournalV1] = []
    commits: list[object] = []
    original_write = journal_module._write_new_durable_file

    def paused_first_write(path: Path, data: bytes) -> None:
        if path.name == "journal.json":
            entered.set()
            if not release.wait(5):
                raise RuntimeError("journal creation release was not signaled")
        original_write(path, data)

    monkeypatch.setattr(journal_module, "_write_new_durable_file", paused_first_write)
    create_worker = Thread(
        target=lambda: journals.append(M6OutboxDeliveryJournalV1.create_for_store(store)),
        daemon=True,
    )

    def publish() -> None:
        commits.append(store.publish(candidate, finality, tau))
        publish_done.set()

    publish_worker = Thread(target=publish, daemon=True)
    create_worker.start()
    assert entered.wait(5)
    publish_worker.start()
    assert publish_done.wait(0.2) is False
    release.set()
    create_worker.join(5)
    publish_worker.join(5)

    assert not create_worker.is_alive()
    assert not publish_worker.is_alive()
    assert len(journals) == 1
    assert len(commits) == 1
    assert commits[0].status is CommitStatusV1.COMMITTED  # type: ignore[union-attr]


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


def test_given_concurrent_ports_when_one_submission_is_in_flight_then_second_is_quarantined(
    tmp_path: Path,
) -> None:
    """The effect lease fails fast and permits only one transport call."""

    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _BlockingReceiptTransport([], Event(), Event())
    first_results: list[M6OutboxDeliveryResultV1] = []
    second_results: list[M6OutboxDeliveryResultV1] = []
    first_port = _delivery_port(tmp_path, subject, store)
    second_port = _delivery_port(tmp_path, subject, store)
    first_worker = Thread(
        target=lambda: first_results.append(first_port.deliver(effect_id, transport)),
        daemon=True,
    )
    second_worker = Thread(
        target=lambda: second_results.append(second_port.deliver(effect_id, transport)),
        daemon=True,
    )

    first_worker.start()
    assert transport.entered.wait(5)
    second_worker.start()
    second_worker.join(5)
    assert not second_worker.is_alive()
    transport.release.set()
    first_worker.join(5)

    assert not first_worker.is_alive()
    assert len(first_results) == 1
    assert len(second_results) == 1
    assert first_results[0].status is M6OutboxDeliveryStatusV1.DELIVERED
    assert second_results[0].status is M6OutboxDeliveryStatusV1.OUTCOME_UNKNOWN
    assert second_results[0].reason == "durable ledger submit guard failed"
    assert transport.calls == [effect_id]
