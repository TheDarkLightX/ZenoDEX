from __future__ import annotations

from dataclasses import dataclass, replace
from pathlib import Path
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
    M6OutboxDeliveryPortV1,
    M6OutboxDeliveryResultV1,
    M6OutboxDeliveryStatusV1,
    M6TauTransportError,
    TauWithdrawalDeliveryReceiptV1,
)
from tests.integration.test_m6_durable_store_v1 import (
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

    def deliver(self, effect: Any) -> Any:
        self.calls.append(getattr(effect, "effect_id", "invalid"))
        if self.fail:
            raise M6TauTransportError("Tau unavailable")
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


def _withdrawal_store(tmp_path: Path) -> tuple[M6PromotionSubjectV1, M6DurableLedgerStoreV1, str]:
    subject = _subject()
    initial = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 10),),
    )
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
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


def test_given_no_committed_outbox_when_delivering_then_transport_is_never_called(tmp_path: Path) -> None:
    subject = _subject()
    store = M6DurableLedgerStoreV1.create(
        tmp_path / "ledger", subject, initial_application_state_v1(subject)
    )
    transport = _StableReceiptTransport([])

    result = M6OutboxDeliveryPortV1(subject, store).deliver("missing-effect", transport)

    assert result.status is M6OutboxDeliveryStatusV1.NOT_COMMITTED
    assert transport.calls == []


@pytest.mark.parametrize("effect_id", ["bad id", "snowman-☃", "x" * 129])
def test_given_malformed_effect_id_when_delivering_then_typed_reject_without_transport(
    tmp_path: Path,
    effect_id: str,
) -> None:
    subject, store, _ = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])

    result = M6OutboxDeliveryPortV1(subject, store).deliver(effect_id, transport)

    assert result.status is M6OutboxDeliveryStatusV1.REJECTED
    assert result.effect_id is None
    assert result.reason == "effect id is malformed"
    assert transport.calls == []


def test_given_committed_withdrawal_when_retried_then_one_process_delivery_is_idempotent(
    tmp_path: Path,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    port = M6OutboxDeliveryPortV1(subject, store)

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

    result = M6OutboxDeliveryPortV1(subject, store).deliver(effect_id, transport)

    after = store.reopen()
    assert result.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert after == before


def test_given_cached_delivery_when_reopen_fails_then_cache_cannot_bypass_canonical_source(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    port = M6OutboxDeliveryPortV1(subject, store)
    first = port.deliver(effect_id, transport)

    def fail_reopen() -> object:
        raise M6DurableCorruptionError("reopen failed")

    monkeypatch.setattr(store, "reopen", fail_reopen)
    second = port.deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert second.status is M6OutboxDeliveryStatusV1.REJECTED
    assert transport.calls == [effect_id]


def test_given_mismatched_transport_receipt_when_retried_then_no_false_success_is_cached(
    tmp_path: Path,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([], tamper=True)
    port = M6OutboxDeliveryPortV1(subject, store)

    rejected = port.deliver(effect_id, transport)
    transport.tamper = False
    retried = port.deliver(effect_id, transport)

    assert rejected.status is M6OutboxDeliveryStatusV1.REJECTED
    assert retried.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert transport.calls == [effect_id, effect_id]


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


def test_given_process_restart_when_redelivering_then_same_effect_identity_reaches_transport(
    tmp_path: Path,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport([])
    first = M6OutboxDeliveryPortV1(subject, store).deliver(effect_id, transport)

    second = M6OutboxDeliveryPortV1(subject, store).deliver(effect_id, transport)

    assert first.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert second.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert second.receipt == first.receipt
    assert transport.calls == [effect_id, effect_id]


@pytest.mark.parametrize("failure_mode", ["malformed", "unavailable"])
def test_given_delivery_failure_when_retried_then_no_false_success_is_cached(
    tmp_path: Path,
    failure_mode: str,
) -> None:
    subject, store, effect_id = _withdrawal_store(tmp_path)
    transport = _StableReceiptTransport(
        [], malformed=failure_mode == "malformed", fail=failure_mode == "unavailable"
    )
    port = M6OutboxDeliveryPortV1(subject, store)

    failed = port.deliver(effect_id, transport)
    transport.malformed = False
    transport.fail = False
    retried = port.deliver(effect_id, transport)

    expected_failure = (
        M6OutboxDeliveryStatusV1.REJECTED
        if failure_mode == "malformed"
        else M6OutboxDeliveryStatusV1.RETRYABLE_FAILURE
    )
    assert failed.status is expected_failure
    assert retried.status is M6OutboxDeliveryStatusV1.DELIVERED
    assert len(transport.calls) == 2
