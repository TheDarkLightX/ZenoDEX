"""Committed response loss is distinct from a rejected economic transition."""

from __future__ import annotations

import sqlite3
from pathlib import Path

import pytest

from src.integration.global_economic_durable_publisher_v1 import (
    GlobalEconomicPublicationIndeterminateV1,
    VerifiedDurableEconomicPublisherV1,
)
from src.integration.global_economic_epoch_journal_v1 import (
    DurableEconomicEpochCommitStatusV1,
    GlobalEconomicEpochJournalV1,
    _DurableEconomicEpochCommitFaultV1,
    _SimulatedDurableEconomicEpochCrashV1,
)
from tests.integration.publisher_receipt_port_fixtures_v1 import (
    publisher_raw_evidence_v1,
)
from tests.integration.publisher_receipt_port_fixtures_v1 import (
    simulated_measured_publisher_crypto_v1 as simulated_measured_publisher_crypto_v1,
)
from tests.integration.test_global_economic_durable_publisher_v1 import (
    _bound_receipt_verifier_v1,
    _publisher_fixture_v1,
)

pytestmark = pytest.mark.usefixtures("simulated_measured_publisher_crypto_v1")


def _logical_store(path: Path) -> tuple[tuple[tuple[object, ...], ...], ...]:
    """Read complete economic rows independently of publisher outcome decoding."""

    with sqlite3.connect(path) as connection:
        connection.execute("BEGIN")
        return tuple(tuple(connection.execute(query).fetchall()) for query in (
            "SELECT * FROM metadata ORDER BY singleton",
            "SELECT * FROM current_head ORDER BY singleton",
            "SELECT * FROM economic_epochs ORDER BY publication_id",
        ))


@pytest.mark.parametrize("fault", tuple(_DurableEconomicEpochCommitFaultV1))
def test_given_journal_fault_then_precommit_is_noop_and_postcommit_is_indeterminate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
    fault: _DurableEconomicEpochCommitFaultV1,
) -> None:
    # Given a verified isolated transfer and an independently observed PRE store.
    admission, candidate, body = _publisher_fixture_v1()
    path = tmp_path / "outcomes.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _bound_receipt_verifier_v1(candidate)[0],
    )
    source = publisher.head
    before = _logical_store(path)

    def commit_with_fault(journal, epoch, cas_token, write_capability):
        return journal._commit_epoch_with_fault_for_test_v1(
            epoch, cas_token, fault, write_capability,
        )

    committed = fault is _DurableEconomicEpochCommitFaultV1.AFTER_COMMIT_BEFORE_ACK
    expected_error = (
        GlobalEconomicPublicationIndeterminateV1 if committed
        else _SimulatedDurableEconomicEpochCrashV1
    )
    # When SQLite fails at a declared transaction boundary.
    with monkeypatch.context() as patch:
        patch.setattr(GlobalEconomicEpochJournalV1,
                      "_commit_epoch_from_verified_publisher_v1", commit_with_fault)
        with pytest.raises(expected_error):
            publisher.publish_economic_epoch(
                expected_source=source, candidate=candidate, body_and_state=body,
                raw_evidence=publisher_raw_evidence_v1(candidate),
            )
    after_failure = _logical_store(path)
    # Then PRE faults leave every row unchanged; POST faults retain one full epoch.
    if committed:
        assert len(after_failure[2]) == 1
        assert publisher.head.sequence == 1
    else:
        assert after_failure == before
        assert publisher.head == source
    publisher.close()
    # A fresh authorized open resolves uncertainty through an exact retry.
    reopened = VerifiedDurableEconomicPublisherV1.open(
        path, admission, _bound_receipt_verifier_v1(candidate)[0],
    )
    outcome = reopened.publish_economic_epoch(
        expected_source=source, candidate=candidate, body_and_state=body,
        raw_evidence=publisher_raw_evidence_v1(candidate),
    )
    assert outcome.status is (
        DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED if committed
        else DurableEconomicEpochCommitStatusV1.COMMITTED
    )
    assert len(_logical_store(path)[2]) == 1
    if committed:
        assert _logical_store(path) == after_failure
    reopened.close()


def test_given_committed_epoch_then_failed_response_projection_is_indeterminate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    admission, candidate, body = _publisher_fixture_v1()
    path = tmp_path / "response.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _bound_receipt_verifier_v1(candidate)[0],
    )
    source = publisher.head

    def response_unavailable(*_args):
        raise OSError("response unavailable")

    with monkeypatch.context() as patch:
        patch.setattr(VerifiedDurableEconomicPublisherV1, "_outcome_v1",
                      staticmethod(response_unavailable))
        with pytest.raises(GlobalEconomicPublicationIndeterminateV1):
            publisher.publish_economic_epoch(
                expected_source=source, candidate=candidate, body_and_state=body,
                raw_evidence=publisher_raw_evidence_v1(candidate),
            )
    committed = _logical_store(path)
    assert len(committed[2]) == 1
    retried = publisher.publish_economic_epoch(
        expected_source=source, candidate=candidate, body_and_state=body,
        raw_evidence=publisher_raw_evidence_v1(candidate),
    )
    assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert _logical_store(path) == committed
    publisher.close()


@pytest.mark.parametrize("commit_first", (False, True))
def test_given_failed_attempt_and_unreadable_history_then_outcome_is_indeterminate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, commit_first: bool,
) -> None:
    admission, candidate, body = _publisher_fixture_v1()
    path = tmp_path / "unreadable.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _bound_receipt_verifier_v1(candidate)[0],
    )
    source = publisher.head
    before = _logical_store(path)
    fault = (
        _DurableEconomicEpochCommitFaultV1.AFTER_COMMIT_BEFORE_ACK if commit_first
        else _DurableEconomicEpochCommitFaultV1.AFTER_INSERT
    )

    def fail_attempt(journal, epoch, cas_token, write_capability):
        return journal._commit_epoch_with_fault_for_test_v1(
            epoch, cas_token, fault, write_capability,
        )

    def history_unavailable(*_args):
        raise OSError("history unavailable")

    with monkeypatch.context() as patch:
        patch.setattr(GlobalEconomicEpochJournalV1,
                      "_commit_epoch_from_verified_publisher_v1", fail_attempt)
        patch.setattr(GlobalEconomicEpochJournalV1,
                      "_contains_exact_epoch_for_verified_publisher_v1", history_unavailable)
        with pytest.raises(GlobalEconomicPublicationIndeterminateV1,
                           match="cannot be observed") as caught:
            publisher.publish_economic_epoch(
                expected_source=source, candidate=candidate, body_and_state=body,
                raw_evidence=publisher_raw_evidence_v1(candidate),
            )
    assert isinstance(caught.value.__cause__, OSError)
    if commit_first:
        assert len(_logical_store(path)[2]) == 1
    else:
        assert _logical_store(path) == before
    publisher.close()


def test_given_other_winner_then_failed_stale_attempt_is_not_attributed_its_commit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    admission, candidate, body = _publisher_fixture_v1(receipt_bytes=b"alice")
    _, bob_candidate, bob_body = _publisher_fixture_v1(receipt_bytes=b"bob")
    path = tmp_path / "winner.sqlite"
    alice = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _bound_receipt_verifier_v1(candidate)[0],
    )
    bob = VerifiedDurableEconomicPublisherV1.open(
        path, admission, _bound_receipt_verifier_v1(bob_candidate)[0],
    )
    source = alice.head
    winner = bob.publish_economic_epoch(
        expected_source=source, candidate=bob_candidate, body_and_state=bob_body,
        raw_evidence=publisher_raw_evidence_v1(bob_candidate),
    )
    assert winner.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    winner_rows = _logical_store(path)

    def failed_stale_response(outcome, _published):
        assert outcome.status is DurableEconomicEpochCommitStatusV1.STALE_HEAD
        raise OSError("stale response unavailable")

    with monkeypatch.context() as patch:
        patch.setattr(VerifiedDurableEconomicPublisherV1, "_outcome_v1",
                      staticmethod(failed_stale_response))
        with pytest.raises(OSError, match="stale response unavailable"):
            alice.publish_economic_epoch(
                expected_source=source, candidate=candidate, body_and_state=body,
                raw_evidence=publisher_raw_evidence_v1(candidate),
            )
    assert _logical_store(path) == winner_rows
    alice.close()
    bob.close()


def test_given_postcommit_interrupt_then_control_flow_is_preserved_and_retry_is_exact(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    admission, candidate, body = _publisher_fixture_v1()
    path = tmp_path / "interrupt.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _bound_receipt_verifier_v1(candidate)[0],
    )
    source = publisher.head
    original = GlobalEconomicEpochJournalV1._commit_epoch_from_verified_publisher_v1

    def interrupt_after_commit(*args):
        original(*args)
        raise KeyboardInterrupt("interrupted")

    with monkeypatch.context() as patch:
        patch.setattr(GlobalEconomicEpochJournalV1,
                      "_commit_epoch_from_verified_publisher_v1", interrupt_after_commit)
        with pytest.raises(KeyboardInterrupt, match="interrupted"):
            publisher.publish_economic_epoch(
                expected_source=source, candidate=candidate, body_and_state=body,
                raw_evidence=publisher_raw_evidence_v1(candidate),
            )
    committed = _logical_store(path)
    assert len(committed[2]) == 1
    retried = publisher.publish_economic_epoch(
        expected_source=source, candidate=candidate, body_and_state=body,
        raw_evidence=publisher_raw_evidence_v1(candidate),
    )
    assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert _logical_store(path) == committed
    publisher.close()
