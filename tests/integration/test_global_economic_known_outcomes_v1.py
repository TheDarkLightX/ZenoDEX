"""A known journal refusal survives response and observation failures.

These isolated fixtures execute the real journal transaction and exact retry.
Failure injection affects acknowledgment, observation, and scheduling only.
Complete SQLite rows identify the winning bundle independently of projection.
The anchored schedule interleaves two verified publishers at the commit port;
it makes no claim about cross-process writer exclusion or cryptographic proof.
"""

from __future__ import annotations

import sqlite3
from pathlib import Path

import pytest

from src.core.global_economic_monotonic_anchor_v1 import decode_global_economic_monotonic_anchor_v1
from src.core.global_settlement_types_v1 import ZERO_ROOT_V1
from src.integration.global_economic_durable_publisher_v1 import (
    GlobalEconomicAnchorAdvanceIndeterminateV1,
    GlobalEconomicRollbackDetectedV1,
    VerifiedDurableEconomicPublisherV1,
)
from src.integration.global_economic_epoch_journal_v1 import (
    DurableEconomicEpochCommitStatusV1,
    GlobalEconomicEpochJournalV1,
)
from tests.integration.publisher_receipt_port_fixtures_v1 import publisher_raw_evidence_v1
from tests.integration.publisher_receipt_port_fixtures_v1 import (
    simulated_measured_publisher_crypto_v1 as simulated_measured_publisher_crypto_v1,
)
from tests.integration.test_global_economic_durable_publisher_v1 import (
    _anchor_for_path_v1,
    _bound_monotonic_anchor_backend_v1,
    _bound_receipt_verifier_v1,
    _MemoryMonotonicAnchorBackendV1,
    _publisher_candidate_v1,
    _publisher_fixture_v1,
)

pytestmark = pytest.mark.usefixtures("simulated_measured_publisher_crypto_v1")


def _logical_store(path: Path) -> tuple[tuple[tuple[object, ...], ...], ...]:
    with sqlite3.connect(path) as connection:
        connection.execute("BEGIN")
        return tuple(tuple(connection.execute(query).fetchall()) for query in (
            "SELECT * FROM metadata ORDER BY singleton",
            "SELECT * FROM current_head ORDER BY singleton",
            "SELECT * FROM economic_epochs ORDER BY publication_id",
        ))


def test_given_known_stale_when_projection_and_observation_fail_then_refusal_stays_known(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    admission, alice_candidate, alice_body = _publisher_fixture_v1(receipt_bytes=b"known-alice")
    _, bob_candidate, bob_body = _publisher_fixture_v1(receipt_bytes=b"known-bob")
    path = tmp_path / "known-stale.sqlite"
    alice = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _bound_receipt_verifier_v1(alice_candidate)[0],
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
    failure = OSError("known stale response unavailable")
    projected = []

    def failed_stale_projection(outcome, _published):
        projected.append(outcome.status)
        assert outcome.status is DurableEconomicEpochCommitStatusV1.STALE_HEAD
        raise failure

    def unavailable_history(*_args):
        raise OSError("history unavailable after known refusal")

    with monkeypatch.context() as patch:
        patch.setattr(VerifiedDurableEconomicPublisherV1, "_outcome_v1",
                      staticmethod(failed_stale_projection))
        patch.setattr(GlobalEconomicEpochJournalV1,
                      "_contains_exact_epoch_for_verified_publisher_v1", unavailable_history)
        with pytest.raises(OSError, match="^known stale response unavailable$") as caught:
            alice.publish_economic_epoch(
                expected_source=source, candidate=alice_candidate, body_and_state=alice_body,
                raw_evidence=publisher_raw_evidence_v1(alice_candidate),
            )
    assert caught.value is failure
    assert projected == [DurableEconomicEpochCommitStatusV1.STALE_HEAD]
    assert _logical_store(path) == winner_rows
    assert alice.head == winner.head
    alice.close()
    bob.close()


def test_given_historical_committed_retry_when_newer_anchor_lags_then_result_stays_committed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    admission, first_candidate, first_body = _publisher_fixture_v1(receipt_bytes=b"historical-first")
    second_candidate, second_body = _publisher_candidate_v1(
        receipt_bytes=b"historical-second",
        verifier_registry_root=first_candidate.profile.verifier_registry_root,
        pre_state=first_candidate.post_state,
        nonce_start=2,
    )
    path = tmp_path / "historical-known-commit.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _bound_receipt_verifier_v1(first_candidate)[0],
    )
    source = created.head
    genesis = _anchor_for_path_v1(path, anchor_sequence=0, previous_anchor_root=ZERO_ROOT_V1)
    first = created.publish_economic_epoch(
        expected_source=source, candidate=first_candidate, body_and_state=first_body,
        raw_evidence=publisher_raw_evidence_v1(first_candidate),
    )
    assert first.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    created.close()
    first_anchor = _anchor_for_path_v1(path, anchor_sequence=1, previous_anchor_root=genesis.anchor_root)
    backend = _MemoryMonotonicAnchorBackendV1(first_anchor)
    bound = _bound_monotonic_anchor_backend_v1(first_anchor, backend)
    alice = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path, admission, _bound_receipt_verifier_v1(first_candidate)[0], bound,
    )
    bob = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path, admission, _bound_receipt_verifier_v1(second_candidate)[0], bound,
    )
    original_commit = GlobalEconomicEpochJournalV1._commit_epoch_from_verified_publisher_v1
    original_projection = VerifiedDurableEconomicPublisherV1._outcome_v1
    winner_rows = []
    projected = []
    scheduled = False

    def retry_after_newer_winner(*args):
        nonlocal scheduled
        if not scheduled:
            scheduled = True
            backend.fail_next_cas = True
            with pytest.raises(GlobalEconomicAnchorAdvanceIndeterminateV1):
                bob.publish_economic_epoch(
                    expected_source=first.head, candidate=second_candidate, body_and_state=second_body,
                    raw_evidence=publisher_raw_evidence_v1(second_candidate),
                )
            winner_rows.append(_logical_store(path))
        return original_commit(*args)

    def fail_historical_projection(outcome, published):
        if outcome.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED:
            projected.append(outcome)
            raise OSError("historical committed response unavailable")
        return original_projection(outcome, published)

    # E1's original source is genesis; the lagging E2 anchor needs E1 as source.
    with monkeypatch.context() as patch:
        patch.setattr(GlobalEconomicEpochJournalV1,
                      "_commit_epoch_from_verified_publisher_v1", retry_after_newer_winner)
        patch.setattr(VerifiedDurableEconomicPublisherV1, "_outcome_v1",
                      staticmethod(fail_historical_projection))
        with pytest.raises(GlobalEconomicAnchorAdvanceIndeterminateV1,
                           match="reconciliation is required") as caught:
            alice.publish_economic_epoch(
                expected_source=source, candidate=first_candidate, body_and_state=first_body,
                raw_evidence=publisher_raw_evidence_v1(first_candidate),
            )
    assert isinstance(caught.value.__cause__, GlobalEconomicRollbackDetectedV1)
    assert len(projected) == 1 and projected[0].committed_epoch == first.committed_epoch
    assert len(winner_rows) == 1 and len(winner_rows[0][2]) == 2
    assert _logical_store(path) == winner_rows[0]
    assert decode_global_economic_monotonic_anchor_v1(backend.current) == first_anchor
    # Recover E2 through its own retry, then reopen and recover E1's old result.
    second = bob.publish_economic_epoch(
        expected_source=first.head, candidate=second_candidate, body_and_state=second_body,
        raw_evidence=publisher_raw_evidence_v1(second_candidate),
    )
    assert second.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    alice.close()
    bob.close()
    reopened = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path, admission, _bound_receipt_verifier_v1(first_candidate)[0], bound,
    )
    recovered = reopened.publish_economic_epoch(
        expected_source=source, candidate=first_candidate, body_and_state=first_body,
        raw_evidence=publisher_raw_evidence_v1(first_candidate),
    )
    assert recovered.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert recovered.committed_epoch == first.committed_epoch
    assert recovered.head == second.head
    assert _logical_store(path) == winner_rows[0]
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert observed.publication_id == second.head.publication_id
    assert observed.publication_sequence == 2
    reopened.close()


def test_given_anchored_other_winner_when_stale_response_fails_then_its_commit_is_not_attributed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    admission, alice_candidate, alice_body = _publisher_fixture_v1(receipt_bytes=b"anchored-known-alice")
    _, bob_candidate, bob_body = _publisher_fixture_v1(receipt_bytes=b"anchored-known-bob")
    path = tmp_path / "anchored-known-stale.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _bound_receipt_verifier_v1(alice_candidate)[0],
    )
    created.close()
    genesis = _anchor_for_path_v1(path, anchor_sequence=0, previous_anchor_root=ZERO_ROOT_V1)
    backend = _MemoryMonotonicAnchorBackendV1(genesis)
    bound = _bound_monotonic_anchor_backend_v1(genesis, backend)
    alice = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path, admission, _bound_receipt_verifier_v1(alice_candidate)[0], bound,
    )
    bob = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path, admission, _bound_receipt_verifier_v1(bob_candidate)[0], bound,
    )
    source = alice.head
    original_commit = GlobalEconomicEpochJournalV1._commit_epoch_from_verified_publisher_v1
    original_projection = VerifiedDurableEconomicPublisherV1._outcome_v1
    failure = OSError("anchored stale response unavailable")
    winner_rows = []
    scheduled = False

    def commit_after_other_winner(*args):
        nonlocal scheduled
        if not scheduled:
            scheduled = True
            backend.fail_next_cas = True
            with pytest.raises(GlobalEconomicAnchorAdvanceIndeterminateV1):
                bob.publish_economic_epoch(
                    expected_source=source, candidate=bob_candidate, body_and_state=bob_body,
                    raw_evidence=publisher_raw_evidence_v1(bob_candidate),
                )
            winner_rows.append(_logical_store(path))
        return original_commit(*args)

    def failed_loser_projection(outcome, published):
        if outcome.status is DurableEconomicEpochCommitStatusV1.STALE_HEAD:
            raise failure
        return original_projection(outcome, published)

    # Alice has passed anchor admission before Bob wins and loses his anchor ACK.
    with monkeypatch.context() as patch:
        patch.setattr(GlobalEconomicEpochJournalV1,
                      "_commit_epoch_from_verified_publisher_v1", commit_after_other_winner)
        patch.setattr(VerifiedDurableEconomicPublisherV1, "_outcome_v1",
                      staticmethod(failed_loser_projection))
        with pytest.raises(OSError, match="^anchored stale response unavailable$") as caught:
            alice.publish_economic_epoch(
                expected_source=source, candidate=alice_candidate, body_and_state=alice_body,
                raw_evidence=publisher_raw_evidence_v1(alice_candidate),
            )
    assert caught.value is failure
    assert len(winner_rows) == 1 and len(winner_rows[0][2]) == 1
    assert _logical_store(path) == winner_rows[0]
    assert decode_global_economic_monotonic_anchor_v1(backend.current) == genesis
    # Only Bob's byte-identical retry reconciles the one committed bundle.
    recovered = bob.publish_economic_epoch(
        expected_source=source, candidate=bob_candidate, body_and_state=bob_body,
        raw_evidence=publisher_raw_evidence_v1(bob_candidate),
    )
    assert recovered.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert _logical_store(path) == winner_rows[0]
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert observed.publication_id == recovered.head.publication_id
    assert observed.publication_sequence == 1
    alice.close()
    bob.close()
