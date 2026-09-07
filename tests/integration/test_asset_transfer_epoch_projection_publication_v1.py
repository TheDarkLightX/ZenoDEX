"""Consumed runtime projection at the isolated custody publication boundary.

Command signatures use real BLS and the ledger stores actual committed bundles.
Receipt processes and release coordinates are synthetic test fixtures. These
histories qualify neither RISC0 proofs nor deployment or publisher-host trust.
"""

from __future__ import annotations

from dataclasses import replace
from pathlib import Path

import pytest

from src.core import asset_transfer_receipt_admission_v1 as admission
from src.core.asset_transfer_epoch_projection_v1 import (
    project_asset_transfer_epoch_position_v1,
)
from src.integration.global_economic_durable_publisher_v1 import (
    GlobalEconomicAllocationRejectedV1,
    VerifiedDurableEconomicPublisherV1,
)
from src.integration.global_economic_epoch_journal_v1 import DurableEconomicEpochCommitStatusV1
from tests.core.test_economic_receipt_verifier_release_v1 import _RecordingBackend
from tests.integration import custody_asset_receipt_pipeline_fixtures_v1 as fixtures
from tests.integration.publisher_receipt_port_fixtures_v1 import (
    simulated_measured_publisher_crypto_v1 as simulated_measured_publisher_crypto_v1,
)
from tests.integration.test_global_economic_custody_pipeline_v1 import (
    _pipeline_v1,
    _publication_v1,
)
from tests.integration.test_global_economic_sealed_bls_pipeline_v1 import _logical_store_v1


def _omitted_replay_fixture_v1(owner, first, monkeypatch: pytest.MonkeyPatch):
    """Prepare a bound proposal with a reused nonce and a structurally valid table.

Only the test fixture builder omits its proposed replay insertion. The patch is
removed before the real authentication, allocation and publication code runs.
The predecessor is the state actually committed by the preceding test step.
"""
    predecessor = first.candidate.post_state
    omitted = []

    def fixture_replace(value, **changes):
        if value is predecessor and "replay_state" in changes:
            omitted.append(changes["replay_state"])
            changes["replay_state"] = predecessor.replay_state
        return replace(value, **changes)

    with monkeypatch.context() as patch:
        patch.setattr(fixtures, "replace", fixture_replace)
        subject = fixtures._fixture(
            owner, activation=first.activation, pre_state=predecessor, nonce_start=1,
        )
    assert len(omitted) == 1
    assert len(omitted[0]) == len(predecessor.replay_state) + 1
    occurrence = subject.candidate.command_occurrences[0]
    assert any(row.replay_id == occurrence.replay_id for row in predecessor.replay_state)
    assert all(row.occurrence_id != occurrence.occurrence_id for row in predecessor.replay_state)
    assert subject.candidate.post_state.replay_state == predecessor.replay_state
    return subject


def _assert_binding_rejection_v1(rejection, cause: str) -> None:
    assert rejection.code.value == "GLOBAL_FRAGMENT_REJECTED"
    assert rejection.occurrence_index == 0
    assert rejection.cause is not None
    assert rejection.cause.code.value == cause


def test_custody_publication_consumes_projection_and_exact_retry_preserves_commit(
    tmp_path: Path, simulated_measured_publisher_crypto_v1, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Given a backed transfer, reverify an exact retry without publishing twice."""
    subject = fixtures._fixture(simulated_measured_publisher_crypto_v1)
    initial, candidate, body = _publication_v1(subject)
    backend = _RecordingBackend()
    projections = []

    def observe_projection(**values):
        projection = project_asset_transfer_epoch_position_v1(**values)
        projections.append(projection)
        return projection

    monkeypatch.setattr(admission, "project_asset_transfer_epoch_position_v1", observe_projection)
    path = tmp_path / "projection.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path, initial, _pipeline_v1(subject, candidate, backend),
    )
    try:
        source = publisher.head
        result = publisher.publish_economic_epoch(
            expected_source=source, candidate=candidate,
            body_and_state=body, raw_evidence=(subject.raw,),
        )
        assert result.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        assert len(projections) == 1
        assert projections[0].predecessor == candidate.pre_state
        assert projections[0].post_state == candidate.post_state
        assert result.head.state_root == projections[0].post_state.state_root
        committed = _logical_store_v1(path)
        calls = tuple(backend.calls), tuple(subject.calls)
        retry = publisher.publish_economic_epoch(
            expected_source=source, candidate=candidate,
            body_and_state=body, raw_evidence=(subject.raw,),
        )
        assert retry.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
        assert retry.head == result.head
        assert retry.published_epoch == result.published_epoch
        assert len(projections) == 2
        assert projections[1].post_state == projections[0].post_state
        assert _logical_store_v1(path) == committed
        assert tuple(backend.calls) == (*calls[0], calls[0][-1])
        assert tuple(subject.calls) == (*calls[1], *subject.expected)
    finally:
        publisher.close()


def test_projection_drift_rejects_before_fragment_root_receipt_and_commit(
    tmp_path: Path, simulated_measured_publisher_crypto_v1, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Given a valid relation, derived frame drift rejects without poisoning a retry."""
    subject = fixtures._fixture(simulated_measured_publisher_crypto_v1)
    initial, candidate, body = _publication_v1(subject)
    backend = _RecordingBackend()
    path = tmp_path / "projection-drift.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path, initial, _pipeline_v1(subject, candidate, backend),
    )
    projections = []

    def drifting_projection(**values):
        projection = project_asset_transfer_epoch_position_v1(**values)
        drift = replace(projection.post_state, history_root="0x" + "ef" * 32)
        assert drift != candidate.post_state
        object.__setattr__(projection, "post_state", drift)
        projections.append(projection)
        return projection

    def unexpected_fragment(*args):
        pytest.fail("projection mismatch reached fragment minting")

    try:
        source = publisher.head
        before = _logical_store_v1(path)
        calls = tuple(backend.calls)
        with monkeypatch.context() as patch:
            patch.setattr(admission, "project_asset_transfer_epoch_position_v1", drifting_projection)
            patch.setattr(admission, "_admit_global_fragment_v1", unexpected_fragment)
            with pytest.raises(GlobalEconomicAllocationRejectedV1) as caught:
                publisher.publish_economic_epoch(
                    expected_source=source, candidate=candidate,
                    body_and_state=body, raw_evidence=(subject.raw,),
                )
            _assert_binding_rejection_v1(caught.value.rejection, "GLOBAL_PROJECTION_ROWS_DRIFT")
        assert len(projections) == 1
        assert _logical_store_v1(path) == before
        assert publisher.head == source
        assert tuple(backend.calls) == calls
        assert tuple(subject.calls) == subject.expected
        result = publisher.publish_economic_epoch(
            expected_source=source, candidate=candidate,
            body_and_state=body, raw_evidence=(subject.raw,),
        )
        assert result.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    finally:
        publisher.close()


def test_committed_nonce_replay_rejects_before_projection_then_fresh_transfer_commits(
    tmp_path: Path, simulated_measured_publisher_crypto_v1, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Given committed custody state, a reused nonce leaves the next transfer usable.

    Keep this longer scenario together so the actual committed predecessor,
    restart, rejected attempt and recovery remain visible in one ordered history.
    """
    owner = simulated_measured_publisher_crypto_v1
    first = fixtures._fixture(owner)
    initial, candidate_one, body_one = _publication_v1(first)
    path = tmp_path / "projection-history.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path, initial, _pipeline_v1(first, candidate_one, _RecordingBackend()),
    )
    try:
        result_one = publisher.publish_economic_epoch(
            expected_source=publisher.head, candidate=candidate_one,
            body_and_state=body_one, raw_evidence=(first.raw,),
        )
        assert result_one.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    finally:
        publisher.close()

    replay = _omitted_replay_fixture_v1(owner, first, monkeypatch)
    fresh = fixtures._fixture(
        owner, activation=first.activation, pre_state=candidate_one.post_state, nonce_start=2,
    )
    _, candidate_bad, body_bad = _publication_v1(replay, receipt=b"replayed-nonce-epoch")
    _, candidate_fresh, body_fresh = _publication_v1(fresh, receipt=b"fresh-nonce-epoch")
    # One fixed synthetic leaf endpoint recognizes both exact test statements.
    replay_expected = replay.expected
    replay.expected = (*replay.expected, *fresh.expected)
    backend = _RecordingBackend()
    publisher = VerifiedDurableEconomicPublisherV1.open(
        path, initial, _pipeline_v1(replay, candidate_bad, backend),
    )

    def unexpected_projection(**values):
        pytest.fail("committed replay reached prospective construction")

    def unexpected_fragment(*args):
        pytest.fail("committed replay reached fragment minting")

    try:
        source = publisher.head
        assert source == result_one.head
        before = _logical_store_v1(path)
        calls = tuple(backend.calls)
        with monkeypatch.context() as patch:
            patch.setattr(admission, "project_asset_transfer_epoch_position_v1", unexpected_projection)
            patch.setattr(admission, "_admit_global_fragment_v1", unexpected_fragment)
            with pytest.raises(GlobalEconomicAllocationRejectedV1) as caught:
                publisher.publish_economic_epoch(
                    expected_source=source, candidate=candidate_bad,
                    body_and_state=body_bad, raw_evidence=(replay.raw,),
                )
            _assert_binding_rejection_v1(caught.value.rejection, "GLOBAL_REPLAY_CONTINUITY_DRIFT")
        assert _logical_store_v1(path) == before
        assert publisher.head == source
        assert tuple(backend.calls) == calls
        assert tuple(replay.calls) == replay_expected
        result = publisher.publish_economic_epoch(
            expected_source=source, candidate=candidate_fresh,
            body_and_state=body_fresh, raw_evidence=(fresh.raw,),
        )
        assert result.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        after = _logical_store_v1(path)
        assert after != before
        assert len(after[2]) == 2
        calls = tuple(backend.calls), tuple(replay.calls)
        retry = publisher.publish_economic_epoch(
            expected_source=source, candidate=candidate_fresh,
            body_and_state=body_fresh, raw_evidence=(fresh.raw,),
        )
        assert retry.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
        assert retry.head == result.head
        assert _logical_store_v1(path) == after
        assert tuple(backend.calls) == (*calls[0], calls[0][-1])
        assert tuple(replay.calls) == (*calls[1], *fresh.expected)
    finally:
        publisher.close()
