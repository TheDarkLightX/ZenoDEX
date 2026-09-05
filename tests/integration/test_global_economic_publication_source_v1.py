"""Store-owned source snapshots; recording receipts do not qualify cryptography."""

from pathlib import Path

import pytest

from src.integration.global_economic_epoch_journal_v1 import (
    DurableEconomicEpochCommitStatusV1,
    GlobalEconomicEpochJournalV1,
)
from tests.integration.publisher_receipt_port_fixtures_v1 import (
    simulated_measured_publisher_crypto_v1 as simulated_measured_publisher_crypto_v1,
)
from tests.integration.test_global_economic_epoch_journal_v1 import (
    _commit_v1,
    _create_writer_v1,
    _fixture_v1,
    _open_writer_v1,
)


def _reject_source_decode(_source):
    raise ValueError("decode failure")


def test_source_snapshot_preserves_historical_state_after_a_competing_commit(tmp_path: Path) -> None:
    # Given a validated genesis and two authorized handles to this isolated store.
    activation, source, epoch = _fixture_v1()
    path = tmp_path / "economic.sqlite"
    journal, capability = _create_writer_v1(path, activation)
    competitor, other_capability = _open_writer_v1(path)
    with journal, competitor:
        captured = journal._publication_source_for_verified_publisher_v1(source.publication_id, capability)
        assert captured.source_head == source
        assert captured.state.state_root == source.state_root
        assert captured.current_head == source
        assert captured.activation.canonical_bytes == activation.canonical_bytes
        assert captured.authority.authority_root == journal._expected_authority.authority_root
        assert not journal._connection.in_transaction
        # When another writer commits after acquisition, the owned source stays PRE.
        committed = _commit_v1(competitor, other_capability, epoch, competitor.acquire_cas_head_token())
        assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        assert captured.state.state_root == source.state_root
        current = journal._publication_source_for_verified_publisher_v1(epoch.head.publication_id, capability)
        assert current.state.state_root == epoch.head.state_root
        assert current.state.state_root != captured.state.state_root
        historical = journal._publication_source_for_verified_publisher_v1(source.publication_id, capability)
        assert historical.source_head == source
        assert historical.current_head == epoch.head
        assert historical.state == captured.state
        # Then exact retry is recognized with the old token and adds no history.
        retry = _commit_v1(journal, capability, epoch, captured.cas_token)
        assert retry.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
        assert len(journal._read_epochs_v1()) == 1


def test_source_snapshot_requires_capability_of_the_exact_journal_before_io(tmp_path: Path, monkeypatch) -> None:
    activation, source, _epoch = _fixture_v1()
    first, first_capability = _create_writer_v1(tmp_path / "first.sqlite", activation)
    second, second_capability = _create_writer_v1(tmp_path / "second.sqlite", activation)
    with first, second:
        monkeypatch.setattr(first, "_validate_store_v1", lambda: pytest.fail("unauthorized source read"))
        for capability, reject_type in ((object(), TypeError), (second_capability, ValueError)):
            with pytest.raises(reject_type, match="capability"):
                first._publication_source_for_verified_publisher_v1(source.publication_id, capability)
        assert first_capability is not second_capability
        assert not first._connection.in_transaction


def test_source_snapshot_unknown_source_and_decode_failure_leave_no_effect(tmp_path: Path, monkeypatch) -> None:
    activation, source, epoch = _fixture_v1()
    journal, capability = _create_writer_v1(tmp_path / "economic.sqlite", activation)
    with journal:
        before = journal._connection.total_changes
        assert journal._publication_source_for_verified_publisher_v1("0x" + "ef" * 32, capability) is None
        assert journal._connection.total_changes == before
        monkeypatch.setattr(journal, "_decode_source_state_v1", _reject_source_decode)
        with pytest.raises(ValueError, match="decode failure"):
            journal._publication_source_for_verified_publisher_v1(source.publication_id, capability)
        assert not journal._connection.in_transaction
        assert journal._connection.total_changes == before
        # Release of the failed read lets an ordinary authorized write finish.
        assert _commit_v1(journal, capability, epoch, journal.acquire_cas_head_token()).status is DurableEconomicEpochCommitStatusV1.COMMITTED


def test_publisher_passes_the_acquired_committed_state_to_the_pure_verifier(
    tmp_path: Path, monkeypatch, simulated_measured_publisher_crypto_v1,
) -> None:
    import src.integration.global_economic_durable_publisher_v1 as publisher_module
    from tests.integration.test_global_economic_durable_publisher_v1 import (
        _bound_receipt_verifier_v1,
        _publisher_fixture_v1,
    )

    admission, candidate, body = _publisher_fixture_v1()
    verifier, _backend = _bound_receipt_verifier_v1(candidate)
    captured = []
    original_acquire = GlobalEconomicEpochJournalV1._publication_source_for_verified_publisher_v1
    original_verify = publisher_module._verify_economic_epoch_for_publisher_v1

    def acquire(journal, publication_id, capability):
        result = original_acquire(journal, publication_id, capability)
        captured.append(result)
        return result

    def verify(owned_candidate, receipt_verifier, token):
        assert len(captured) == 1
        assert owned_candidate.pre_state is captured[0].state
        assert owned_candidate.pre_state is not candidate.pre_state
        assert owned_candidate.pre_state == admission.state
        return original_verify(owned_candidate, receipt_verifier, token)

    monkeypatch.setattr(GlobalEconomicEpochJournalV1, "_publication_source_for_verified_publisher_v1", acquire)
    monkeypatch.setattr(publisher_module, "_verify_economic_epoch_for_publisher_v1", verify)
    with publisher_module.VerifiedDurableEconomicPublisherV1.create(
        tmp_path / "economic.sqlite", admission, verifier,
    ) as publisher:
        result = publisher.publish_economic_epoch(
            expected_source=publisher.head, candidate=candidate, body_and_state=body,
        )
        assert result.status is DurableEconomicEpochCommitStatusV1.COMMITTED
