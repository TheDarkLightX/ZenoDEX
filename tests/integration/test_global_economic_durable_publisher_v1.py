"""Authority, replay, and concurrency evidence for the durable publisher."""

from __future__ import annotations

import hashlib
import inspect
from dataclasses import replace
from pathlib import Path
from threading import Event, Thread
from typing import Any, cast

import pytest

from src.core.economic_receipt_verifier_deployment_v1 import (
    BoundEconomicReceiptVerifierV1,
    EconomicReceiptVerifierEvidenceManifestV1,
    bind_economic_receipt_verifier_deployment_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierRegistryV1,
    EconomicReceiptVerifierSelectionPurposeV1,
)
from src.core.global_economic_durable_activation_v1 import (
    prepare_durable_economic_initial_state_bundle_v1,
)
from src.core.global_economic_proof_v1 import EconomicEpochReceiptCandidateV1
from src.core.global_settlement_types_v1 import hash_global_v1
from src.integration.global_economic_authority_journal_v1 import (
    GlobalEconomicAuthorityCommitStatusV1,
    GlobalEconomicAuthorityJournalV1,
    authority_journal_path_for_epoch_v1,
)
from src.integration.global_economic_commit_v1 import EconomicEpochBodyAndStateV1
from src.integration.global_economic_durable_publisher_v1 import (
    VerifiedDurableEconomicPublisherV1,
    VerifiedDurableEconomicPublishOutcomeV1,
)
from src.integration.global_economic_epoch_journal_v1 import (
    DurableEconomicEpochCommitStatusV1,
    GlobalEconomicEpochJournalV1,
)
from src.integration.global_economic_migration_journal_v1 import (
    DurableEconomicCommitStatusV1,
    GlobalEconomicMigrationJournalV1,
)
from tests.core.test_economic_receipt_verifier_release_v1 import (
    _ARTIFACT_BYTES,
    _manifest,
    _RecordingBackend,
    _release,
)
from tests.core.test_global_settlement_abi_v1 import (
    _epoch_admission_fixture,
    _initial_state_admission,
    _migration_admission_for_source_head,
    _RecordingReceiptVerifier,
    _root,
)


def _receipt_verifier_manifest_v1() -> EconomicReceiptVerifierEvidenceManifestV1:
    return _manifest(
        root_image_id=_root(411),
        max_receipt_bytes=4_096,
        max_journal_bytes=1_048_576,
    )


def _bound_receipt_verifier_v1(
    candidate: EconomicEpochReceiptCandidateV1,
    backend: _RecordingBackend | None = None,
) -> tuple[BoundEconomicReceiptVerifierV1, _RecordingBackend]:
    manifest = _receipt_verifier_manifest_v1()
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    assert registry.registry_root == candidate.profile.verifier_registry_root
    selected_backend = backend or _RecordingBackend()
    return (
        bind_economic_receipt_verifier_deployment_v1(
            profile=candidate.profile,
            verifier_registry=registry,
            selection_purpose=(
                EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW
            ),
            evidence_manifest=manifest,
            measured_artifact_bytes=_ARTIFACT_BYTES,
            deployment_root=candidate.pre_state.deployment_root,
            backend=selected_backend,
        ),
        selected_backend,
    )


def _publisher_fixture_v1(*, receipt_bytes: bytes = b"durable-publisher-epoch"):
    manifest = _receipt_verifier_manifest_v1()
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    candidate = _epoch_admission_fixture(
        1,
        verifier_registry_root=registry.registry_root,
    )
    body = EconomicEpochBodyAndStateV1(
        pre_state_root=candidate.pre_state.state_root,
        post_state=candidate.post_state,
        ordered_command_body_hashes=candidate.ordered_command_body_hashes,
        receipt_archive_root=hash_global_v1(
            "durable-publisher-receipt-archive-v1",
            {"receipt_sha256": hashlib.sha256(receipt_bytes).hexdigest()},
        ),
        data_availability_root=candidate.certificate.data_availability_root,
        finality_root=candidate.certificate.finality_root,
    )
    certificate = replace(
        candidate.certificate,
        body_commitment=body.body_commitment,
        receipt_root="0x" + hashlib.sha256(receipt_bytes).hexdigest(),
        journal_bytes=1,
    )
    certificate = replace(
        certificate,
        journal_bytes=len(certificate.canonical_journal_bytes),
    )
    candidate = replace(
        candidate,
        certificate=certificate,
        receipt_bytes=receipt_bytes,
        expected_body_commitment=body.body_commitment,
    )
    admission = _initial_state_admission(candidate.profile, candidate.pre_state)
    return admission, candidate, body


def test_create_publish_reopen_and_exact_retry_are_one_durable_history(
    tmp_path: Path,
) -> None:
    # Arrange: Alice prepares one valid epoch and a verifier-backed genesis.
    admission, candidate, body = _publisher_fixture_v1()
    path = tmp_path / "publisher.sqlite"
    first_verifier, first_backend = _bound_receipt_verifier_v1(candidate)
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        first_verifier,
    )
    source = publisher.head

    # Act: publish, simulate a lost acknowledgement, reopen, and retry exactly.
    committed = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )
    publisher.close()
    retry_verifier, retry_backend = _bound_receipt_verifier_v1(candidate)
    reopened = VerifiedDurableEconomicPublisherV1.open(
        path,
        admission,
        retry_verifier,
    )
    retried = reopened.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: one exact publication survives restart and duplicate submission.
    assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert committed.published_epoch == retried.published_epoch
    assert reopened.head == committed.committed_epoch
    assert len(first_backend.calls) == 2
    assert len(retry_backend.calls) == 2
    reopened.close()


def test_exact_create_retry_recovers_committed_activation_after_lost_ack(
    tmp_path: Path,
) -> None:
    # Arrange: Alice creates the exact verified activation, then loses the handle.
    admission, candidate, _ = _publisher_fixture_v1()
    path = tmp_path / "activation-create-retry.sqlite"
    first = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    expected_head = first.head
    first.close()

    # Act: the operator retries create because the original acknowledgment was lost.
    recovered = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )

    # Assert: exact activation bytes recover one sequence-zero durable history.
    assert recovered.head == expected_head
    recovered.close()


def test_create_retry_rejects_matching_activation_with_nonzero_history(
    tmp_path: Path,
) -> None:
    # Arrange: one verifier commits an epoch under the matching activation.
    admission, candidate, body = _publisher_fixture_v1()
    path = tmp_path / "create-retry-nonzero-history.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    committed = publisher.publish_economic_epoch(
        expected_source=publisher.head,
        candidate=candidate,
        body_and_state=body,
    )
    publisher.close()
    before = path.read_bytes()

    class RejectingHistoryBackend(_RecordingBackend):
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> object:
            result = super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            if receipt_bytes == candidate.receipt_bytes:
                raise ValueError("recovered history receipt rejected")
            return result

    backend = RejectingHistoryBackend()
    verifier, _ = _bound_receipt_verifier_v1(candidate, backend)

    # Act and assert: create recovery is restricted to the activation-only head.
    with pytest.raises(ValueError, match="sequence-zero activation head"):
        VerifiedDurableEconomicPublisherV1.create(
            path,
            admission,
            verifier,
        )
    assert path.read_bytes() == before
    assert len(backend.calls) == 1
    with GlobalEconomicEpochJournalV1.open(path) as journal:
        assert journal.head == committed.committed_epoch


def test_fabricated_source_metadata_is_stale_before_receipt_verification(
    tmp_path: Path,
) -> None:
    # Arrange: Mallory retains the real publication id but changes its certificate.
    admission, candidate, body = _publisher_fixture_v1()
    verifier, verifier_backend = _bound_receipt_verifier_v1(candidate)
    publisher = VerifiedDurableEconomicPublisherV1.create(
        tmp_path / "fabricated-source.sqlite",
        admission,
        verifier,
    )
    source = publisher.head
    fabricated = replace(source, certificate_root="0x" + "ab" * 32)

    # Act: submit a valid epoch against the fabricated source description.
    outcome = publisher.publish_economic_epoch(
        expected_source=fabricated,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: stored history owns source identity and no epoch receipt is checked.
    assert outcome.status is DurableEconomicEpochCommitStatusV1.STALE_HEAD
    assert outcome.published_epoch is None
    assert publisher.head == source
    assert len(verifier_backend.calls) == 1
    publisher.close()


def test_body_binding_rejection_is_noop(
    tmp_path: Path,
) -> None:
    # Arrange: the supplied body differs from the certificate-bound receipt archive.
    admission, candidate, body = _publisher_fixture_v1()
    publisher = VerifiedDurableEconomicPublisherV1.create(
        tmp_path / "body-mismatch.sqlite",
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    source = publisher.head
    wrong_body = replace(body, receipt_archive_root="0x" + "cd" * 32)

    # Act and assert: verified proof material cannot publish a different full body.
    with pytest.raises(ValueError, match="body commitment"):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=wrong_body,
        )
    assert publisher.head == source
    publisher.close()


def test_receipt_replacement_rejects_without_publication(
    tmp_path: Path,
) -> None:
    # Arrange: the candidate receipt changes after its certificate was constructed.
    admission, candidate, body = _publisher_fixture_v1()
    publisher = VerifiedDurableEconomicPublisherV1.create(
        tmp_path / "receipt-replacement.sqlite",
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    source = publisher.head
    replaced_receipt = replace(candidate, receipt_bytes=b"replacement-receipt")

    # Act and assert: receipt-root verification fails before durable publication.
    with pytest.raises(ValueError, match="receipt root"):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=replaced_receipt,
            body_and_state=body,
        )
    assert publisher.head == source
    publisher.close()


def test_selected_verifier_rejection_is_noop(
    tmp_path: Path,
) -> None:
    # Arrange: genesis verifies, while the selected backend rejects the epoch proof.
    admission, candidate, body = _publisher_fixture_v1()

    class RejectingEpochVerifier(_RecordingBackend):
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> object:
            result = super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            if receipt_bytes == candidate.receipt_bytes:
                raise ValueError("selected verifier rejected epoch")
            return result

    backend = RejectingEpochVerifier()
    verifier, _ = _bound_receipt_verifier_v1(candidate, backend)
    publisher = VerifiedDurableEconomicPublisherV1.create(
        tmp_path / "verifier-reject.sqlite",
        admission,
        verifier,
    )
    source = publisher.head

    # Act and assert: verifier rejection propagates and SQLite stays at genesis.
    with pytest.raises(ValueError, match="selected verifier rejected"):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    assert publisher.head == source
    assert len(backend.calls) == 2
    publisher.close()


def test_backend_method_replacement_cannot_turn_rejection_into_publication(
    tmp_path: Path,
) -> None:
    # Arrange: genesis passes, but the callable pinned at binding rejects the epoch.
    admission, candidate, body = _publisher_fixture_v1()

    class RejectingEpochBackend(_RecordingBackend):
        def __init__(self) -> None:
            super().__init__()
            self.replacement_calls = 0

        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> object:
            result = super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            if receipt_bytes == candidate.receipt_bytes:
                raise ValueError("pinned epoch verifier rejected receipt")
            return result

    backend = RejectingEpochBackend()
    verifier, _ = _bound_receipt_verifier_v1(candidate, backend)
    publisher = VerifiedDurableEconomicPublisherV1.create(
        tmp_path / "replaced-backend-method.sqlite",
        admission,
        verifier,
    )
    source = publisher.head

    def accept_replacement(
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        backend.replacement_calls += 1

    cast(Any, backend).verify_succinct_receipt = accept_replacement

    # Act and assert: in-place method replacement cannot forge durable acceptance.
    with pytest.raises(ValueError, match="pinned epoch verifier rejected receipt"):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    assert publisher.head == source
    assert backend.replacement_calls == 0
    publisher.close()


def test_generic_caller_selected_verifier_rejects_before_backend_use(
    tmp_path: Path,
) -> None:
    # Arrange: Mallory supplies a protocol-shaped verifier with no release binding.
    admission, _, _ = _publisher_fixture_v1()
    generic = _RecordingReceiptVerifier()

    # Act and assert: only an exact measured profile-selected capability is accepted.
    with pytest.raises(TypeError, match="bound economic receipt verifier"):
        VerifiedDurableEconomicPublisherV1.create(
            tmp_path / "generic-verifier.sqlite",
            admission,
            generic,
        )
    assert generic.calls == []


def test_two_publishers_from_one_source_linearize_one_valid_successor(
    tmp_path: Path,
) -> None:
    # Arrange: two sequencers hold distinct, valid receipts for the same source.
    admission, first_candidate, first_body = _publisher_fixture_v1(
        receipt_bytes=b"first-competing-receipt"
    )
    _, second_candidate, second_body = _publisher_fixture_v1(
        receipt_bytes=b"second-competing-receipt"
    )
    path = tmp_path / "competing-publishers.sqlite"
    first = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(first_candidate)[0],
    )
    second = VerifiedDurableEconomicPublisherV1.open(
        path,
        admission,
        _bound_receipt_verifier_v1(second_candidate)[0],
    )
    source = first.head

    # Act: the first candidate commits before the second reaches SQLite CAS.
    winner = first.publish_economic_epoch(
        expected_source=source,
        candidate=first_candidate,
        body_and_state=first_body,
    )
    loser = second.publish_economic_epoch(
        expected_source=source,
        candidate=second_candidate,
        body_and_state=second_body,
    )

    # Assert: one full verifier-derived bundle wins and the other is a typed no-op.
    assert winner.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert loser.status is DurableEconomicEpochCommitStatusV1.STALE_HEAD
    assert first.head == second.head == winner.committed_epoch
    first.close()
    second.close()


def test_head_change_during_receipt_verification_returns_stale_noop(
    tmp_path: Path,
) -> None:
    # Arrange: one verifier pauses while a second publisher commits another receipt.
    admission, delayed_candidate, delayed_body = _publisher_fixture_v1(
        receipt_bytes=b"delayed-valid-receipt"
    )
    _, fast_candidate, fast_body = _publisher_fixture_v1(
        receipt_bytes=b"fast-valid-receipt"
    )
    entered = Event()
    release = Event()

    class BlockingEpochVerifier(_RecordingBackend):
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> object:
            result = super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            if receipt_bytes == delayed_candidate.receipt_bytes:
                entered.set()
                if not release.wait(timeout=10):
                    raise RuntimeError("test verifier release timed out")
            return result

    path = tmp_path / "verification-race.sqlite"
    delayed = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(
            delayed_candidate,
            BlockingEpochVerifier(),
        )[0],
    )
    fast = VerifiedDurableEconomicPublisherV1.open(
        path,
        admission,
        _bound_receipt_verifier_v1(fast_candidate)[0],
    )
    source = delayed.head
    results: list[VerifiedDurableEconomicPublishOutcomeV1] = []

    def publish_delayed() -> None:
        results.append(
            delayed.publish_economic_epoch(
                expected_source=source,
                candidate=delayed_candidate,
                body_and_state=delayed_body,
            )
        )

    thread = Thread(target=publish_delayed)
    thread.start()
    assert entered.wait(timeout=10)

    # Act: a competing valid epoch commits while the first verifier is paused.
    winner = fast.publish_economic_epoch(
        expected_source=source,
        candidate=fast_candidate,
        body_and_state=fast_body,
    )
    release.set()
    thread.join(timeout=10)

    # Assert: the delayed candidate observes the changed source and publishes nothing.
    assert not thread.is_alive()
    assert winner.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert len(results) == 1
    delayed_outcome = results[0]
    assert delayed_outcome.status is DurableEconomicEpochCommitStatusV1.STALE_HEAD
    assert delayed.head == fast.head == winner.committed_epoch
    delayed.close()
    fast.close()


def test_old_store_cannot_reopen_after_shared_authority_revocation(
    tmp_path: Path,
) -> None:
    # Arrange: an old-profile publisher closes while its shared authority is active.
    admission, candidate, _ = _publisher_fixture_v1()
    path = tmp_path / "old-profile.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    expected_head = publisher.head
    publisher.close()
    epoch_bytes = path.read_bytes()
    authority = GlobalEconomicAuthorityJournalV1.open(
        authority_journal_path_for_epoch_v1(path)
    )

    # Act: governance durably revokes the current authority generation.
    outcome = authority._commit_successor_for_unmounted_control_plane_v1(
        authority.head.revoked_successor(),
        authority._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )
    authority.close()

    # Assert: reopening the retained store fails closed and changes no epoch bytes.
    assert outcome.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    with pytest.raises(ValueError, match="current authority mismatch"):
        VerifiedDurableEconomicPublisherV1.open(
            path,
            admission,
            _bound_receipt_verifier_v1(candidate)[0],
        )
    assert path.read_bytes() == epoch_bytes
    with GlobalEconomicEpochJournalV1.open(path) as structural_reader:
        assert structural_reader.head == expected_head


def test_two_named_epoch_stores_cannot_share_one_authority_head(
    tmp_path: Path,
) -> None:
    # Arrange: Alice creates the one authorized epoch store in this directory.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"single-store-authority"
    )
    first_path = tmp_path / "epoch-a.sqlite"
    second_path = tmp_path / "epoch-b.sqlite"
    first = VerifiedDurableEconomicPublisherV1.create(
        first_path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    source = first.head

    # Act: Mallory tries to create an independent sequence-zero head beside it.
    with pytest.raises(ValueError, match="current authority mismatch"):
        VerifiedDurableEconomicPublisherV1.create(
            second_path,
            admission,
            _bound_receipt_verifier_v1(candidate)[0],
        )
    committed = first.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: only the store named by the authority can publish or be created.
    assert not second_path.exists()
    assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert first.head == committed.committed_epoch
    first.close()


def test_restored_pre_revocation_authority_remains_a_release_blocker(
    tmp_path: Path,
) -> None:
    # Arrange: an old publisher and a recoverable copy of its active authority.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"rollback-resurrection-blocker"
    )
    path = tmp_path / "rollback-resurrection.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    publisher.close()
    authority_path = authority_journal_path_for_epoch_v1(path)
    active_authority_bytes = authority_path.read_bytes()
    authority = GlobalEconomicAuthorityJournalV1.open(authority_path)
    revoked = authority._commit_successor_for_unmounted_control_plane_v1(
        authority.head.revoked_successor(),
        authority._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )
    authority.close()

    # Act: restoring both authority bytes and the old publisher resurrects it.
    authority_path.write_bytes(active_authority_bytes)
    resurrected = VerifiedDurableEconomicPublisherV1.open(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    published = resurrected.publish_economic_epoch(
        expected_source=resurrected.head,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: this reproducible disaster state keeps rollback resistance open.
    assert revoked.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    assert published.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    resurrected.close()


def test_separate_migration_commit_leaves_old_publisher_active_release_blocker(
    tmp_path: Path,
) -> None:
    # Arrange: one old publisher and a migration bundle derived from its genesis.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"migration-atomicity-blocker"
    )
    publisher_path = tmp_path / "old-publisher-after-migration.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        publisher_path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    genesis = prepare_durable_economic_initial_state_bundle_v1(
        admission,
        source_head=None,
    )
    _, _, migration_admission = _migration_admission_for_source_head(
        candidate.profile,
        candidate.pre_state,
    )
    migration = prepare_durable_economic_initial_state_bundle_v1(
        migration_admission,
        source_head=genesis.head,
    )
    migration_journal = GlobalEconomicMigrationJournalV1.create(
        tmp_path / "separate-migration.sqlite",
        genesis,
    )

    # Act: migration commits in its separate store, then the old writer publishes.
    migrated = migration_journal.commit_migration(
        migration,
        migration_journal.acquire_cas_head_token(),
    )
    published = publisher.publish_economic_epoch(
        expected_source=publisher.head,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: both commits succeed, proving atomic migration retirement is open.
    assert migrated.status is DurableEconomicCommitStatusV1.COMMITTED
    assert published.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    migration_journal.close()
    publisher.close()


def test_old_store_cannot_reopen_after_shared_profile_rotation(
    tmp_path: Path,
) -> None:
    # Arrange: one retained profile-P0 epoch store and its shared authority head.
    admission, candidate, _ = _publisher_fixture_v1()
    path = tmp_path / "old-profile-after-rotation.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    publisher.close()
    authority = GlobalEconomicAuthorityJournalV1.open(
        authority_journal_path_for_epoch_v1(path)
    )
    current = authority.head
    rotated = replace(
        current,
        generation=current.generation + 1,
        activation_id="0x" + "a1" * 32,
        profile_root="0x" + "a2" * 32,
        writer_epoch=current.writer_epoch + 1,
    )

    # Act: the shared control head advances to a distinct profile generation.
    outcome = authority._commit_successor_for_unmounted_control_plane_v1(
        rotated,
        authority._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )
    authority.close()

    # Assert: P0 cannot reopen even though its own epoch bytes are intact.
    assert outcome.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    with pytest.raises(ValueError, match="current authority mismatch"):
        VerifiedDurableEconomicPublisherV1.open(
            path,
            admission,
            _bound_receipt_verifier_v1(candidate)[0],
        )


def test_inflight_verification_cannot_publish_after_authority_revocation(
    tmp_path: Path,
) -> None:
    # Arrange: Mallory's epoch verification pauses after the authority snapshot.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"inflight-before-revocation"
    )
    entered = Event()
    release = Event()

    class BlockingEpochVerifier(_RecordingBackend):
        def verify_succinct_receipt(
            self,
            receipt_bytes: bytes,
            *,
            expected_image_id: str,
            expected_journal_bytes: bytes,
        ) -> object:
            result = super().verify_succinct_receipt(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )
            if receipt_bytes == candidate.receipt_bytes:
                entered.set()
                if not release.wait(timeout=10):
                    raise RuntimeError("test verifier release timed out")
            return result

    path = tmp_path / "inflight-revocation.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(
            candidate,
            BlockingEpochVerifier(),
        )[0],
    )
    source = publisher.head
    outcomes: list[VerifiedDurableEconomicPublishOutcomeV1] = []

    def publish_inflight() -> None:
        outcomes.append(
            publisher.publish_economic_epoch(
                expected_source=source,
                candidate=candidate,
                body_and_state=body,
            )
        )

    thread = Thread(target=publish_inflight)
    thread.start()
    assert entered.wait(timeout=10)

    # Act: a separate control connection revokes authority before verification returns.
    authority = GlobalEconomicAuthorityJournalV1.open(
        authority_journal_path_for_epoch_v1(path)
    )
    revoked = authority._commit_successor_for_unmounted_control_plane_v1(
        authority.head.revoked_successor(),
        authority._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )
    authority.close()
    release.set()
    thread.join(timeout=10)

    # Assert: the inner durable CAS observes revocation and publishes no epoch.
    assert not thread.is_alive()
    assert revoked.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    assert len(outcomes) == 1
    assert outcomes[0].status is DurableEconomicEpochCommitStatusV1.AUTHORITY_STALE
    assert outcomes[0].published_epoch is None
    assert publisher.head == source
    publisher.close()


def test_open_rejects_a_different_verified_activation(
    tmp_path: Path,
) -> None:
    # Arrange: a journal is created from one exact genesis admission.
    admission, candidate, _ = _publisher_fixture_v1()
    path = tmp_path / "wrong-activation.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    publisher.close()
    different_state = replace(
        candidate.pre_state,
        history_root="0x" + "ef" * 32,
    )
    different_admission = _initial_state_admission(
        candidate.profile,
        different_state,
    )

    # Act and assert: restart must reproduce the byte-identical durable activation.
    with pytest.raises(ValueError, match="activation"):
        VerifiedDurableEconomicPublisherV1.open(
            path,
            different_admission,
            _bound_receipt_verifier_v1(candidate)[0],
        )


def test_expected_source_rejects_boolean_sequence_alias(
    tmp_path: Path,
) -> None:
    # Arrange: Python's bool/int alias is injected past the frozen dataclass guard.
    admission, candidate, body = _publisher_fixture_v1()
    publisher = VerifiedDurableEconomicPublisherV1.create(
        tmp_path / "boolean-sequence.sqlite",
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    source = publisher.head
    object.__setattr__(source, "sequence", False)

    # Act and assert: the boundary reconstructs exact typed source coordinates.
    with pytest.raises(TypeError, match="sequence"):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    assert publisher.head.sequence == 0
    publisher.close()


def test_direct_publisher_construction_is_rejected() -> None:
    # Arrange: Mallory has caller-constructible placeholders for every argument.
    foreign_mint = object()

    # Act and assert: only create/open may construct the authority boundary.
    with pytest.raises(TypeError, match="factory-constructed"):
        VerifiedDurableEconomicPublisherV1(
            foreign_mint,
            object(),
            object(),
            object(),
            object(),
            "0x" + "00" * 32,
        )


def test_publication_api_has_no_caller_supplied_authority_objects() -> None:
    # Arrange: the method signature is part of the authority-boundary contract.
    signature = inspect.signature(
        VerifiedDurableEconomicPublisherV1.publish_economic_epoch
    )

    # Act: enumerate every caller-controlled publication input.
    parameter_names = tuple(signature.parameters)

    # Assert: witnesses, records, bundles, tokens, and journals remain internal.
    assert parameter_names == (
        "self",
        "expected_source",
        "candidate",
        "body_and_state",
    )
    assert "journal" not in VerifiedDurableEconomicPublisherV1.__dict__
    assert "commit_epoch" not in GlobalEconomicEpochJournalV1.__dict__
    assert "verify_economic_epoch" not in VerifiedDurableEconomicPublisherV1.__dict__
    assert "commit_verified_economic_epoch" not in (
        VerifiedDurableEconomicPublisherV1.__dict__
    )

    # Assert: create/open derive the shared authority path and expected head.
    assert tuple(
        inspect.signature(VerifiedDurableEconomicPublisherV1.create).parameters
    ) == ("path", "initial_state_admission", "receipt_verifier")
    assert tuple(
        inspect.signature(VerifiedDurableEconomicPublisherV1.open).parameters
    ) == ("path", "initial_state_admission", "receipt_verifier")
