"""Authority, replay, and concurrency evidence for the durable publisher."""

from __future__ import annotations

import hashlib
import inspect
import sqlite3
from dataclasses import replace
from pathlib import Path
from threading import Event, Thread
from typing import Any, cast

import pytest

import src.integration.global_economic_authority_journal_v1 as authority_journal_module
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
from src.core.global_economic_monotonic_anchor_v1 import (
    GlobalEconomicMonotonicAnchorV1,
    decode_global_economic_monotonic_anchor_v1,
)
from src.core.global_economic_proof_v1 import EconomicEpochReceiptCandidateV1
from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    GlobalEconomicStateV1,
    hash_global_v1,
)
from src.integration.global_economic_authority_journal_v1 import (
    GlobalEconomicAuthorityBootstrapBusyV1,
    GlobalEconomicAuthorityCommitStatusV1,
    GlobalEconomicAuthorityJournalV1,
    authority_journal_path_for_epoch_v1,
)
from src.integration.global_economic_commit_v1 import EconomicEpochBodyAndStateV1
from src.integration.global_economic_durable_publisher_v1 import (
    GlobalEconomicAnchorAdvanceIndeterminateV1,
    GlobalEconomicRollbackDetectedV1,
    VerifiedDurableEconomicPublisherV1,
    VerifiedDurableEconomicPublishOutcomeV1,
)
from src.integration.global_economic_epoch_journal_v1 import (
    DurableEconomicEpochCommitStatusV1,
    DurableEconomicEpochWriteCapabilityV1,
    GlobalEconomicEpochJournalV1,
    _DurableEconomicEpochCommitFaultV1,
    _SimulatedDurableEconomicEpochCrashV1,
)
from src.integration.global_economic_migration_journal_v1 import (
    DurableEconomicCommitStatusV1,
    GlobalEconomicMigrationJournalV1,
)
from src.integration.global_economic_monotonic_anchor_v1 import (
    GlobalEconomicMonotonicAnchorBackendEvidenceStatusV1,
    GlobalEconomicMonotonicAnchorBackendReleaseV1,
    GlobalEconomicMonotonicAnchorBackendStatusV1,
    bind_global_economic_monotonic_anchor_backend_v1,
    build_global_economic_monotonic_anchor_v1,
    global_economic_monotonic_anchor_backend_implementation_root_v1,
    global_economic_monotonic_anchor_backend_protocol_root_v1,
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


def _publisher_candidate_v1(
    *,
    receipt_bytes: bytes,
    verifier_registry_root: str,
    pre_state: GlobalEconomicStateV1 | None = None,
    nonce_start: int = 1,
) -> tuple[EconomicEpochReceiptCandidateV1, EconomicEpochBodyAndStateV1]:
    candidate = _epoch_admission_fixture(
        1,
        verifier_registry_root=verifier_registry_root,
        pre_state=pre_state,
        nonce_start=nonce_start,
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
    return (
        replace(
            candidate,
            certificate=certificate,
            receipt_bytes=receipt_bytes,
            expected_body_commitment=body.body_commitment,
        ),
        body,
    )


def _publisher_fixture_v1(*, receipt_bytes: bytes = b"durable-publisher-epoch"):
    manifest = _receipt_verifier_manifest_v1()
    registry = EconomicReceiptVerifierRegistryV1((_release(manifest),))
    candidate, body = _publisher_candidate_v1(
        receipt_bytes=receipt_bytes,
        verifier_registry_root=registry.registry_root,
    )
    admission = _initial_state_admission(candidate.profile, candidate.pre_state)
    return admission, candidate, body


class _MemoryMonotonicAnchorBackendV1:
    def __init__(self, anchor: GlobalEconomicMonotonicAnchorV1) -> None:
        self.current = anchor.canonical_bytes
        self.fail_next_cas = False
        self.reject_next_cas = False

    def read_current_anchor(self, anchor_namespace_root: str) -> bytes:
        return self.current

    def compare_and_set_anchor(
        self,
        anchor_namespace_root: str,
        expected_anchor_root: str,
        successor_anchor_bytes: bytes,
    ) -> bool:
        if self.fail_next_cas:
            self.fail_next_cas = False
            raise OSError("simulated external anchor outage after local commit")
        if self.reject_next_cas:
            self.reject_next_cas = False
            return False
        current = decode_global_economic_monotonic_anchor_v1(self.current)
        if current.anchor_root != expected_anchor_root:
            return False
        self.current = successor_anchor_bytes
        return True


class _LostAckMonotonicAnchorBackendV1(_MemoryMonotonicAnchorBackendV1):
    def __init__(self, anchor: GlobalEconomicMonotonicAnchorV1) -> None:
        super().__init__(anchor)
        self.fail_post_cas_read = False

    def read_current_anchor(self, anchor_namespace_root: str) -> bytes:
        if self.fail_post_cas_read:
            self.fail_post_cas_read = False
            raise OSError("simulated lost acknowledgment after external anchor write")
        return super().read_current_anchor(anchor_namespace_root)

    def compare_and_set_anchor(
        self,
        anchor_namespace_root: str,
        expected_anchor_root: str,
        successor_anchor_bytes: bytes,
    ) -> bool:
        advanced = super().compare_and_set_anchor(
            anchor_namespace_root,
            expected_anchor_root,
            successor_anchor_bytes,
        )
        if advanced:
            self.fail_post_cas_read = True
        return advanced


def _bound_monotonic_anchor_backend_v1(
    anchor: GlobalEconomicMonotonicAnchorV1,
    backend: _MemoryMonotonicAnchorBackendV1,
):
    artifact = b"publisher-monotonic-anchor-backend-v1"
    release = GlobalEconomicMonotonicAnchorBackendReleaseV1.build(
        semantic_version="1.0.0-shadow",
        implementation_root=(
            global_economic_monotonic_anchor_backend_implementation_root_v1(
                artifact
            )
        ),
        specification_root=_root(930),
        source_root=_root(931),
        toolchain_root=_root(932),
        evidence_manifest_root=_root(933),
        backend_protocol_root=(
            global_economic_monotonic_anchor_backend_protocol_root_v1()
        ),
        status=GlobalEconomicMonotonicAnchorBackendStatusV1.SHADOW,
        evidence_statuses=tuple(GlobalEconomicMonotonicAnchorBackendEvidenceStatusV1),
    )
    return bind_global_economic_monotonic_anchor_backend_v1(
        release=release,
        measured_artifact_bytes=artifact,
        anchor_namespace_root=anchor.anchor_namespace_root,
        chain_id=anchor.chain_id,
        deployment_root=anchor.deployment_root,
        backend=backend,
    )


def _anchor_for_path_v1(
    path: Path,
    *,
    anchor_sequence: int,
    previous_anchor_root: str,
) -> GlobalEconomicMonotonicAnchorV1:
    with GlobalEconomicAuthorityJournalV1.open(
        authority_journal_path_for_epoch_v1(path)
    ) as authority_journal:
        authority = authority_journal.head
    with GlobalEconomicEpochJournalV1.open(path) as epoch_journal:
        publication = epoch_journal.head
    return build_global_economic_monotonic_anchor_v1(
        anchor_namespace_root=_root(929),
        anchor_sequence=anchor_sequence,
        previous_anchor_root=previous_anchor_root,
        authority=authority,
        publication=publication,
    )


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


@pytest.mark.parametrize(
    "reserved_candidate_name",
    (
        ".global-economic-authority-bootstrap-v1.sqlite",
        ".global-economic-epoch-bootstrap-v1.sqlite",
    ),
)
def test_verified_publisher_create_recovers_post_link_bootstrap_crash(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    reserved_candidate_name: str,
) -> None:
    # Arrange: crash after either authority or epoch candidate has been linked
    # to its final name but before the reserved candidate can be removed.
    admission, candidate, _ = _publisher_fixture_v1(
        receipt_bytes=reserved_candidate_name.encode("ascii")
    )
    path = tmp_path / "post-link-create-recovery.sqlite"
    authority_path = authority_journal_path_for_epoch_v1(path)
    reserved_candidate = tmp_path / reserved_candidate_name
    final_path = (
        authority_path
        if "authority" in reserved_candidate_name
        else path
    )
    original_unlink = authority_journal_module.os.unlink

    def faulting_unlink(
        target: str | bytes | Path,
        *args: object,
        **kwargs: object,
    ) -> None:
        if Path(target).name == reserved_candidate_name:
            raise OSError("simulated publisher bootstrap crash after link")
        original_unlink(target, *args, **kwargs)

    monkeypatch.setattr(authority_journal_module.os, "unlink", faulting_unlink)

    # Act: first construction loses progress at the linked-name boundary.
    with pytest.raises(OSError, match="simulated publisher bootstrap crash"):
        VerifiedDurableEconomicPublisherV1.create(
            path,
            admission,
            _bound_receipt_verifier_v1(candidate)[0],
        )
    monkeypatch.setattr(authority_journal_module.os, "unlink", original_unlink)

    # Assert: an exact verified retry validates the linked inode, completes its
    # install, and returns the unique sequence-zero publisher.
    assert final_path.exists()
    assert reserved_candidate.exists()
    assert final_path.stat().st_ino == reserved_candidate.stat().st_ino
    recovered = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    assert recovered.head.sequence == 0
    recovered.close()
    assert not reserved_candidate.exists()
    assert final_path.stat().st_nlink == 1


def test_concurrent_verified_publisher_create_has_one_install_and_typed_busy(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: pause one publisher while it owns the shared directory bootstrap.
    admission, candidate, _ = _publisher_fixture_v1(
        receipt_bytes=b"concurrent-publisher-create"
    )
    path = tmp_path / "concurrent-publisher-create.sqlite"
    original_initialize = authority_journal_module._initialize_authority_candidate_v1
    entered = Event()
    release = Event()

    def blocking_initialize(candidate_path: Path, initial_head: Any) -> None:
        entered.set()
        if not release.wait(timeout=10):
            raise RuntimeError("test publisher bootstrap release timed out")
        original_initialize(candidate_path, initial_head)

    monkeypatch.setattr(
        authority_journal_module,
        "_initialize_authority_candidate_v1",
        blocking_initialize,
    )
    publishers: list[VerifiedDurableEconomicPublisherV1] = []
    errors: list[BaseException] = []

    def create() -> None:
        try:
            publishers.append(
                VerifiedDurableEconomicPublisherV1.create(
                    path,
                    admission,
                    _bound_receipt_verifier_v1(candidate)[0],
                )
            )
        except BaseException as exc:
            errors.append(exc)

    first = Thread(target=create)
    second = Thread(target=create)

    # Act: a second same-profile installer contests the live bootstrap.
    first.start()
    assert entered.wait(timeout=10)
    second.start()
    second.join(timeout=20)
    release.set()
    first.join(timeout=20)

    # Assert: one install succeeds and contention has one closed exception type.
    assert not first.is_alive()
    assert not second.is_alive()
    assert len(errors) == 1
    assert type(errors[0]) is GlobalEconomicAuthorityBootstrapBusyV1
    assert len(publishers) == 1
    assert publishers[0].head.sequence == 0
    for publisher in publishers:
        publisher.close()


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


def test_monotonic_anchor_rejects_restored_pre_revocation_authority_bytes(
    tmp_path: Path,
) -> None:
    # Arrange: an externally retained checkpoint advances to the revoked head.
    admission, candidate, _ = _publisher_fixture_v1(
        receipt_bytes=b"anchored-authority-rollback"
    )
    path = tmp_path / "anchored-authority-rollback.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    publisher.close()
    authority_path = authority_journal_path_for_epoch_v1(path)
    active_bytes = authority_path.read_bytes()
    active_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    with GlobalEconomicAuthorityJournalV1.open(authority_path) as authority:
        revoked = authority._commit_successor_for_unmounted_control_plane_v1(
            authority.head.revoked_successor(),
            authority._acquire_cas_head_token_for_unmounted_control_plane_v1(),
        )
    revoked_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=1,
        previous_anchor_root=active_anchor.anchor_root,
    )
    backend = _MemoryMonotonicAnchorBackendV1(revoked_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(revoked_anchor, backend)

    # Act: Mallory restores the valid generation-zero authority database.
    authority_path.write_bytes(active_bytes)
    restored_bytes = authority_path.read_bytes()

    # Assert: the external authority coordinates reject before a writer reopens.
    assert revoked.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    with pytest.raises(ValueError, match="monotonic anchor"):
        VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
            path,
            admission,
            _bound_receipt_verifier_v1(candidate)[0],
            bound_anchor,
        )
    assert authority_path.read_bytes() == restored_bytes


def test_monotonic_anchor_rejects_epoch_only_rollback_without_mutation(
    tmp_path: Path,
) -> None:
    # Arrange: the external checkpoint observes the first committed epoch.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-epoch-rollback"
    )
    path = tmp_path / "anchored-epoch-rollback.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    sequence_zero_bytes = path.read_bytes()
    committed = publisher.publish_economic_epoch(
        expected_source=publisher.head,
        candidate=candidate,
        body_and_state=body,
    )
    publisher.close()
    committed_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=1,
        previous_anchor_root=_root(934),
    )
    backend = _MemoryMonotonicAnchorBackendV1(committed_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(committed_anchor, backend)

    # Act: restore only the sequence-zero epoch bytes.
    path.write_bytes(sequence_zero_bytes)
    restored_bytes = path.read_bytes()

    # Assert: no duplicate writer can reopen under the newer external checkpoint.
    assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    with pytest.raises(ValueError, match="monotonic anchor"):
        VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
            path,
            admission,
            _bound_receipt_verifier_v1(candidate)[0],
            bound_anchor,
        )
    assert path.read_bytes() == restored_bytes


def test_monotonic_anchor_advances_after_one_durable_epoch_commit(
    tmp_path: Path,
) -> None:
    # Arrange: an independently stored checkpoint exactly matches genesis.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-normal-publication"
    )
    path = tmp_path / "anchored-normal-publication.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    backend = _MemoryMonotonicAnchorBackendV1(genesis_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    publisher = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )

    # Act
    committed = publisher.publish_economic_epoch(
        expected_source=publisher.head,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: success is returned only after the external CAS observes the tip.
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert observed.publication_id == committed.committed_epoch.publication_id
    assert observed.publication_sequence == 1
    assert observed.previous_anchor_root == genesis_anchor.anchor_root
    publisher.close()


def test_post_commit_anchor_outage_recovers_only_by_exact_epoch_retry(
    tmp_path: Path,
) -> None:
    # Arrange: the backend fails once after the local epoch linearization point.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-post-commit-recovery"
    )
    path = tmp_path / "anchored-post-commit-recovery.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    backend = _MemoryMonotonicAnchorBackendV1(genesis_anchor)
    backend.fail_next_cas = True
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    first = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )
    source = first.head

    # Act: local commit succeeds, external CAS is indeterminate, then exact retry.
    with pytest.raises(GlobalEconomicAnchorAdvanceIndeterminateV1):
        first.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    assert first.head.sequence == 1
    assert decode_global_economic_monotonic_anchor_v1(backend.current) == genesis_anchor
    first.close()
    recovering = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )
    retried = recovering.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: one history remains and the external checkpoint catches up exactly.
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert observed.publication_id == retried.committed_epoch.publication_id
    assert observed.publication_sequence == 1
    assert recovering.head == retried.committed_epoch
    recovering.close()


def test_post_commit_stale_anchor_cas_is_typed_indeterminate_and_no_double_commit(
    tmp_path: Path,
) -> None:
    # Arrange: the external compare-and-set reports a stale expected root.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-stale-cas-recovery"
    )
    path = tmp_path / "anchored-stale-cas-recovery.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    backend = _MemoryMonotonicAnchorBackendV1(genesis_anchor)
    backend.reject_next_cas = True
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    publisher = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )
    source = publisher.head

    # Act
    with pytest.raises(GlobalEconomicAnchorAdvanceIndeterminateV1):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    recovered = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: retry observes one committed row and advances only the anchor.
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert recovered.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert publisher.head.sequence == observed.publication_sequence == 1
    assert publisher.head.publication_id == observed.publication_id
    publisher.close()


def test_post_commit_anchor_lost_ack_reconciles_the_exact_successor_on_retry(
    tmp_path: Path,
) -> None:
    # Arrange: the external CAS writes its successor, then its confirming read fails.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-post-commit-lost-ack"
    )
    path = tmp_path / "anchored-post-commit-lost-ack.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    backend = _LostAckMonotonicAnchorBackendV1(genesis_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    publisher = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )
    source = publisher.head

    # Act: the first call loses its acknowledgment after both durable writes;
    # Alice submits only the byte-identical epoch from the exact predecessor.
    with pytest.raises(GlobalEconomicAnchorAdvanceIndeterminateV1):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    retried = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: the observed sole successor reconciles without another value write.
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert publisher.head.sequence == observed.publication_sequence == 1
    assert publisher.head.publication_id == observed.publication_id
    publisher.close()


def test_changed_external_anchor_rejects_unless_it_is_the_exact_local_successor(
    tmp_path: Path,
) -> None:
    # Arrange: Mallory advances only the external sequence while local durable
    # state remains at genesis, creating no valid local successor relation.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-divergent-external-successor"
    )
    path = tmp_path / "anchored-divergent-external-successor.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    backend = _MemoryMonotonicAnchorBackendV1(genesis_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    receipt_verifier, receipt_backend = _bound_receipt_verifier_v1(candidate)
    publisher = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        receipt_verifier,
        bound_anchor,
    )
    calls_before = tuple(receipt_backend.calls)
    source = publisher.head
    local_bytes = path.read_bytes()
    divergent = replace(
        genesis_anchor,
        anchor_sequence=1,
        previous_anchor_root=genesis_anchor.anchor_root,
    )
    backend.current = divergent.canonical_bytes

    # Act / Assert: divergence rejects before proof work or local publication.
    with pytest.raises(GlobalEconomicRollbackDetectedV1):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    assert tuple(receipt_backend.calls) == calls_before
    assert publisher.head == source
    assert path.read_bytes() == local_bytes
    publisher.close()


def test_exhausted_anchor_sequence_rejects_before_proof_or_local_commit(
    tmp_path: Path,
) -> None:
    # Arrange: V1 has no representable anchor after the exact u64 maximum.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-exhausted-sequence"
    )
    path = tmp_path / "anchored-exhausted-sequence.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    exhausted_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=(1 << 64) - 1,
        previous_anchor_root=_root(934),
    )
    backend = _MemoryMonotonicAnchorBackendV1(exhausted_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(exhausted_anchor, backend)
    receipt_verifier, receipt_backend = _bound_receipt_verifier_v1(candidate)
    publisher = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        receipt_verifier,
        bound_anchor,
    )
    calls_before = tuple(receipt_backend.calls)
    source = publisher.head
    local_bytes = path.read_bytes()

    # Act / Assert: capacity rejects before proof verification or value mutation.
    with pytest.raises(ValueError, match="cannot advance"):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    assert tuple(receipt_backend.calls) == calls_before
    assert publisher.head == source
    assert path.read_bytes() == local_bytes
    assert decode_global_economic_monotonic_anchor_v1(backend.current) == (
        exhausted_anchor
    )
    publisher.close()


def test_post_commit_local_anchor_projection_fault_is_indeterminate_and_retryable(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: the local commit succeeds, then the first post-commit projection
    # of authority, tip, and predecessor fails before the external CAS.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-post-commit-local-projection-fault"
    )
    path = tmp_path / "anchored-post-commit-local-projection-fault.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    backend = _MemoryMonotonicAnchorBackendV1(genesis_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    publisher = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )
    source = publisher.head
    original = GlobalEconomicEpochJournalV1._anchor_heads_for_verified_publisher_v1
    fail_once = True

    def fail_first_post_commit_projection(
        journal: GlobalEconomicEpochJournalV1,
        write_capability: DurableEconomicEpochWriteCapabilityV1,
    ):
        nonlocal fail_once
        heads = original(journal, write_capability)
        if fail_once and heads[1].sequence == 1:
            fail_once = False
            raise RuntimeError("simulated post-commit local anchor projection fault")
        return heads

    monkeypatch.setattr(
        GlobalEconomicEpochJournalV1,
        "_anchor_heads_for_verified_publisher_v1",
        fail_first_post_commit_projection,
    )

    # Act: one local row commits before the projection fault, then Alice retries
    # the byte-identical epoch from the exact predecessor.
    with pytest.raises(GlobalEconomicAnchorAdvanceIndeterminateV1):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    retried = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: the retry advances only the anchor and cannot double-publish value.
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert publisher.head.sequence == observed.publication_sequence == 1
    assert publisher.head.publication_id == observed.publication_id
    publisher.close()


def test_concurrent_exact_retry_arms_recovery_before_projection_fault(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: Alice pauses after anchor/session admission. Bob commits the same
    # epoch locally, but the external CAS is unavailable. Alice then observes an
    # exact ALREADY_COMMITTED result before her post-commit projection fails.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-concurrent-exact-retry-projection-fault"
    )
    path = tmp_path / "anchored-concurrent-exact-retry-projection-fault.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    backend = _MemoryMonotonicAnchorBackendV1(genesis_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
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

    alice = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate, BlockingEpochVerifier())[0],
        bound_anchor,
    )
    bob = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )
    source = alice.head
    alice_errors: list[BaseException] = []

    def publish_alice() -> None:
        try:
            alice.publish_economic_epoch(
                expected_source=source,
                candidate=candidate,
                body_and_state=body,
            )
        except BaseException as exc:
            alice_errors.append(exc)

    thread = Thread(target=publish_alice)
    thread.start()
    assert entered.wait(timeout=10)
    backend.fail_next_cas = True
    with pytest.raises(GlobalEconomicAnchorAdvanceIndeterminateV1):
        bob.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    original = GlobalEconomicEpochJournalV1._anchor_heads_for_verified_publisher_v1
    fail_once = True

    def fail_first_already_committed_projection(
        journal: GlobalEconomicEpochJournalV1,
        write_capability: DurableEconomicEpochWriteCapabilityV1,
    ):
        nonlocal fail_once
        heads = original(journal, write_capability)
        if fail_once and heads[1].sequence == 1:
            fail_once = False
            raise RuntimeError("simulated exact-retry projection fault")
        return heads

    monkeypatch.setattr(
        GlobalEconomicEpochJournalV1,
        "_anchor_heads_for_verified_publisher_v1",
        fail_first_already_committed_projection,
    )

    # Act: Alice's local exact retry succeeds, then projection loses its result.
    release.set()
    thread.join(timeout=20)
    assert not thread.is_alive()
    assert len(alice_errors) == 1
    assert type(alice_errors[0]) is GlobalEconomicAnchorAdvanceIndeterminateV1
    retried = alice.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: the same-process retry advances only the anchor and adds no epoch.
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert alice.head.sequence == observed.publication_sequence == 1
    alice.close()
    bob.close()


def test_lower_journal_commit_lost_ack_becomes_typed_anchor_recovery(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: SQLite commits the epoch, then its journal acknowledgment is lost
    # before the publisher receives a DurableEconomicEpochCommitOutcomeV1.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-lower-journal-commit-lost-ack"
    )
    path = tmp_path / "anchored-lower-journal-commit-lost-ack.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    backend = _MemoryMonotonicAnchorBackendV1(genesis_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    publisher = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )
    source = publisher.head

    def commit_then_lose_ack(
        journal: GlobalEconomicEpochJournalV1,
        epoch: Any,
        cas_token: Any,
        write_capability: DurableEconomicEpochWriteCapabilityV1,
    ):
        return journal._commit_epoch_with_fault_for_test_v1(
            epoch,
            cas_token,
            _DurableEconomicEpochCommitFaultV1.AFTER_COMMIT_BEFORE_ACK,
            write_capability,
        )

    monkeypatch.setattr(
        GlobalEconomicEpochJournalV1,
        "_commit_epoch_from_verified_publisher_v1",
        commit_then_lose_ack,
    )

    # Act: the publisher classifies the now-durable one-step relation, then the
    # normal exact retry runs after fault injection is removed.
    with pytest.raises(GlobalEconomicAnchorAdvanceIndeterminateV1):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    monkeypatch.undo()
    retried = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: one local epoch exists and its exact retry advances only the anchor.
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert publisher.head.sequence == observed.publication_sequence == 1
    publisher.close()


def test_external_forward_tip_without_matching_local_history_fails_closed(
    tmp_path: Path,
) -> None:
    # Arrange: Alice's epoch-one CAS succeeds, then a different writer advances
    # the external source to epoch two without the matching local epoch-two row.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-forward-tip-without-local-history"
    )
    path = tmp_path / "anchored-forward-tip-without-local-history.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )

    class ForwardTipAfterCasBackend(_MemoryMonotonicAnchorBackendV1):
        def compare_and_set_anchor(
            self,
            anchor_namespace_root: str,
            expected_anchor_root: str,
            successor_anchor_bytes: bytes,
        ) -> bool:
            advanced = super().compare_and_set_anchor(
                anchor_namespace_root,
                expected_anchor_root,
                successor_anchor_bytes,
            )
            if advanced:
                installed = decode_global_economic_monotonic_anchor_v1(self.current)
                self.current = replace(
                    installed,
                    anchor_sequence=installed.anchor_sequence + 1,
                    previous_anchor_root=installed.anchor_root,
                    publication_id=_root(940),
                    publication_sequence=installed.publication_sequence + 1,
                    height=installed.height + 1,
                    state_root=_root(941),
                    commit_id=_root(942),
                    certificate_root=_root(943),
                ).canonical_bytes
            return advanced

    backend = ForwardTipAfterCasBackend(genesis_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    publisher = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )
    source = publisher.head

    # Act: epoch one commits locally, but adoption of the observed epoch-two
    # anchor requires an exact complete local epoch-two authority/publication tip.
    with pytest.raises(GlobalEconomicAnchorAdvanceIndeterminateV1):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )

    # Assert: the mismatched external tip is never adopted as local authority,
    # and subsequent value movement remains closed for this publisher session.
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert publisher.head.sequence == 1
    assert observed.publication_sequence == 2
    with pytest.raises(GlobalEconomicRollbackDetectedV1):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    publisher.close()


def test_concurrent_forward_tip_with_matching_local_history_is_adopted(
    tmp_path: Path,
) -> None:
    # Arrange: Alice prepares epoch one. Bob's valid epoch two is derived from
    # Alice's exact post-state and runs after Alice's external CAS linearizes.
    admission, first_candidate, first_body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-positive-forward-epoch-one"
    )
    second_candidate, second_body = _publisher_candidate_v1(
        receipt_bytes=b"anchored-positive-forward-epoch-two",
        verifier_registry_root=first_candidate.profile.verifier_registry_root,
        pre_state=first_candidate.post_state,
        nonce_start=2,
    )
    path = tmp_path / "anchored-positive-forward-tip.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(first_candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )

    class ConcurrentForwardTipBackend(_MemoryMonotonicAnchorBackendV1):
        def __init__(self, anchor: GlobalEconomicMonotonicAnchorV1) -> None:
            super().__init__(anchor)
            self.after_first_cas: Any = None
            self.first_cas_completed = False

        def compare_and_set_anchor(
            self,
            anchor_namespace_root: str,
            expected_anchor_root: str,
            successor_anchor_bytes: bytes,
        ) -> bool:
            advanced = super().compare_and_set_anchor(
                anchor_namespace_root,
                expected_anchor_root,
                successor_anchor_bytes,
            )
            if advanced and not self.first_cas_completed:
                self.first_cas_completed = True
                if self.after_first_cas is None:
                    raise RuntimeError("concurrent forward callback is absent")
                self.after_first_cas()
            return advanced

    backend = ConcurrentForwardTipBackend(genesis_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    second_outcomes: list[VerifiedDurableEconomicPublishOutcomeV1] = []

    def publish_second_epoch() -> None:
        bob = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
            path,
            admission,
            _bound_receipt_verifier_v1(second_candidate)[0],
            bound_anchor,
        )
        try:
            second_outcomes.append(
                bob.publish_economic_epoch(
                    expected_source=bob.head,
                    candidate=second_candidate,
                    body_and_state=second_body,
                )
            )
        finally:
            bob.close()

    backend.after_first_cas = publish_second_epoch
    alice = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(first_candidate)[0],
        bound_anchor,
    )

    # Act: Alice confirms epoch one after Bob has advanced the same complete
    # local and external histories to epoch two.
    first_outcome = alice.publish_economic_epoch(
        expected_source=alice.head,
        candidate=first_candidate,
        body_and_state=first_body,
    )

    # Assert: Alice adopts the exact current tip and the journal contains each
    # canonical epoch bundle once.
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert first_outcome.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert len(second_outcomes) == 1
    assert second_outcomes[0].status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert alice.head.sequence == observed.publication_sequence == 2
    with sqlite3.connect(path) as connection:
        assert connection.execute("SELECT COUNT(*) FROM economic_epochs").fetchone() == (
            2,
        )
    alice.close()


def test_post_commit_control_flow_interruption_arms_same_process_recovery(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: SQLite commits one epoch, then a process-control exception crosses
    # the lower journal acknowledgment boundary.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"anchored-post-commit-keyboard-interrupt"
    )
    path = tmp_path / "anchored-post-commit-keyboard-interrupt.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    backend = _MemoryMonotonicAnchorBackendV1(genesis_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    publisher = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )
    source = publisher.head

    def commit_then_interrupt(
        journal: GlobalEconomicEpochJournalV1,
        epoch: Any,
        cas_token: Any,
        write_capability: DurableEconomicEpochWriteCapabilityV1,
    ):
        try:
            journal._commit_epoch_with_fault_for_test_v1(
                epoch,
                cas_token,
                _DurableEconomicEpochCommitFaultV1.AFTER_COMMIT_BEFORE_ACK,
                write_capability,
            )
        except RuntimeError as committed_fault:
            raise KeyboardInterrupt from committed_fault
        raise RuntimeError("post-commit fault injection unexpectedly returned")

    monkeypatch.setattr(
        GlobalEconomicEpochJournalV1,
        "_commit_epoch_from_verified_publisher_v1",
        commit_then_interrupt,
    )

    # Act: preserve KeyboardInterrupt for the caller, then retry the exact epoch
    # in the same publisher after removing the injected lower-journal fault.
    with pytest.raises(KeyboardInterrupt):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    monkeypatch.undo()
    retried = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: the control-flow exception is not normalized, while exact recovery
    # advances only the external anchor and inserts no duplicate epoch.
    observed = decode_global_economic_monotonic_anchor_v1(backend.current)
    assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert publisher.head.sequence == observed.publication_sequence == 1
    publisher.close()


@pytest.mark.parametrize(
    "fault",
    (
        _DurableEconomicEpochCommitFaultV1.AFTER_BEGIN,
        _DurableEconomicEpochCommitFaultV1.AFTER_INSERT,
        _DurableEconomicEpochCommitFaultV1.AFTER_HEAD_UPDATE_BEFORE_COMMIT,
    ),
)
def test_lower_journal_precommit_fault_preserves_error_and_no_effect(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    fault: _DurableEconomicEpochCommitFaultV1,
) -> None:
    # Arrange: inject each lower-journal crash boundary before SQLite commit.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=f"anchored-precommit-{fault.value}".encode("ascii")
    )
    path = tmp_path / f"anchored-precommit-{fault.value}.sqlite"
    created = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    created.close()
    genesis_anchor = _anchor_for_path_v1(
        path,
        anchor_sequence=0,
        previous_anchor_root=ZERO_ROOT_V1,
    )
    backend = _MemoryMonotonicAnchorBackendV1(genesis_anchor)
    bound_anchor = _bound_monotonic_anchor_backend_v1(genesis_anchor, backend)
    publisher = VerifiedDurableEconomicPublisherV1.open_with_monotonic_anchor(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
        bound_anchor,
    )
    source = publisher.head

    def fail_before_commit(
        journal: GlobalEconomicEpochJournalV1,
        epoch: Any,
        cas_token: Any,
        write_capability: DurableEconomicEpochWriteCapabilityV1,
    ):
        return journal._commit_epoch_with_fault_for_test_v1(
            epoch,
            cas_token,
            fault,
            write_capability,
        )

    monkeypatch.setattr(
        GlobalEconomicEpochJournalV1,
        "_commit_epoch_from_verified_publisher_v1",
        fail_before_commit,
    )

    # Act / Assert: no-commit faults preserve their original typed failure and
    # leave both durable heads unchanged; a normal retry still commits once.
    with pytest.raises(_SimulatedDurableEconomicEpochCrashV1, match=fault.value):
        publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
        )
    assert publisher.head == source
    assert decode_global_economic_monotonic_anchor_v1(backend.current) == genesis_anchor
    monkeypatch.undo()
    committed = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )
    assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    publisher.close()


def test_replaced_authority_inode_remains_open_publisher_release_blocker(
    tmp_path: Path,
) -> None:
    # Arrange: one publisher retains the ACTIVE authority inode, while governance
    # prepares an exact REVOKED successor database in another directory.
    import os

    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"authority-inode-replacement-blocker"
    )
    path = tmp_path / "authority-inode-replacement.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    source = publisher.head
    authority_path = authority_journal_path_for_epoch_v1(path)
    with GlobalEconomicAuthorityJournalV1.open(authority_path) as current_journal:
        current = current_journal.head
    replacement_dir = tmp_path / "revoked-authority-replacement"
    replacement_dir.mkdir()
    replacement_path = authority_journal_path_for_epoch_v1(
        replacement_dir / "epoch.sqlite"
    )
    replacement = GlobalEconomicAuthorityJournalV1.create(
        replacement_path,
        current,
    )
    revoked = replacement._commit_successor_for_unmounted_control_plane_v1(
        current.revoked_successor(),
        replacement._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )
    replacement.close()

    # Act: replace the pathname atomically, then publish through the connection
    # that still has the detached ACTIVE authority inode attached.
    os.replace(replacement_path, authority_path)
    with GlobalEconomicAuthorityJournalV1.open(authority_path) as path_reader:
        assert path_reader.head.status.value == "REVOKED"
    published = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: the split view is reproducible and blocks any production claim.
    assert revoked.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    assert published.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    publisher.close()


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


def test_exact_committed_retry_after_revocation_returns_history_without_mutation(
    tmp_path: Path,
) -> None:
    # Arrange: Alice commits one verified epoch before governance revokes its writer.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"committed-before-revocation"
    )
    path = tmp_path / "committed-retry-after-revocation.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    source = publisher.head
    committed = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )
    epoch_bytes = path.read_bytes()
    authority = GlobalEconomicAuthorityJournalV1.open(
        authority_journal_path_for_epoch_v1(path)
    )
    revoked = authority._commit_successor_for_unmounted_control_plane_v1(
        authority.head.revoked_successor(),
        authority._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )
    authority.close()

    # Act: a lost-ack retry submits the exact publication already in history.
    retried = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: historical truth is returned, while revocation admits no new write.
    assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert revoked.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
    assert retried.committed_epoch == committed.committed_epoch
    assert retried.published_epoch == committed.published_epoch
    assert publisher.head == committed.committed_epoch
    assert path.read_bytes() == epoch_bytes
    publisher.close()


def test_epoch_only_sequence_zero_restore_allows_duplicate_release_blocker(
    tmp_path: Path,
) -> None:
    # Arrange: preserve only the sequence-zero epoch file while authority remains
    # active, then commit one value-bearing publication under that authority.
    admission, candidate, body = _publisher_fixture_v1(
        receipt_bytes=b"epoch-only-rollback-blocker"
    )
    path = tmp_path / "epoch-only-rollback-blocker.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    sequence_zero_bytes = path.read_bytes()
    source = publisher.head
    first = publisher.publish_economic_epoch(
        expected_source=source,
        candidate=candidate,
        body_and_state=body,
    )
    publisher.close()

    # Act: an operator restores only the epoch DB, then reopens under the unchanged
    # active authority and submits the identical publication again.
    path.write_bytes(sequence_zero_bytes)
    restored = VerifiedDurableEconomicPublisherV1.open(
        path,
        admission,
        _bound_receipt_verifier_v1(candidate)[0],
    )
    duplicate = restored.publish_economic_epoch(
        expected_source=restored.head,
        candidate=candidate,
        body_and_state=body,
    )

    # Assert: this reproducible duplicate keeps anti-rollback publication open.
    assert first.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert duplicate.status is DurableEconomicEpochCommitStatusV1.COMMITTED
    assert duplicate.committed_epoch == first.committed_epoch
    restored.close()


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
