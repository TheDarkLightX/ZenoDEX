"""Isolated custody publication with explicit predecessor claimant liabilities.

RISC0 process replies and release coordinates are synthetic. These tests exercise
the real publication, allocation and command-authentication paths on test state;
they qualify no initial ownership policy, guest image, receipt or live release.
"""

from __future__ import annotations

import hashlib
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.global_settlement_types_v1 import EconomicAmountV1, hash_global_v1
from src.integration import economic_command_bls_signature_verifier_v1 as bls
from src.integration import global_receipt_verifier_v1 as receipt_bridge
from src.integration import isolated_asset_receipt_pipeline_v1 as pipeline
from src.integration import sealed_bls_command_verifier_v1 as sealed_bls
from src.integration.global_economic_commit_v1 import EconomicEpochBodyAndStateV1
from src.integration.global_economic_durable_epoch_v1 import (
    DurableEconomicEpochMaterialV1,
    prepare_durable_economic_epoch_bundle_v1,
)
from src.integration.global_economic_durable_publisher_v1 import (
    GlobalEconomicAllocationRejectedV1,
    VerifiedDurableEconomicPublisherV1,
)
from src.integration.global_economic_epoch_journal_v1 import DurableEconomicEpochCommitStatusV1
from tests.core.test_economic_receipt_verifier_release_v1 import _RecordingBackend
from tests.integration.custody_asset_receipt_pipeline_fixtures_v1 import _fixture
from tests.integration.publisher_receipt_port_fixtures_v1 import (
    simulated_measured_publisher_crypto_v1 as simulated_measured_publisher_crypto_v1,
)
from tests.integration.test_global_economic_sealed_bls_pipeline_v1 import (
    _logical_store_v1,
    _qualified_bls_binary_v1,
    _receipt_ports_v1,
)
from tests.integration.test_sealed_bls_command_verifier_deployment_v1 import (
    _isolated_test_manifest,
    _isolated_test_release,
)

_DIRECT_SEALED_BLS_INVOKE_V1 = sealed_bls._invoke_v1


def _publication_v1(
    subject,
    *,
    receipt: bytes = b"custody-publisher-epoch-v1",
):
    candidate = subject.candidate
    body = EconomicEpochBodyAndStateV1(
        pre_state_root=candidate.pre_state.state_root,
        post_state=candidate.post_state,
        ordered_command_body_hashes=candidate.ordered_command_body_hashes,
        receipt_archive_root=hash_global_v1(
            "durable-publisher-receipt-archive-v1",
            {"receipt_sha256": hashlib.sha256(receipt).hexdigest()},
        ),
        data_availability_root=candidate.certificate.data_availability_root,
        finality_root=candidate.certificate.finality_root,
    )
    certificate = replace(
        candidate.certificate,
        body_commitment=body.body_commitment,
        receipt_root="0x" + hashlib.sha256(receipt).hexdigest(),
        journal_bytes=1,
    )
    certificate = replace(certificate, journal_bytes=len(certificate.canonical_journal_bytes))
    candidate = replace(
        candidate,
        certificate=certificate,
        receipt_bytes=receipt,
        expected_body_commitment=body.body_commitment,
    )
    return subject.activation.initial_state_admission, candidate, body


def _pipeline_v1(subject, candidate, root_backend, artifact: Path | None = None):
    if artifact is not None:
        return pipeline.bind_isolated_custody_asset_receipt_pipeline_with_sealed_bls_v1(
            profile=candidate.profile,
            policy_registry=subject.policy,
            receipt_ports=_receipt_ports_v1(candidate, subject, root_backend),
            deployment_root=candidate.pre_state.deployment_root,
            signature_artifact_path=artifact,
            signature_release=subject.signature_release,
            signature_evidence_manifest=subject.signature_manifest,
            signature_timeout_ms=5000,
        )
    return pipeline.bind_isolated_custody_asset_receipt_pipeline_v1(
        profile=candidate.profile,
        policy_registry=subject.policy,
        receipt_ports=_receipt_ports_v1(candidate, subject, root_backend),
        deployment_root=candidate.pre_state.deployment_root,
        signature_artifact_path=Path(bls.__file__),
        signature_release=subject.signature_release,
        signature_evidence_manifest=subject.signature_manifest,
    )


@pytest.mark.parametrize("signature_backend", ["python", "sealed"])
def test_backed_custody_commits_complete_bundle_and_exact_retry(
    tmp_path: Path, simulated_measured_publisher_crypto_v1, signature_backend: str,
) -> None:
    artifact = _qualified_bls_binary_v1() if signature_backend == "sealed" else None
    if artifact is None:
        subject = _fixture(simulated_measured_publisher_crypto_v1)
    else:
        assert sealed_bls._invoke_v1 is _DIRECT_SEALED_BLS_INVOKE_V1
        assert receipt_bridge._invoke_v1 is not _DIRECT_SEALED_BLS_INVOKE_V1
        subject = _fixture(
            simulated_measured_publisher_crypto_v1,
            signature_artifact_path=artifact,
            signature_manifest_factory=lambda data: _isolated_test_manifest(artifact_bytes=data),
            signature_release_factory=_isolated_test_release,
        )
    admission, candidate, body = _publication_v1(subject)
    backend = _RecordingBackend()
    path = tmp_path / "custody.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _pipeline_v1(subject, candidate, backend, artifact),
    )
    try:
        source = publisher.head
        before = _logical_store_v1(path)
        signature = subject.raw.envelope.signature_bytes
        bad = replace(subject.raw, envelope=replace(
            subject.raw.envelope, signature_bytes=signature[:-1] + bytes((signature[-1] ^ 1,)),
        ))
        calls = tuple(backend.calls)
        with pytest.raises(ValueError, match="command authentication signature rejected"):
            publisher.publish_economic_epoch(
                expected_source=source, candidate=candidate,
                body_and_state=body, raw_evidence=(bad,),
            )
        assert _logical_store_v1(path) == before
        assert publisher.head == source
        assert subject.calls == []
        assert tuple(backend.calls) == calls

        result = publisher.publish_economic_epoch(
            expected_source=source, candidate=candidate,
            body_and_state=body, raw_evidence=(subject.raw,),
        )
        assert result.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        assert result.published_epoch is not None
        expected = prepare_durable_economic_epoch_bundle_v1(DurableEconomicEpochMaterialV1(
            source_head=source, profile=candidate.profile, certificate=candidate.certificate,
            effect_plan=candidate.effect_plan, body_and_state=body,
            published_epoch=result.published_epoch, receipt_bytes=candidate.receipt_bytes,
        ))
        assert result.head == expected.head == result.committed_epoch
        committed = (
            before[0], ((1, expected.record.publication_id, "1"),),
            ((expected.record.publication_id, expected.record.commit_id, "1", expected.canonical_bytes),),
        )
        assert _logical_store_v1(path) == committed
        assert tuple(subject.calls) == subject.expected
        assert len(backend.calls) == len(calls) + 1
        assert candidate.post_state.custody == candidate.pre_state.custody
        assert candidate.post_state.liabilities == candidate.pre_state.liabilities
        assert candidate.pre_state.custody == (EconomicAmountV1("custodian", "USD", "vault", 7),)
        assert candidate.pre_state.liabilities == (EconomicAmountV1("alice", "USD", "vault", 7),)

        retry = publisher.publish_economic_epoch(
            expected_source=source, candidate=candidate,
            body_and_state=body, raw_evidence=(subject.raw,),
        )
        assert retry.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
        assert retry.head == result.head
        assert retry.published_epoch == result.published_epoch
        assert _logical_store_v1(path) == committed
    finally:
        publisher.close()


@pytest.mark.parametrize("liability_atoms", [0, 6, 8])
def test_missing_or_mismatched_claimant_backing_rejects_before_epoch_and_commit(
    tmp_path: Path, simulated_measured_publisher_crypto_v1, liability_atoms: int,
) -> None:
    liabilities = (
        () if liability_atoms == 0
        else (EconomicAmountV1("alice", "USD", "vault", liability_atoms),)
    )
    subject = _fixture(
        simulated_measured_publisher_crypto_v1, claimant_liabilities=liabilities,
    )
    admission, candidate, body = _publication_v1(subject)
    backend = _RecordingBackend()
    path = tmp_path / "unbacked.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _pipeline_v1(subject, candidate, backend),
    )
    try:
        source = publisher.head
        before = _logical_store_v1(path)
        calls = tuple(backend.calls)
        with pytest.raises(GlobalEconomicAllocationRejectedV1) as caught:
            publisher.publish_economic_epoch(
                expected_source=source, candidate=candidate,
                body_and_state=body, raw_evidence=(subject.raw,),
            )
        rejection = caught.value.rejection
        assert rejection.code.value == "GLOBAL_FRAGMENT_REJECTED"
        assert rejection.cause is not None
        assert rejection.cause.code.value == "ENTITLEMENT_COVERAGE_DRIFT"
        assert _logical_store_v1(path) == before
        assert publisher.head == source
        assert tuple(subject.calls) == subject.expected
        assert tuple(backend.calls) == calls
    finally:
        publisher.close()


def test_forward_epoch_fixture_reuses_immutable_activation_context(
    simulated_measured_publisher_crypto_v1,
) -> None:
    first = _fixture(simulated_measured_publisher_crypto_v1)
    second = _fixture(
        simulated_measured_publisher_crypto_v1,
        activation=first.activation,
        pre_state=first.candidate.post_state,
        nonce_start=2,
    )
    assert second.candidate.pre_state == first.candidate.post_state
    assert second.candidate.profile == first.candidate.profile
    assert second.policy == first.policy
    assert second.raw.authorization_registry is first.activation.authorization_registry
    assert second.raw.signature_verifier_registry is first.activation.signature_verifier_registry
    assert second.raw.asset_policy_registry is first.activation.asset_policy_registry


def test_custody_activation_reopens_and_commits_adjacent_forward_epoch(
    tmp_path: Path, simulated_measured_publisher_crypto_v1,
) -> None:
    first = _fixture(simulated_measured_publisher_crypto_v1)
    admission, candidate, body = _publication_v1(
        first, receipt=b"custody-publisher-epoch-one-v1",
    )
    path = tmp_path / "custody-lifecycle.sqlite"
    first_backend = _RecordingBackend()
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path, admission, _pipeline_v1(first, candidate, first_backend),
    )
    try:
        source_zero = publisher.head
        result_one = publisher.publish_economic_epoch(
            expected_source=source_zero,
            candidate=candidate,
            body_and_state=body,
            raw_evidence=(first.raw,),
        )
        assert result_one.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        assert result_one.published_epoch is not None
        expected_one = prepare_durable_economic_epoch_bundle_v1(
            DurableEconomicEpochMaterialV1(
                source_head=source_zero,
                profile=candidate.profile,
                certificate=candidate.certificate,
                effect_plan=candidate.effect_plan,
                body_and_state=body,
                published_epoch=result_one.published_epoch,
                receipt_bytes=candidate.receipt_bytes,
            )
        )
        assert result_one.head == expected_one.head
    finally:
        publisher.close()

    committed_one_store = _logical_store_v1(path)
    assert committed_one_store[2] == (
        (
            expected_one.record.publication_id,
            expected_one.record.commit_id,
            "1",
            expected_one.canonical_bytes,
        ),
    )

    reopened_backend = _RecordingBackend()
    reopened = VerifiedDurableEconomicPublisherV1.open(
        path, admission, _pipeline_v1(first, candidate, reopened_backend),
    )
    try:
        assert reopened.head == result_one.head
        retry_one = reopened.publish_economic_epoch(
            expected_source=source_zero,
            candidate=candidate,
            body_and_state=body,
            raw_evidence=(first.raw,),
        )
        assert retry_one.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
        assert retry_one.head == result_one.head
        assert retry_one.published_epoch == result_one.published_epoch
        assert _logical_store_v1(path) == committed_one_store
    finally:
        reopened.close()

    second = _fixture(
        simulated_measured_publisher_crypto_v1,
        activation=first.activation,
        pre_state=candidate.post_state,
        nonce_start=2,
    )
    admission_two, candidate_two, body_two = _publication_v1(
        second, receipt=b"custody-publisher-epoch-two-v1",
    )
    assert second.activation is first.activation
    assert admission_two is admission
    assert candidate_two.pre_state == candidate.post_state
    for state in (candidate, candidate_two):
        assert state.pre_state.custody == (
            EconomicAmountV1("custodian", "USD", "vault", 7),
        )
        assert state.post_state.custody == state.pre_state.custody
        assert state.pre_state.liabilities == (
            EconomicAmountV1("alice", "USD", "vault", 7),
        )
        assert state.post_state.liabilities == state.pre_state.liabilities

    second_backend = _RecordingBackend()
    publisher_two = VerifiedDurableEconomicPublisherV1.open(
        path,
        admission_two,
        _pipeline_v1(second, candidate_two, second_backend),
    )
    try:
        source_one = publisher_two.head
        assert source_one == result_one.head
        result_two = publisher_two.publish_economic_epoch(
            expected_source=source_one,
            candidate=candidate_two,
            body_and_state=body_two,
            raw_evidence=(second.raw,),
        )
        assert result_two.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        assert result_two.published_epoch is not None
        expected_two = prepare_durable_economic_epoch_bundle_v1(
            DurableEconomicEpochMaterialV1(
                source_head=source_one,
                profile=candidate_two.profile,
                certificate=candidate_two.certificate,
                effect_plan=candidate_two.effect_plan,
                body_and_state=body_two,
                published_epoch=result_two.published_epoch,
                receipt_bytes=candidate_two.receipt_bytes,
            )
        )
        assert result_two.head == expected_two.head
        assert expected_two.record.source_publication_id == expected_one.record.publication_id
        assert expected_two.record.pre_state_root == expected_one.record.post_state_root
        assert expected_two.record.height == expected_one.record.height + 1
        assert expected_two.record.sequence == expected_one.record.sequence + 1

        exact_rows = tuple(
            sorted(
                (
                    (
                        bundle.record.publication_id,
                        bundle.record.commit_id,
                        str(bundle.record.sequence),
                        bundle.canonical_bytes,
                    )
                    for bundle in (expected_one, expected_two)
                ),
                key=lambda row: row[0],
            )
        )
        store_after_two = _logical_store_v1(path)
        assert store_after_two[1] == ((1, expected_two.record.publication_id, "2"),)
        assert store_after_two[2] == exact_rows

        retry_two = publisher_two.publish_economic_epoch(
            expected_source=source_one,
            candidate=candidate_two,
            body_and_state=body_two,
            raw_evidence=(second.raw,),
        )
        assert retry_two.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
        assert retry_two.head == result_two.head
        assert retry_two.published_epoch == result_two.published_epoch
        assert _logical_store_v1(path) == store_after_two
    finally:
        publisher_two.close()
