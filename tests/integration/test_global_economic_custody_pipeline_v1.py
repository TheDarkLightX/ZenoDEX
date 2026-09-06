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
from tests.core.test_global_settlement_abi_v1 import _initial_state_admission
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


def _publication_v1(subject):
    candidate = subject.candidate
    receipt = b"custody-publisher-epoch-v1"
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
    admission = replace(
        _initial_state_admission(candidate.profile, candidate.pre_state),
        policy_registry=subject.policy,
    )
    return admission, candidate, body


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
