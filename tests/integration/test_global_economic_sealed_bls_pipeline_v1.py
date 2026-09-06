"""Test-state publication through measured BLS and synthetic receipt replies.

Command authentication executes the checksum-qualified standalone BLS endpoint.
The existing publisher fixture still supplies synthetic RISC0 process replies,
so this evidence qualifies neither genuine receipts nor a production release.
All signature release and manifest coordinates in this file are synthetic.
"""

from __future__ import annotations

import hashlib
import os
import sqlite3
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

import tests.integration.asset_receipt_pipeline_fixtures_v1 as asset_fixtures
import tests.integration.publisher_receipt_port_fixtures_v1 as publisher_fixtures
from src.integration import global_receipt_verifier_v1 as receipt_bridge
from src.integration import isolated_asset_receipt_pipeline_v1 as pipeline
from src.integration import sealed_bls_command_verifier_v1 as sealed_bls
from src.integration.global_economic_durable_epoch_v1 import (
    DurableEconomicEpochMaterialV1,
    prepare_durable_economic_epoch_bundle_v1,
)
from src.integration.global_economic_durable_publisher_v1 import (
    VerifiedDurableEconomicPublisherV1,
)
from src.integration.global_economic_epoch_journal_v1 import (
    DurableEconomicEpochCommitStatusV1,
)
from tests.core.test_economic_receipt_verifier_release_v1 import _RecordingBackend
from tests.integration.publisher_receipt_port_fixtures_v1 import (
    simulated_measured_publisher_crypto_v1 as simulated_measured_publisher_crypto_v1,
)
from tests.integration.test_global_economic_durable_publisher_v1 import (
    _publisher_fixture_v1,
)
from tests.integration.test_sealed_bls_command_verifier_deployment_v1 import (
    _isolated_test_manifest,
    _isolated_test_release,
)

pytestmark = pytest.mark.usefixtures("simulated_measured_publisher_crypto_v1")

_BLS_BINARY_ENV_V1 = "ZENODEX_BLS_VERIFIER_TEST_BINARY"
_BLS_BINARY_SHA256_V1 = "597f1e56fcca8f00bc94805cf020ca0e6f2779ded3b1944d1d699231f55b0eee"
_DIRECT_SEALED_BLS_INVOKE_V1 = sealed_bls._invoke_v1


def _qualified_bls_binary_v1() -> Path:
    configured = os.environ.get(_BLS_BINARY_ENV_V1)
    if configured is None:
        pytest.skip("explicit checksum-qualified BLS verifier binary is required")
    path = Path(os.environ[_BLS_BINARY_ENV_V1])
    assert hashlib.sha256(path.read_bytes()).hexdigest() == _BLS_BINARY_SHA256_V1
    return path


def _logical_store_v1(path: Path) -> tuple[tuple[tuple[object, ...], ...], ...]:
    with sqlite3.connect(path) as connection:
        connection.execute("BEGIN")
        return tuple(
            tuple(connection.execute(query).fetchall())
            for query in (
                "SELECT * FROM metadata ORDER BY singleton",
                "SELECT * FROM current_head ORDER BY singleton",
                "SELECT * FROM economic_epochs ORDER BY publication_id",
            )
        )


def _publisher_fixture_for_signature_protocol_v1(
    monkeypatch: pytest.MonkeyPatch,
    artifact_path: Path,
    *,
    sealed_bls: bool,
):
    with monkeypatch.context() as patch:
        patch.setattr(
            asset_fixtures,
            "bls",
            SimpleNamespace(__file__=str(artifact_path)),
        )
        if sealed_bls:
            patch.setattr(
                asset_fixtures,
                "_signature_verifier_manifest",
                _isolated_test_manifest,
            )
            patch.setattr(
                asset_fixtures,
                "_signature_verifier_release",
                _isolated_test_release,
            )
        return _publisher_fixture_v1(receipt_bytes=b"sealed-bls-publisher-epoch-v1")


def _subject_v1(candidate):
    occurrence_id = candidate.command_occurrences[0].occurrence_id
    return publisher_fixtures._owner().publisher_subjects[occurrence_id]


def _receipt_ports_v1(candidate, subject, root_backend: _RecordingBackend):
    root_call = root_backend.verify_succinct_receipt

    class ReceiptStagesV1:
        def verify_succinct_receipt(
            self,
            receipt_bytes,
            *,
            expected_image_id,
            expected_journal_bytes,
        ):
            call = (
                root_call
                if expected_image_id == candidate.profile.root_image_id
                else subject.verify_succinct_receipt
            )
            return call(
                receipt_bytes,
                expected_image_id=expected_image_id,
                expected_journal_bytes=expected_journal_bytes,
            )

    return publisher_fixtures.bind_publisher_test_receipt_ports_v1(
        candidate,
        ReceiptStagesV1(),
    )


def _bind_sealed_pipeline_v1(
    candidate,
    subject,
    artifact_path: Path,
    root_backend: _RecordingBackend,
):
    return pipeline.bind_isolated_asset_receipt_pipeline_with_sealed_bls_v1(
        profile=candidate.profile,
        policy_registry=subject.policy,
        receipt_ports=_receipt_ports_v1(candidate, subject, root_backend),
        deployment_root=candidate.pre_state.deployment_root,
        signature_artifact_path=artifact_path,
        signature_release=subject.signature_release,
        signature_evidence_manifest=subject.signature_manifest,
        signature_timeout_ms=5000,
    )


def test_measured_sealed_bls_authentication_controls_exact_durable_publication(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact_path = _qualified_bls_binary_v1()
    admission, candidate, body = _publisher_fixture_for_signature_protocol_v1(
        monkeypatch,
        artifact_path,
        sealed_bls=True,
    )
    assert sealed_bls._invoke_v1 is _DIRECT_SEALED_BLS_INVOKE_V1
    assert receipt_bridge._invoke_v1 is not _DIRECT_SEALED_BLS_INVOKE_V1
    subject = _subject_v1(candidate)
    root_backend = _RecordingBackend()
    admission_pipeline = _bind_sealed_pipeline_v1(
        candidate,
        subject,
        artifact_path,
        root_backend,
    )
    path = tmp_path / "sealed-bls-publisher.sqlite"
    publisher = VerifiedDurableEconomicPublisherV1.create(
        path,
        admission,
        admission_pipeline,
    )
    try:
        source = publisher.head
        before = _logical_store_v1(path)
        assert before[1] == ((1, source.publication_id, "0"),)
        assert before[2] == ()
        leaf_calls_before = tuple(subject.calls)
        root_calls_before = tuple(root_backend.calls)
        signature = subject.raw.envelope.signature_bytes
        invalid_signature = signature[:-1] + bytes((signature[-1] ^ 1,))
        invalid_raw = (
            replace(
                subject.raw,
                envelope=replace(
                    subject.raw.envelope,
                    signature_bytes=invalid_signature,
                ),
            ),
        )

        with pytest.raises(ValueError, match="^command authentication signature rejected$"):
            publisher.publish_economic_epoch(
                expected_source=source,
                candidate=candidate,
                body_and_state=body,
                raw_evidence=invalid_raw,
            )

        assert _logical_store_v1(path) == before
        assert publisher.head == source
        assert tuple(subject.calls) == leaf_calls_before
        assert tuple(root_backend.calls) == root_calls_before

        committed = publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
            raw_evidence=(subject.raw,),
        )
        assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        assert committed.committed_epoch is not None
        assert committed.published_epoch is not None
        expected_bundle = prepare_durable_economic_epoch_bundle_v1(
            DurableEconomicEpochMaterialV1(
                source_head=source,
                profile=candidate.profile,
                certificate=candidate.certificate,
                effect_plan=candidate.effect_plan,
                body_and_state=body,
                published_epoch=committed.published_epoch,
                receipt_bytes=candidate.receipt_bytes,
            )
        )
        assert committed.head == expected_bundle.head
        assert committed.committed_epoch == expected_bundle.head
        committed_rows = (
            before[0],
            ((1, expected_bundle.record.publication_id, "1"),),
            (
                (
                    expected_bundle.record.publication_id,
                    expected_bundle.record.commit_id,
                    "1",
                    expected_bundle.canonical_bytes,
                ),
            ),
        )
        assert _logical_store_v1(path) == committed_rows
        assert tuple(subject.calls[len(leaf_calls_before) :]) == subject.expected
        assert len(root_backend.calls) == len(root_calls_before) + 1

        retried = publisher.publish_economic_epoch(
            expected_source=source,
            candidate=candidate,
            body_and_state=body,
            raw_evidence=(subject.raw,),
        )
        assert retried.status is DurableEconomicEpochCommitStatusV1.ALREADY_COMMITTED
        assert retried.head == expected_bundle.head
        assert retried.committed_epoch == expected_bundle.head
        assert retried.published_epoch == committed.published_epoch
        assert _logical_store_v1(path) == committed_rows
    finally:
        publisher.close()


def test_sealed_pipeline_factory_rejects_legacy_protocol_before_mint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    artifact_path = _qualified_bls_binary_v1()
    _, candidate, _ = _publisher_fixture_for_signature_protocol_v1(
        monkeypatch,
        artifact_path,
        sealed_bls=False,
    )
    subject = _subject_v1(candidate)
    root_backend = _RecordingBackend()
    receipt_ports = _receipt_ports_v1(candidate, subject, root_backend)
    mint_calls: list[object] = []

    def forbidden_mint(**values: object):
        mint_calls.append(values)
        raise AssertionError("wrong protocol reached pipeline authority mint")

    monkeypatch.setattr(
        pipeline,
        "_mint_isolated_asset_receipt_pipeline_v1",
        forbidden_mint,
    )
    with pytest.raises(
        ValueError,
        match="^command signature verifier backend protocol root mismatch$",
    ):
        pipeline.bind_isolated_asset_receipt_pipeline_with_sealed_bls_v1(
            profile=candidate.profile,
            policy_registry=subject.policy,
            receipt_ports=receipt_ports,
            deployment_root=candidate.pre_state.deployment_root,
            signature_artifact_path=artifact_path,
            signature_release=subject.signature_release,
            signature_evidence_manifest=subject.signature_manifest,
            signature_timeout_ms=5000,
        )
    assert mint_calls == []
