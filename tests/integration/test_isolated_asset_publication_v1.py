"""Admission-to-commit controls: real BLS, explicitly simulated proof processes."""

import sqlite3
from contextlib import closing
from dataclasses import replace

import pytest

from src.core.asset_transfer_epoch_allocation_v1 import (
    AssetTransferEpochAllocationRejectCodeV1,
    AssetTransferEpochAllocationRejectedV1,
)
from src.integration import global_economic_durable_publisher_v1 as publisher_module
from src.integration.global_economic_epoch_journal_v1 import DurableEconomicEpochCommitStatusV1
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


def _economic_rows(path):
    # These rows contain the full activation, complete epoch bundles and head.
    # SQLite housekeeping bytes are deliberately outside this logical oracle.
    with closing(sqlite3.connect(path)) as connection:
        return tuple(
            tuple(connection.execute(f"SELECT * FROM {table} ORDER BY 1"))
            for table in ("metadata", "economic_epochs", "current_head")
        )


@pytest.mark.parametrize("missing", (True, False))
def test_given_valid_epoch_when_raw_authentication_is_absent_then_no_commit(tmp_path, missing):
    admission, candidate, body = _publisher_fixture_v1()
    pipeline, backend = _bound_receipt_verifier_v1(candidate)
    path = tmp_path / "missing-auth.sqlite"
    with publisher_module.VerifiedDurableEconomicPublisherV1.create(
        path, admission, pipeline
    ) as publisher:
        source, before = publisher.head, _economic_rows(path)
        arguments = dict(expected_source=source, candidate=candidate, body_and_state=body)
        if not missing:
            arguments["raw_evidence"] = ()
        with pytest.raises((TypeError, ValueError), match="raw_evidence|raw occurrence"):
            publisher.publish_economic_epoch(**arguments)
        assert publisher.head == source
        assert _economic_rows(path) == before
        assert len(backend.calls) == 1


def test_given_real_signed_intent_when_signature_changes_then_replay_and_history_stay_pre(tmp_path):
    admission, candidate, body = _publisher_fixture_v1()
    pipeline, backend = _bound_receipt_verifier_v1(candidate)
    raw = publisher_raw_evidence_v1(candidate)[0]
    changed = replace(raw, envelope=replace(raw.envelope, signature_bytes=b"\0" * 96))
    path = tmp_path / "bad-signature.sqlite"
    with publisher_module.VerifiedDurableEconomicPublisherV1.create(
        path, admission, pipeline
    ) as publisher:
        source, before = publisher.head, _economic_rows(path)
        with pytest.raises(ValueError, match="signature rejected"):
            publisher.publish_economic_epoch(
                expected_source=source, candidate=candidate,
                body_and_state=body, raw_evidence=(changed,),
            )
        assert publisher.head == source
        assert _economic_rows(path) == before
        assert len(backend.calls) == 1
        committed = publisher.publish_economic_epoch(
            expected_source=source, candidate=candidate,
            body_and_state=body, raw_evidence=(raw,),
        )
        assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        assert publisher.head.sequence == 1


@pytest.mark.parametrize(
    "field", ("module_receipt_bytes", "coordinator_receipt_bytes", "route_receipt_bytes")
)
def test_each_leaf_verifier_refusal_stops_publication_before_root_and_commit(tmp_path, field):
    admission, candidate, body = _publisher_fixture_v1()
    pipeline, backend = _bound_receipt_verifier_v1(candidate)
    raw = publisher_raw_evidence_v1(candidate)[0]
    path = tmp_path / "bad-leaf.sqlite"
    with publisher_module.VerifiedDurableEconomicPublisherV1.create(
        path, admission, pipeline
    ) as publisher:
        source, before = publisher.head, _economic_rows(path)
        with pytest.raises(ValueError, match="receipt|statement"):
            publisher.publish_economic_epoch(
                expected_source=source, candidate=candidate, body_and_state=body,
                raw_evidence=(replace(raw, **{field: b"foreign-leaf"}),),
            )
        assert publisher.head == source
        assert _economic_rows(path) == before
        assert len(backend.calls) == 1


def test_allocation_refusal_is_mandatory_and_does_not_poison_exact_resubmission(
    tmp_path, monkeypatch
):
    admission, candidate, body = _publisher_fixture_v1()
    pipeline, backend = _bound_receipt_verifier_v1(candidate)
    path = tmp_path / "allocation-refused.sqlite"
    raw = publisher_raw_evidence_v1(candidate)
    rejection = AssetTransferEpochAllocationRejectedV1(
        AssetTransferEpochAllocationRejectCodeV1.CERTIFICATE_REJECTED, 0,
    )
    observed = []

    def refuse(**inputs):
        observed.append(inputs)
        return rejection

    # This fixed-verdict fault control proves mandatory mediation. Exact
    # allocation semantics have independent core/refinement regression tests.
    with publisher_module.VerifiedDurableEconomicPublisherV1.create(
        path, admission, pipeline
    ) as publisher:
        source, before = publisher.head, _economic_rows(path)
        with monkeypatch.context() as patch:
            patch.setattr(publisher_module, "check_asset_transfer_epoch_allocation_v1", refuse)
            with pytest.raises(publisher_module.GlobalEconomicAllocationRejectedV1) as caught:
                publisher.publish_economic_epoch(
                    expected_source=source, candidate=candidate,
                    body_and_state=body, raw_evidence=raw,
                )
        assert caught.value.rejection is rejection
        assert len(observed) == 1
        assert observed[0]["predecessor"] == admission.state
        assert len(observed[0]["module_evidence"]) == 1
        assert publisher.head == source
        assert _economic_rows(path) == before
        assert len(backend.calls) == 1
        committed = publisher.publish_economic_epoch(
            expected_source=source, candidate=candidate,
            body_and_state=body, raw_evidence=raw,
        )
        assert committed.status is DurableEconomicEpochCommitStatusV1.COMMITTED
        assert publisher.head.sequence == 1


@pytest.mark.parametrize("field", ("route_journals", "route_effect_plans"))
def test_extra_parallel_row_is_refused_before_candidate_snapshot(tmp_path, monkeypatch, field):
    admission, candidate, body = _publisher_fixture_v1()
    pipeline, backend = _bound_receipt_verifier_v1(candidate)
    # Two ordinary rows suffice to observe guard ordering; this is no load test.
    extra = replace(candidate, **{field: getattr(candidate, field) * 2})
    path = tmp_path / "extra-parallel-row.sqlite"
    with publisher_module.VerifiedDurableEconomicPublisherV1.create(
        path, admission, pipeline
    ) as publisher:
        source, before = publisher.head, _economic_rows(path)
        observed = []

        def unexpected_snapshot(value):
            observed.append(value)
            pytest.fail("out-of-scope candidate reached deep snapshot")

        monkeypatch.setattr(
            publisher_module, "_snapshot_economic_epoch_candidate_v1", unexpected_snapshot
        )
        with pytest.raises(ValueError, match="one occurrence and one lane"):
            publisher.publish_economic_epoch(
                expected_source=source, candidate=extra, body_and_state=body,
                raw_evidence=publisher_raw_evidence_v1(candidate),
            )
        assert observed == []
        assert publisher.head == source
        assert _economic_rows(path) == before
        assert len(backend.calls) == 1
