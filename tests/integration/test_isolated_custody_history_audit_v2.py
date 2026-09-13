"""Read-only historical reauthentication; receipt fixtures are not proofs."""

import hashlib
import json
import os
import sqlite3
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.global_settlement_primitives_v2 import canonical_global_bytes_v2
from src.integration.custody_publication_record_v2 import CustodyPublicationRecordV2
from src.integration.global_receipt_verifier_v1 import (
    GlobalReceiptVerifierErrorV1,
    GlobalReceiptVerifierRejectV1,
)
from src.integration.isolated_custody_publisher_v2 import IsolatedCustodyPublisherV2
from tests.integration.test_authenticated_asset_lane_custody_receipt_v2 import (
    _RECEIPT,
    _case,
    _receipt_exchange,
    _sign,
)
from tests.integration.test_isolated_custody_publisher_v2 import (
    _configuration,
    _create,
    _logical_store,
    _publish,
)
from tests.integration.test_isolated_economic_command_authentication_v2 import (
    _NATIVE_SHA256,
)
from tests.integration.test_isolated_economic_command_authentication_v2 import (
    protocol_case as protocol_case,
)
from tests.integration.test_profiled_asset_lane_custody_receipt_v2 import (
    receipt_artifact as receipt_artifact,
)


@pytest.fixture
def history(tmp_path, protocol_case, receipt_artifact, monkeypatch):
    case = _case()
    config = _configuration(case, protocol_case[1], receipt_artifact)
    receipts = _receipt_exchange(monkeypatch, case.expected)
    with _create(tmp_path, case, config) as publisher:
        _publish(publisher, case)
        head = publisher.snapshot()
    return tmp_path / "custody.sqlite", case, config, head, receipts, protocol_case[2]


def _audit(history, **overrides):
    path, case, config, head, _, _ = history
    options = {
        "authentication_candidates": (case.candidate,),
        "expected_publication_id": head.publication_id,
        "expected_authority_root": head.authority.authority_root,
    }
    options.update(overrides)
    return IsolatedCustodyPublisherV2.audit(
        path, case.inputs[3], case.inputs[1], config, **options,
    )


def _replace_retained_record(path, **changes):
    """A compromised writer recomputes all local hashes after substitution."""
    with sqlite3.connect(path) as connection:
        row = connection.execute("SELECT * FROM publications").fetchone()
        record = replace(CustodyPublicationRecordV2(row[0], *row[3:]), **changes)
        connection.execute(
            "UPDATE publications SET publication_id=?, request_id=?, authentication_message=?, signature=?, receipt=?",
            (record.publication_id, record.request_id, record.authentication_message, record.signature, record.receipt),
        )
        connection.execute("UPDATE heads SET publication_id=?", (record.publication_id,))
    return record


def test_given_retained_history_when_audited_then_reverify_and_leave_database_unchanged(history):
    path, _, _, head, receipts, signatures = history
    before = path.read_bytes(), _logical_store(path), path.stat().st_mtime_ns
    assert _audit(history) == head
    assert len(receipts) == len(signatures) == 2
    assert (path.read_bytes(), _logical_store(path), path.stat().st_mtime_ns) == before


def test_given_rehashed_false_signature_when_audited_then_conserving_forgery_rejects(history):
    path, case, config, _, receipts, signatures = history
    forged = _sign(case.candidate, scalar=42)
    record = _replace_retained_record(path, signature=forged.envelope.signature_bytes)
    # Economic recovery alone accepts this self-consistent history. The new
    # auditor must reject even if given the attacker's recomputed checkpoint.
    with IsolatedCustodyPublisherV2.open(path, case.inputs[3], case.inputs[1], config) as recovered:
        assert recovered.snapshot().publication_id == record.publication_id
        assert recovered.snapshot().global_state == case.inputs[4]
    before = path.read_bytes(), _logical_store(path)
    with pytest.raises(ValueError, match="signature rejected"):
        _audit(history, authentication_candidates=(forged,), expected_publication_id=record.publication_id)
    assert len(receipts) == 1 and len(signatures) == 2
    assert (path.read_bytes(), _logical_store(path)) == before


def test_given_rehashed_false_receipt_when_audited_then_backend_rejection_propagates(history, monkeypatch):
    from src.integration import global_receipt_verifier_v1 as transport

    path = history[0]
    record = _replace_retained_record(path, receipt=b"forged receipt")
    calls = []

    def reject(descriptor, request, timeout):
        calls.append(request)
        return b"", b"", 1

    monkeypatch.setattr(transport, "_invoke_v1", reject)
    before = path.read_bytes(), _logical_store(path)
    with pytest.raises(GlobalReceiptVerifierErrorV1) as caught:
        _audit(history, expected_publication_id=record.publication_id)
    assert caught.value.reason is GlobalReceiptVerifierRejectV1.VERIFICATION_REJECTED
    assert len(calls) == 1 and calls[0].endswith(record.statement + record.receipt)
    assert (path.read_bytes(), _logical_store(path)) == before


def test_given_changed_retained_policy_witness_when_audited_then_no_verifier_io(history):
    path, case, _, _, receipts, signatures = history
    with sqlite3.connect(path) as connection:
        message = connection.execute("SELECT authentication_message FROM publications").fetchone()[0]
    start = message.index(b"{")
    body = json.loads(message[start:])
    body["authorization_id"] = "0x" + "ad" * 32
    record = _replace_retained_record(
        path, authentication_message=message[:start] + canonical_global_bytes_v2(body),
    )
    assert record.replay().global_post == case.inputs[4]
    before = path.read_bytes(), _logical_store(path)
    with pytest.raises(ValueError, match="audit authentication witness"):
        _audit(history, expected_publication_id=record.publication_id)
    assert len(receipts) == len(signatures) == 1
    assert (path.read_bytes(), _logical_store(path)) == before


@pytest.mark.parametrize("field", ("expected_publication_id", "expected_authority_root", "authentication_candidates"))
def test_given_missing_witness_or_wrong_checkpoint_when_audited_then_no_verifier_io(history, field):
    path, _, _, _, receipts, signatures = history
    changed = () if field == "authentication_candidates" else "0x" + "ab" * 32
    before = path.read_bytes(), _logical_store(path)
    with pytest.raises(ValueError, match="audit"):
        _audit(history, **{field: changed})
    assert len(receipts) == len(signatures) == 1
    assert (path.read_bytes(), _logical_store(path)) == before


def test_given_hostile_or_oversized_authentication_witnesses_when_audited_then_fail_before_io(history):
    class Hostile:
        @property
        def profile(self):
            pytest.fail("foreign getter executed")

    for candidates, error in (
        ([history[1].candidate], TypeError),
        ((Hostile(),), TypeError),
        ((history[1].candidate,) * 65, ValueError),
    ):
        with pytest.raises(error):
            _audit(history, authentication_candidates=candidates)
    assert len(history[4]) == len(history[5]) == 1


def test_given_revoked_writer_when_audited_then_history_verifies_without_restoring_authority(history):
    path, case, config, _, receipts, signatures = history
    with IsolatedCustodyPublisherV2.open(path, case.inputs[3], case.inputs[1], config) as publisher:
        publisher.revoke()
        final = publisher.snapshot()
    with pytest.raises(PermissionError, match="authority"):
        IsolatedCustodyPublisherV2.open(path, case.inputs[3], case.inputs[1], config)
    before = path.read_bytes(), _logical_store(path)
    assert _audit(history, expected_authority_root=final.authority.authority_root) == final
    assert len(receipts) == len(signatures) == 2
    assert (path.read_bytes(), _logical_store(path)) == before


def test_audit_connection_cannot_write_and_is_closed_before_external_verification(history, monkeypatch):
    from src.integration import global_receipt_verifier_v1 as transport

    original = sqlite3.connect
    connections = []

    def connect(*args, **kwargs):
        connection = original(*args, **kwargs)
        with pytest.raises(sqlite3.OperationalError, match="readonly"):
            connection.execute("UPDATE heads SET sequence=sequence")
        connections.append(connection)
        return connection

    def exchange(descriptor, request, timeout):
        assert len(connections) == 1
        with pytest.raises(sqlite3.ProgrammingError, match="closed"):
            connections[0].execute("SELECT * FROM heads")
        return b"ZDXRV1OK" + hashlib.sha256(request).digest() + request[8:40], b"", 0

    monkeypatch.setattr(sqlite3, "connect", connect)
    monkeypatch.setattr(transport, "_invoke_v1", exchange)
    assert _audit(history) == history[3]


def test_given_empty_history_when_audited_then_no_crypto_or_writer_authority(
    tmp_path, protocol_case, receipt_artifact,
):
    case = _case()
    config = _configuration(case, protocol_case[1], receipt_artifact)
    with _create(tmp_path, case, config) as publisher:
        head = publisher.snapshot()
    history = tmp_path / "custody.sqlite", case, config, head, [], protocol_case[2]
    assert _audit(history, authentication_candidates=()) == head
    assert head.sequence == 0 and protocol_case[2] == []


def test_given_interleaved_margin_and_transfer_history_when_audited_then_exact_order_and_roles(
    tmp_path, protocol_case, receipt_artifact, monkeypatch,
):
    from src.core.asset_lane_custody_coordinator_v2 import transition_asset_lane_custody_v2
    from src.core.asset_lane_custody_global_v2 import derive_asset_lane_custody_global_post_v2
    from src.core.asset_lane_custody_statement_v2 import (
        prepare_asset_lane_custody_global_statement_v2,
    )
    from src.core.perps_margin_receipt_v2 import prepare_perps_margin_statement_v2
    from src.integration import global_receipt_verifier_v1 as transport
    from tests.integration.test_isolated_joint_margin_publisher_v2 import (
        CLOSE,
        DEPOSIT,
        WITHDRAW,
        _margin,
        _open,
        _setup,
        _transfer,
    )

    base, config = _setup(protocol_case, receipt_artifact)
    path = tmp_path / "joint.sqlite"
    candidates, requests = [], []
    with _open(path, base, config, create=True) as publisher:
        for kind, amount, nonce, outer in ((DEPOSIT, 40, 1, 1), (WITHDRAW, 40, 2, 3), (CLOSE, 0, 3, 4)):
            head = publisher.snapshot()
            candidate, request = _margin(base, head, kind, amount, nonce, outer)
            expected = prepare_perps_margin_statement_v2(head.custody_state, head.margin_state, head.global_state, request)
            calls = _receipt_exchange(monkeypatch, expected)
            publisher.publish(candidate, request, receipt_bytes=_RECEIPT)
            candidates.append(candidate)
            requests.extend(calls)
            if outer == 1:
                head = publisher.snapshot()
                candidate, context, command = _transfer(base, head, 5, 2)
                accepted = transition_asset_lane_custody_v2(context, head.custody_state, command)
                successor = derive_asset_lane_custody_global_post_v2(head.custody_state, accepted, head.global_state, context.occurrence)
                expected = prepare_asset_lane_custody_global_statement_v2(context, head.custody_state, command, head.global_state, successor)
                calls = _receipt_exchange(monkeypatch, expected)
                publisher.publish(candidate, context, command, receipt_bytes=_RECEIPT)
                requests.extend(calls)
                candidates.append(candidate)
        final = publisher.snapshot()
    before = path.read_bytes(), _logical_store(path)
    verified = []

    def exchange(descriptor, request, timeout):
        assert request == requests[len(verified)]
        verified.append(request)
        # Later inputs remain caller-owned aliases. Mutating one during an
        # earlier verifier call must not change the already acquired audit.
        if len(verified) == 1:
            object.__setattr__(candidates[-1].envelope, "signature_bytes", b"\x00" * 96)
        return b"ZDXRV1OK" + hashlib.sha256(request).digest() + request[8:40], b"", 0

    monkeypatch.setattr(transport, "_invoke_v1", exchange)
    options = dict(
        margin_state=base.margin, authentication_candidates=tuple(candidates),
        expected_publication_id=final.publication_id, expected_authority_root=final.authority.authority_root,
    )
    assert IsolatedCustodyPublisherV2.audit(path, base.global_pre, base.assets, config, **options) == final
    assert len(verified) == final.sequence == 4
    assert len(protocol_case[2]) == 8
    options["authentication_candidates"] = tuple(reversed(candidates))
    with pytest.raises(ValueError, match="audit authentication witness"):
        IsolatedCustodyPublisherV2.audit(path, base.global_pre, base.assets, config, **options)
    assert len(verified) == 4 and len(protocol_case[2]) == 8
    assert (path.read_bytes(), _logical_store(path)) == before


def test_native_bls_reauthenticates_history_and_rejects_rehashed_forgery(tmp_path, receipt_artifact, monkeypatch):
    configured = os.environ.get("ZENODEX_BLS_VERIFIER_TEST_BINARY")
    if configured is None:
        pytest.skip("explicit measured native BLS artifact required")
    signature_path = Path(configured)
    artifact = signature_path.read_bytes()
    assert hashlib.sha256(artifact).hexdigest() == _NATIVE_SHA256
    case = _case(artifact=artifact)
    config = _configuration(case, signature_path, receipt_artifact)
    receipts = _receipt_exchange(monkeypatch, case.expected)
    with _create(tmp_path, case, config) as publisher:
        _publish(publisher, case)
        final = publisher.snapshot()
    history = tmp_path / "custody.sqlite", case, config, final, receipts, []
    assert _audit(history) == final
    forged = _sign(case.candidate, scalar=42)
    record = _replace_retained_record(history[0], signature=forged.envelope.signature_bytes)
    before = history[0].read_bytes(), _logical_store(history[0])
    with pytest.raises(ValueError, match="signature rejected"):
        _audit(history, authentication_candidates=(forged,), expected_publication_id=record.publication_id)
    assert len(receipts) == 2
    assert (history[0].read_bytes(), _logical_store(history[0])) == before
