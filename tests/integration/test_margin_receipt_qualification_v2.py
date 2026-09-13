"""Exact publisher workload; real-receipt success requires explicit artifacts."""

import hashlib
import json
import os
import subprocess
import sys
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.perps_margin_receipt_v2 import replay_perps_margin_frame_v2
from src.integration.global_receipt_verifier_v1 import (
    GlobalReceiptVerifierErrorV1,
    GlobalReceiptVerifierV1,
)
from src.integration.isolated_custody_publisher_v2 import (
    CustodyPublicationStatusV2,
    IsolatedCustodyPublisherV2,
)
from tests.integration.test_authenticated_asset_lane_custody_receipt_v2 import _sign
from tests.integration.test_isolated_custody_publisher_v2 import _logical_store
from tests.integration.test_perps_margin_real_guest_v2 import _execute
from tests.integration.test_profiled_perps_margin_receipt_v2 import perps_margin_signed_case
from tools import qualify_margin_receipts_v2 as qualification


def test_measured_signature_artifact_rebinds_profile_and_authentication():
    original = perps_margin_signed_case()
    changed = perps_margin_signed_case(signature_artifact=b"different isolated BLS build")
    assert changed.profile.profile_id != original.profile.profile_id
    assert changed.global_pre.profile_root == changed.candidate.intent.profile_root == changed.profile.profile_id
    assert changed.candidate.envelope.signature_bytes != original.candidate.envelope.signature_bytes
    assert changed.request.occurrence.pre_state_root == changed.global_pre.state_root


def test_receipt_fifo_rejects_without_waiting_for_a_writer(tmp_path):
    fifo = tmp_path / "prover-receipt"
    os.mkfifo(fifo)
    code = """
from pathlib import Path
import sys
from tools.qualify_margin_receipts_v2 import read_bounded
try:
    read_bounded(Path(sys.argv[1]), 16)
except ValueError as error:
    if str(error) != 'evidence file type or size':
        raise
    print('rejected FIFO')
else:
    raise SystemExit('FIFO accepted')
"""
    result = subprocess.run([sys.executable, "-c", code, str(fifo)], capture_output=True, timeout=10)
    assert result.returncode == 0 and result.stdout == b"rejected FIFO\n", result.stderr


def test_receipt_acquisition_rejects_links_empty_and_oversize_files(tmp_path):
    regular = tmp_path / "receipt"
    regular.write_bytes(b"abc")
    assert qualification.read_bounded(regular, 3) == b"abc"
    with pytest.raises(ValueError):
        qualification.read_bounded(regular, 2)
    link = tmp_path / "linked-receipt"
    link.symlink_to(regular)
    with pytest.raises(OSError):
        qualification.read_bounded(link, 3)
    regular.write_bytes(b"")
    with pytest.raises(ValueError, match="empty"):
        qualification.read_bounded(regular, 3)


@pytest.fixture
def measured_paths():
    configured = tuple(os.environ.get(name) for name in (
        "ZENODEX_BLS_VERIFIER_TEST_BINARY", "ZENODEX_MARGIN_EXECUTOR", "ZENODEX_MARGIN_R0VM",
    ))
    if all(path is None for path in configured):
        pytest.skip("configure measured BLS, margin execution and r0vm artifacts")
    assert all(configured), "all three measured executable settings are required"
    signature, executor, r0vm = map(Path, configured)
    receipt = executor.parent.parent / "verify_margin_receipt_v2"
    assert all(path.is_absolute() and path.is_file() for path in (signature, receipt, executor, r0vm))
    return signature, receipt, executor, r0vm


def test_prepared_workload_is_deterministic_and_exact_guest_execution_agrees(measured_paths, tmp_path):
    signature, receipt, executor, r0vm = measured_paths
    first = qualification.prepare(signature, receipt, tmp_path / "first")
    second = qualification.prepare(signature, receipt, tmp_path / "second")
    assert first == second
    assert first["actual_signature_checks"] == 3
    assert first["production_authority"] is first["genuine_receipts_produced"] is False
    configuration, cases = qualification.build_workload(signature, receipt)
    assert [case.global_pre.height for case in cases] == [0, 1, 2]
    for index, case in enumerate(cases, 1):
        inner = qualification.frame(case)
        actual = _execute([str(executor), str(r0vm)], inner)
        assert actual.returncode == 0, actual.stderr
        expected = replay_perps_margin_frame_v2(inner)
        assert actual.stdout == expected.statement == (tmp_path / "first" / f"{index:02}.journal.json").read_bytes()
        assert (tmp_path / "first" / f"{index:02}.input.bin").read_bytes() == len(inner).to_bytes(4, "little") + inner
        assert (tmp_path / "first" / f"{index:02}.input.bin").read_bytes() == (tmp_path / "second" / f"{index:02}.input.bin").read_bytes()
        assert case.request.occurrence.profile_root == first["profile_root"]
        qualification.authenticate(case, configuration)
    assert expected.result.post_state.custody == expected.result.post_state.liabilities == ()
    assert expected.result.post_margin.economic_state.account("margin-a").status.value == "CLOSED"


@pytest.mark.parametrize("artifact", ("signature", "receipt"))
def test_substituted_executable_cannot_select_a_new_proving_context(measured_paths, tmp_path, artifact):
    signature, receipt, _, _ = measured_paths
    substituted = tmp_path / "substituted"
    raw = (signature if artifact == "signature" else receipt).read_bytes()
    substituted.write_bytes(raw[:-1] + bytes([raw[-1] ^ 1]))
    paths = (substituted, receipt) if artifact == "signature" else (signature, substituted)
    with pytest.raises(ValueError, match=f"{artifact} executable hash drift"):
        qualification.prepare(*paths, tmp_path / "packet")
    assert not (tmp_path / "packet").exists()


def test_actual_signature_and_receipt_rejections_leave_complete_store_unchanged(measured_paths, tmp_path):
    signature, receipt, _, _ = measured_paths
    configuration, cases = qualification.build_workload(signature, receipt)
    case = cases[0]
    database = tmp_path / "reject.sqlite"
    with IsolatedCustodyPublisherV2.create(
        database, case.global_pre, case.assets, configuration, margin_state=case.margin,
    ) as publisher:
        before = _logical_store(database)
        with pytest.raises(ValueError, match="signature rejected"):
            publisher.publish(_sign(case.candidate, scalar=18), case.request, receipt_bytes=b"{}")
        assert _logical_store(database) == before
        with pytest.raises(GlobalReceiptVerifierErrorV1) as failure:
            publisher.publish(case.candidate, case.request, receipt_bytes=b"{}")
        assert failure.value.reason.value == "VERIFICATION_REJECTED"
        assert _logical_store(database) == before
        # A good signature reaches receipt checking; a changed signed body does not.
        changed = replace(case.request, command=replace(case.request.command, amount_atoms=41))
        with pytest.raises(ValueError, match="body"):
            publisher.publish(case.candidate, changed, receipt_bytes=b"{}")
        assert _logical_store(database) == before


def test_genuine_receipts_commit_complete_lifecycle_and_survive_restart(measured_paths, tmp_path):
    configured = os.environ.get("ZENODEX_MARGIN_RECEIPTS")
    if configured is None:
        pytest.skip("genuine margin receipts unavailable; publication remains unqualified")
    signature, receipt, _, _ = measured_paths
    database = tmp_path / "qualified.sqlite"
    result = qualification.publish(signature, receipt, Path(configured), database)
    assert result["committed"] == 3 and result["production_authority"] is False
    assert result["retained_evidence_reverified"] is True
    before = database.read_bytes(), _logical_store(database)
    checked = subprocess.run([
        sys.executable, str(Path(qualification.__file__)), "audit",
        "--signature-verifier", str(signature), "--receipt-verifier", str(receipt),
        "--database", str(database), "--expected-publication-id", result["publication_id"],
        "--expected-authority-root", result["authority_root"],
    ], capture_output=True, timeout=120)
    assert checked.returncode == 0, checked.stderr
    audited = json.loads(checked.stdout)
    assert audited["publication_id"] == result["publication_id"]
    assert audited["authority_root"] == result["authority_root"]
    assert audited["post_state_root"] == result["post_state_root"]
    assert audited["verified_publications"] == 3 and audited["production_authority"] is False
    assert (database.read_bytes(), _logical_store(database)) == before


@pytest.fixture
def closed_qualification_history(measured_paths, tmp_path, monkeypatch):
    """Real BLS and complete economics; fabricated receipt acceptance only."""
    from src.integration import global_receipt_verifier_v1 as transport

    signature, receipt, _, _ = measured_paths
    configuration, cases = qualification.build_workload(signature, receipt)
    base = cases[0]
    database = tmp_path / "audit.sqlite"

    def fabricated_success(descriptor, request, timeout):
        return b"ZDXRV1OK" + hashlib.sha256(request).digest() + request[8:40], b"", 0

    with monkeypatch.context() as compromised:
        compromised.setattr(transport, "_invoke_v1", fabricated_success)
        with IsolatedCustodyPublisherV2.create(
            database, base.global_pre, base.assets, configuration, margin_state=base.margin,
        ) as publisher:
            for case in cases:
                outcome = publisher.publish(case.candidate, case.request, receipt_bytes=b"{}")
                assert outcome.status is CustodyPublicationStatusV2.COMMITTED
                if publisher.snapshot().sequence == 1:
                    earlier = database.read_bytes()
            final = publisher.snapshot()
    return signature, receipt, database, final, earlier, fabricated_success


def test_given_closed_history_when_audit_cli_runs_then_use_read_only_external_checkpoint(
    closed_qualification_history, monkeypatch, capsys,
):
    from src.integration import global_receipt_verifier_v1 as transport

    signature, receipt, database, final, _, fixture_receipt_verifier = closed_qualification_history
    # Only the receipt result is a double; BLS and the audit/store path run normally.
    monkeypatch.setattr(transport, "_invoke_v1", fixture_receipt_verifier)
    connect = IsolatedCustodyPublisherV2._connect

    def read_only_connection(self, *args, **kwargs):
        assert kwargs.get("access") == "ro", "audit attempted to acquire a writer"
        return connect(self, *args, **kwargs)

    monkeypatch.setattr(IsolatedCustodyPublisherV2, "_connect", read_only_connection)
    monkeypatch.setattr(sys, "argv", [
        "qualify_margin_receipts_v2.py", "audit", "--signature-verifier", str(signature),
        "--receipt-verifier", str(receipt), "--database", str(database),
        "--expected-publication-id", final.publication_id,
        "--expected-authority-root", final.authority.authority_root,
    ])
    before = database.read_bytes(), database.stat().st_mtime_ns, _logical_store(database)
    qualification.main()
    result = json.loads(capsys.readouterr().out)
    assert result["publication_id"] == final.publication_id
    assert result["authority_root"] == final.authority.authority_root
    assert result["post_state_root"] == final.global_state.state_root
    assert result["verified_publications"] == 3
    assert result["retained_evidence_reverified"] is True
    assert result["production_authority"] is False
    assert (database.read_bytes(), database.stat().st_mtime_ns, _logical_store(database)) == before


@pytest.mark.parametrize("substitution", (
    "older_database", "publication_checkpoint", "authority_checkpoint", "fabricated_receipt",
))
def test_given_substituted_history_when_independently_audited_then_reject_without_changes(
    closed_qualification_history, substitution,
):
    signature, receipt, database, final, earlier, _ = closed_qualification_history
    publication = final.publication_id
    authority = final.authority.authority_root
    if substitution == "older_database":
        database.write_bytes(earlier)
    elif substitution == "authority_checkpoint":
        authority = "0x" + "ff" * 32
    elif substitution == "publication_checkpoint":
        publication = "0x" + "ff" * 32
    before = database.read_bytes(), database.stat().st_mtime_ns, _logical_store(database)
    expected_error = GlobalReceiptVerifierErrorV1 if substitution == "fabricated_receipt" else ValueError
    with pytest.raises(expected_error) as failure:
        qualification.audit(
            signature, receipt, database, expected_publication_id=publication,
            expected_authority_root=authority,
        )
    if substitution == "fabricated_receipt":
        assert failure.value.reason.value == "VERIFICATION_REJECTED"
    else:
        assert str(failure.value) == "audit history differs from independently selected checkpoint"
    assert (database.read_bytes(), database.stat().st_mtime_ns, _logical_store(database)) == before


@pytest.mark.parametrize("missing", ("--database", "--expected-publication-id", "--expected-authority-root"))
def test_audit_cli_requires_database_and_both_independent_checkpoint_roots(missing, monkeypatch, capsys):
    arguments = {"--signature-verifier": "sig", "--receipt-verifier": "receipt", "--database": "db",
                 "--expected-publication-id": "0x" + "aa" * 32, "--expected-authority-root": "0x" + "bb" * 32}
    del arguments[missing]
    monkeypatch.setattr(sys, "argv", ["qualify_margin_receipts_v2.py", "audit"] + [
        value for item in arguments.items() for value in item
    ])
    with pytest.raises(SystemExit) as failure:
        qualification.main()
    assert failure.value.code == 2
    assert f"required: {missing}" in capsys.readouterr().err


def test_actual_receipt_verifier_rejects_fabricated_but_consistent_history(measured_paths, tmp_path, monkeypatch):
    from src.integration import global_receipt_verifier_v1 as transport

    signature, receipt, _, _ = measured_paths
    configuration, cases = qualification.build_workload(signature, receipt)
    case = cases[0]
    database = tmp_path / "forged-history.sqlite"
    # Simulate a compromised publication-time receipt result. Real BLS is
    # still required. The audit below restores the actual measured endpoint.
    def fabricated_success(descriptor, request, timeout):
        return b"ZDXRV1OK" + hashlib.sha256(request).digest() + request[8:40], b"", 0

    with IsolatedCustodyPublisherV2.create(
        database, case.global_pre, case.assets, configuration, margin_state=case.margin,
    ) as publisher:
        with monkeypatch.context() as compromised:
            compromised.setattr(transport, "_invoke_v1", fabricated_success)
            result = publisher.publish(case.candidate, case.request, receipt_bytes=b"{}")
            assert result.status is CustodyPublicationStatusV2.COMMITTED
        final = publisher.snapshot()
    before = database.read_bytes(), _logical_store(database)
    with pytest.raises(GlobalReceiptVerifierErrorV1) as failure:
        IsolatedCustodyPublisherV2.audit(
            database, case.global_pre, case.assets, configuration, margin_state=case.margin,
            authentication_candidates=(case.candidate,), expected_publication_id=final.publication_id,
            expected_authority_root=final.authority.authority_root,
        )
    assert failure.value.reason.value == "VERIFICATION_REJECTED"
    assert (database.read_bytes(), _logical_store(database)) == before


def test_genuine_receipt_substitution_and_reordering_cannot_change_the_store(measured_paths, tmp_path):
    configured = os.environ.get("ZENODEX_MARGIN_RECEIPTS")
    if configured is None:
        pytest.skip("genuine receipt substitution controls require actual proofs")
    signature, receipt, _, _ = measured_paths
    configuration, cases = qualification.build_workload(signature, receipt)
    raw = tuple(qualification.read_bounded(
        Path(configured) / f"{index:02}.receipt.json", qualification.MAX_RECEIPT_BYTES_V1,
    ) for index in range(1, 4))
    first = cases[0]
    image = configuration.margin_role.evidence_manifest.root_image_id
    digest = hashlib.sha256(receipt.read_bytes()).hexdigest()
    journal = replay_perps_margin_frame_v2(qualification.frame(first)).statement
    verifier = GlobalReceiptVerifierV1(str(receipt), digest, image, 30_000)
    verifier.verify_succinct_receipt(raw[0], expected_image_id=image, expected_journal_bytes=journal)
    foreign_image = "0x" + "fe" * 32
    for selected, expected_journal in ((image, b"foreign journal"), (foreign_image, journal)):
        foreign = GlobalReceiptVerifierV1(str(receipt), digest, selected, 30_000)
        with pytest.raises(GlobalReceiptVerifierErrorV1) as failure:
            foreign.verify_succinct_receipt(raw[0], expected_image_id=selected, expected_journal_bytes=expected_journal)
        assert failure.value.reason.value == "VERIFICATION_REJECTED"
    database = tmp_path / "substitution.sqlite"
    with IsolatedCustodyPublisherV2.create(
        database, first.global_pre, first.assets, configuration, margin_state=first.margin,
    ) as publisher:
        assert publisher.publish(first.candidate, first.request, receipt_bytes=raw[0]).status is CustodyPublicationStatusV2.COMMITTED
        before = _logical_store(database)
        with pytest.raises(GlobalReceiptVerifierErrorV1) as failure:
            publisher.publish(cases[1].candidate, cases[1].request, receipt_bytes=raw[0])
        assert failure.value.reason.value == "VERIFICATION_REJECTED"
        assert _logical_store(database) == before
        stale = publisher.publish(cases[2].candidate, cases[2].request, receipt_bytes=raw[2])
        assert stale.status is CustodyPublicationStatusV2.STALE_HEAD
        assert _logical_store(database) == before
