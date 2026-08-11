from __future__ import annotations

import json
import os
import selectors
import subprocess
import sys
import time
from contextlib import contextmanager
from dataclasses import replace
from pathlib import Path
from typing import Any, BinaryIO, cast

import pytest

import src.integration.m6_durable_store_v1 as durable_store
from src.core.m6_authority_evidence_v1 import (
    _issue_m6_execution_context_verification_receipt_v1,
    _issue_m6_finality_verification_receipt_v1,
    verify_authenticated_execution_context_v1,
)
from src.core.m6_safe_mount_transition_v1 import run_m6_transition_v1
from src.core.m6_safe_mount_types_v1 import (
    _VERIFIED_ZRPF_TOKEN,
    MAX_ATOMS_V1,
    ZRPF_COMMAND_COUNT_V1,
    AcceptCandidateV1,
    AuthenticatedExecutionContextV1,
    BusinessStatusV1,
    EconomicAtomKindV1,
    EconomicAtomV1,
    FinalityModeV1,
    FreshnessBoundsV1,
    GlobalCommandKindV1,
    GlobalCommandV1,
    M6ApplicationStateV1,
    M6DurabilityProfileV1,
    M6ExecutionContextClaimsV1,
    M6PromotionSubjectV1,
    OracleContextV1,
    OutboxAtomV1,
    TauBatchCertificateV1,
    VerifiedZenoLedgerFinalityV1,
    VerifiedZRPFRootV1,
    ZenoLedgerFinalityCertificateV1,
    canonical_bytes_v1,
    hash_v1,
    initial_application_state_v1,
    ordered_root_v1,
)
from src.core.m6_safe_mount_types_v1 import (
    verify_zeno_ledger_finality_v1 as _verify_zeno_ledger_finality_v1,
)
from src.core.m6_zrpf_v1 import (
    DirectBatchCandidateV1,
    ZRPFBatchCandidateV1,
    _issue_m6_zrpf_verification_receipt_v1,
    direct_candidate_data_availability_projection_v1,
    execute_direct_batch_v1,
    execute_zrpf_batch_v1,
    verify_zrpf_root_v1,
)
from src.integration.m6_commit_port_v1 import CommitStatusV1, _decode_replay_body
from src.integration.m6_durable_store_v1 import (
    M6DurableCorruptionError,
    _decode_subject,
    _validate_cross_block_publication,
)
from src.integration.m6_durable_store_v1 import (
    M6DurableLedgerStoreV1 as _M6DurableLedgerStoreV1,
)

_FRESH_REOPEN_CODE = """
import json
import sys
from pathlib import Path

from src.core.m6_safe_mount_types_v1 import DEFAULT_DURABILITY_JSON_BYTES_V1
from src.integration.m6_durable_store_v1 import (
    M6DurableCorruptionError,
    M6DurableLedgerStoreV1,
    _decode_subject,
    _read_canonical_json,
)

root = Path(sys.argv[1])
subject_path = Path(sys.argv[2])
subject_raw, _ = _read_canonical_json(
    subject_path,
    max_bytes=DEFAULT_DURABILITY_JSON_BYTES_V1,
)
subject = _decode_subject(subject_raw)
try:
    reopened = M6DurableLedgerStoreV1(root, subject).reopen()
except M6DurableCorruptionError as exc:
    print(f"corruption:{exc}")
    raise SystemExit(2)
print(json.dumps({
    "head_block_id": reopened.head_block_id,
    "state_root": reopened.state.state_root,
    "chain_block_ids": reopened.chain_block_ids,
}, sort_keys=True))
"""

_CONCURRENT_CREATE_CODE = """
import json
import sys
from pathlib import Path

from src.core.m6_safe_mount_types_v1 import (
    DEFAULT_DURABILITY_JSON_BYTES_V1,
    initial_application_state_v1,
)
from src.integration.m6_durable_store_v1 import (
    M6DurableCorruptionError,
    M6DurableLedgerStoreV1,
    _decode_subject,
    _read_canonical_json,
)

root = Path(sys.argv[1])
subject_path = Path(sys.argv[2])
subject_raw, _ = _read_canonical_json(
    subject_path,
    max_bytes=DEFAULT_DURABILITY_JSON_BYTES_V1,
)
subject = _decode_subject(subject_raw)
print("ready", flush=True)
if sys.stdin.buffer.read(1) != b"x":
    raise SystemExit("create worker did not receive its release byte")
try:
    M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))
except FileExistsError as exc:
    print(json.dumps({"error": type(exc).__name__, "status": "rejected"}), flush=True)
except M6DurableCorruptionError as exc:
    print(json.dumps({"error": type(exc).__name__, "status": "rejected"}), flush=True)
else:
    print(json.dumps({"status": "created"}), flush=True)
"""

_LOCK_HOLD_CODE = """
import sys
from pathlib import Path

from src.core.m6_safe_mount_types_v1 import DEFAULT_DURABILITY_JSON_BYTES_V1
from src.integration.m6_durable_store_v1 import (
    M6DurableLedgerStoreV1,
    _decode_subject,
    _read_canonical_json,
)

root = Path(sys.argv[1])
subject_path = Path(sys.argv[2])
subject_raw, _ = _read_canonical_json(
    subject_path,
    max_bytes=DEFAULT_DURABILITY_JSON_BYTES_V1,
)
subject = _decode_subject(subject_raw)
store = M6DurableLedgerStoreV1(root, subject)
with store._file_lock(create_lock=True):
    print("locked", flush=True)
    sys.stdin.buffer.read(1)
"""

_LOCK_WAIT_CODE = """
import fcntl
import os
import sys
from pathlib import Path

from src.core.m6_safe_mount_types_v1 import DEFAULT_DURABILITY_JSON_BYTES_V1
from src.integration.m6_durable_store_v1 import (
    LOCK_FILE_V1,
    _decode_subject,
    _read_canonical_json,
)

root = Path(sys.argv[1])
subject_path = Path(sys.argv[2])
subject_raw, _ = _read_canonical_json(
    subject_path,
    max_bytes=DEFAULT_DURABILITY_JSON_BYTES_V1,
)
subject = _decode_subject(subject_raw)
lock_fd = os.open(root / LOCK_FILE_V1, os.O_RDWR | getattr(os, "O_NOFOLLOW", 0))
print("ready", flush=True)
try:
    try:
        fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("blocked", flush=True)
        if sys.stdin.buffer.read(1) != b"x":
            raise SystemExit("lock waiter did not receive its release byte")
        fcntl.flock(lock_fd, fcntl.LOCK_EX)
        print("acquired", flush=True)
    else:
        print("acquired", flush=True)
finally:
    fcntl.flock(lock_fd, fcntl.LOCK_UN)
    os.close(lock_fd)
"""


def _fresh_reopen(root: Path, subject: M6PromotionSubjectV1, probe: Path) -> subprocess.CompletedProcess[str]:
    probe.write_bytes(canonical_bytes_v1(subject))
    repo_root = Path(__file__).resolve().parents[2]
    environment = os.environ.copy()
    existing_pythonpath = environment.get("PYTHONPATH")
    environment["PYTHONPATH"] = str(repo_root) + (
        os.pathsep + existing_pythonpath if existing_pythonpath else ""
    )
    return subprocess.run(
        [sys.executable, "-c", _FRESH_REOPEN_CODE, str(root), str(probe)],
        cwd=repo_root,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )


def _await_lines(
    workers: list[subprocess.Popen[bytes]],
    expected: bytes,
    *,
    timeout_seconds: float = 30.0,
) -> None:
    selector = selectors.DefaultSelector()
    try:
        for index, worker in enumerate(workers):
            assert worker.stdout is not None
            selector.register(worker.stdout, selectors.EVENT_READ, data=index)
        deadline = time.monotonic() + timeout_seconds
        for _ in workers:
            remaining = deadline - time.monotonic()
            assert remaining > 0, "worker readiness deadline expired"
            events = selector.select(remaining)
            assert events, f"worker did not emit {expected!r} before deadline"
            key, _ = events[0]
            line = cast(BinaryIO, key.fileobj).readline().strip()
            assert line == expected, f"worker emitted {line!r}, expected {expected!r}"
            selector.unregister(key.fileobj)
    finally:
        selector.close()


def _await_line_sequence(
    worker: subprocess.Popen[bytes],
    expected_lines: tuple[bytes, ...],
    *,
    timeout_seconds: float = 30.0,
) -> None:
    assert worker.stdout is not None
    file_descriptor = worker.stdout.fileno()
    previous_blocking = os.get_blocking(file_descriptor)
    os.set_blocking(file_descriptor, False)
    selector = selectors.DefaultSelector()
    buffer = b""
    observed: list[bytes] = []
    try:
        selector.register(file_descriptor, selectors.EVENT_READ)
        deadline = time.monotonic() + timeout_seconds
        while len(observed) < len(expected_lines):
            remaining = deadline - time.monotonic()
            assert remaining > 0, "worker line-sequence deadline expired"
            assert selector.select(remaining), (
                f"worker did not emit {expected_lines[len(observed)]!r} before deadline"
            )
            try:
                chunk = os.read(file_descriptor, 4096)
            except BlockingIOError:
                continue
            assert chunk, "worker closed stdout before completing its line sequence"
            buffer += chunk
            while b"\n" in buffer and len(observed) < len(expected_lines):
                line, buffer = buffer.split(b"\n", 1)
                line = line.rstrip(b"\r")
                expected = expected_lines[len(observed)]
                assert line == expected, f"worker emitted {line!r}, expected {expected!r}"
                observed.append(line)
    finally:
        selector.close()
        os.set_blocking(file_descriptor, previous_blocking)


def _concurrent_creates(
    root: Path,
    subject: M6PromotionSubjectV1,
    probe: Path,
) -> list[tuple[int, dict[str, str]]]:
    probe.write_bytes(canonical_bytes_v1(subject))
    repo_root = Path(__file__).resolve().parents[2]
    environment = os.environ.copy()
    existing_pythonpath = environment.get("PYTHONPATH")
    environment["PYTHONPATH"] = str(repo_root) + (
        os.pathsep + existing_pythonpath if existing_pythonpath else ""
    )
    workers = [
        subprocess.Popen(
            [sys.executable, "-c", _CONCURRENT_CREATE_CODE, str(root), str(probe)],
            cwd=repo_root,
            env=environment,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        for _ in range(2)
    ]
    try:
        _await_lines(workers, b"ready")
        for worker in workers:
            assert worker.stdin is not None
            worker.stdin.write(b"x")
            worker.stdin.close()
        results: list[tuple[int, dict[str, str]]] = []
        for worker in workers:
            return_code = worker.wait(timeout=30)
            assert worker.stdout is not None
            output = worker.stdout.read().splitlines()
            assert len(output) == 1
            results.append((return_code, json.loads(output[0].decode("utf-8"))))
        return results
    finally:
        for worker in workers:
            if worker.poll() is None:
                worker.kill()
            try:
                worker.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass


def _lock_handoff(root: Path, subject: M6PromotionSubjectV1, probe: Path) -> None:
    root.mkdir()
    probe.write_bytes(canonical_bytes_v1(subject))
    repo_root = Path(__file__).resolve().parents[2]
    environment = os.environ.copy()
    existing_pythonpath = environment.get("PYTHONPATH")
    environment["PYTHONPATH"] = str(repo_root) + (
        os.pathsep + existing_pythonpath if existing_pythonpath else ""
    )
    holder = subprocess.Popen(
        [sys.executable, "-c", _LOCK_HOLD_CODE, str(root), str(probe)],
        cwd=repo_root,
        env=environment,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    waiter: subprocess.Popen[bytes] | None = None
    try:
        _await_lines([holder], b"locked")
        waiter = subprocess.Popen(
            [sys.executable, "-c", _LOCK_WAIT_CODE, str(root), str(probe)],
            cwd=repo_root,
            env=environment,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        _await_line_sequence(waiter, (b"ready", b"blocked"))
        assert holder.stdin is not None
        holder.stdin.write(b"x")
        holder.stdin.close()
        assert waiter.stdin is not None
        waiter.stdin.write(b"x")
        waiter.stdin.close()
        assert holder.wait(timeout=30) == 0
        assert waiter.wait(timeout=30) == 0
        waiter_stdout = waiter.stdout
        assert waiter_stdout is not None
        assert waiter_stdout.read().splitlines() == [b"acquired"]
    finally:
        for worker in (holder, waiter):
            if worker is None:
                continue
            if worker.poll() is None:
                worker.kill()
            try:
                worker.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _subject() -> M6PromotionSubjectV1:
    return M6PromotionSubjectV1(
        source=_root(1),
        proof=_root(2),
        build=_root(3),
        schema=_root(4),
        deployment=_root(5),
        chain_id=_root(11),
        verifier=_root(6),
        tau_profile=_root(7),
        validator_set=_root(8),
        writer_epoch=0,
        managed_asset_policy=_root(9),
        risc0_image=_root(10),
        destination_adapter_roots=(),
    )


def _command(nonce: int, *, auction_id: str) -> GlobalCommandV1:
    return GlobalCommandV1(
        kind=GlobalCommandKindV1.SELLER_AUCTION_CANCEL,
        command_id=_root(1_000 + nonce),
        sender="alice",
        nonce=nonce,
        payload={"auction_id": auction_id},
    )


class _TestExecutionContextVerifier:
    def verify_execution_context(self, claims: M6ExecutionContextClaimsV1):
        assert claims.authentication_root
        return _issue_m6_execution_context_verification_receipt_v1(
            claims,
            attestation_root=claims.authentication_root,
        )


_TEST_EXECUTION_CONTEXT_VERIFIER = _TestExecutionContextVerifier()


class _TestZRPFReceiptVerifier:
    def verify_zrpf_receipt(self, subject, batch, journal):
        return _issue_m6_zrpf_verification_receipt_v1(
            promotion_subject_root=subject.subject_root,
            profile=journal.profile,
            verifier_image=journal.verifier_image,
            journal_root=journal.journal_root,
            data_availability_root=journal.data_availability_root,
            attestation_root=hash_v1(
                "test-m6-zrpf-attestation-v1",
                {"candidate_id": batch.candidate_id, "journal_root": journal.journal_root},
            ),
        )


_TEST_ZRPF_RECEIPT_VERIFIER = _TestZRPFReceiptVerifier()


def _context(subject: M6PromotionSubjectV1, state: M6ApplicationStateV1, nonce: int) -> AuthenticatedExecutionContextV1:
    return verify_authenticated_execution_context_v1(
        deployment=subject.deployment,
        chain_id=subject.chain_id,
        parent_head=state.head,
        epoch=state.writer_epoch,
        sender="alice",
        nonce=nonce,
        oracle_context=OracleContextV1(_root(100), observed_height=10, oracle_height=10),
        tau_profile=subject.tau_profile,
        verifier_registry=subject.verifier,
        freshness_bounds=FreshnessBoundsV1(2, 2, 2),
        verifier=_TEST_EXECUTION_CONTEXT_VERIFIER,
    )


def _candidate(subject: M6PromotionSubjectV1, state: M6ApplicationStateV1, nonce: int, auction_id: str):
    command = _command(nonce, auction_id=auction_id)
    result = run_m6_transition_v1(subject, state, _context(subject, state, nonce), command)
    assert isinstance(result, AcceptCandidateV1)
    return result


def _finality_and_tau(
    subject: M6PromotionSubjectV1,
    candidate: AcceptCandidateV1,
    batch_id: str,
) -> tuple[VerifiedZenoLedgerFinalityV1, TauBatchCertificateV1]:
    command = candidate.command
    tau = TauBatchCertificateV1(
        batch_id=batch_id,
        tau_profile_root=subject.tau_profile,
        chain_id=subject.chain_id,
        ordered_command_hashes=(command.command_hash,),
        ordered_nonce_identities=(command.nonce_identity,),
        candidate_parent_head=candidate.context.parent_head,
        certificate_root=hash_v1(
            "m6-tau-batch-certificate-v1",
            {
                "batch_id": batch_id,
                "tau_profile_root": subject.tau_profile,
                "chain_id": subject.chain_id,
                "ordered_command_hashes": (command.command_hash,),
                "ordered_nonce_identities": (command.nonce_identity,),
                "candidate_parent_head": candidate.context.parent_head,
            },
        ),
    )
    certificate = ZenoLedgerFinalityCertificateV1(
        finality_id=_root(900),
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        chain_id=subject.chain_id,
        validator_set_root=subject.validator_set,
        writer_epoch=candidate.post_state.writer_epoch,
        signer_ids=("v1", "v2", "v3", "v4", "v5"),
        quorum=5,
        mode=FinalityModeV1.TAU_ORDERED,
        signature_root=_root(901),
    )
    finality = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        candidate_parent_head=candidate.context.parent_head,
        expected_command_root=ordered_root_v1(
            "m6-direct-command-root-v1",
            (command.command_hash,),
        ),
        expected_nonce_root=ordered_root_v1(
            "m6-direct-nonce-root-v1",
            (command.nonce_identity,),
        ),
        certificate=certificate,
        tau_certificate=tau,
    )
    return finality, tau


def _finality_and_tau_for_direct_batch(
    subject: M6PromotionSubjectV1,
    initial: M6ApplicationStateV1,
    direct: DirectBatchCandidateV1,
) -> tuple[VerifiedZenoLedgerFinalityV1, TauBatchCertificateV1]:
    command_hashes = tuple(command.command_hash for command in direct.commands)
    nonce_identities = tuple(command.nonce_identity for command in direct.commands)
    batch_id = "direct-batch-mutant"
    tau = TauBatchCertificateV1(
        batch_id=batch_id,
        tau_profile_root=subject.tau_profile,
        chain_id=subject.chain_id,
        ordered_command_hashes=command_hashes,
        ordered_nonce_identities=nonce_identities,
        candidate_parent_head=direct.pre_head,
        certificate_root=hash_v1(
            "m6-tau-batch-certificate-v1",
            {
                "batch_id": batch_id,
                "tau_profile_root": subject.tau_profile,
                "chain_id": subject.chain_id,
                "ordered_command_hashes": command_hashes,
                "ordered_nonce_identities": nonce_identities,
                "candidate_parent_head": direct.pre_head,
            },
        ),
    )
    certificate = ZenoLedgerFinalityCertificateV1(
        finality_id=_root(992),
        candidate_head=direct.post_state_root,
        publication_root=direct.publication_root,
        chain_id=subject.chain_id,
        validator_set_root=subject.validator_set,
        writer_epoch=initial.writer_epoch,
        signer_ids=("v1", "v2", "v3", "v4", "v5"),
        quorum=5,
        mode=FinalityModeV1.TAU_ORDERED,
        signature_root=_root(993),
    )
    return (
        verify_zeno_ledger_finality_v1(
            subject,
            candidate_head=direct.post_state_root,
            publication_root=direct.publication_root,
            candidate_parent_head=direct.pre_head,
            expected_writer_epoch=initial.writer_epoch,
            expected_command_root=direct.command_root,
            expected_nonce_root=direct.nonce_root,
            certificate=certificate,
            tau_certificate=tau,
        ),
        tau,
    )


class _TestFinalityVerifier:
    """Research fixture for the external finality-verifier port."""

    def verify_finality(self, subject: M6PromotionSubjectV1, **kwargs: object):
        certificate = cast(ZenoLedgerFinalityCertificateV1, kwargs["certificate"])
        return _issue_m6_finality_verification_receipt_v1(
            subject_root=subject.subject_root,
            candidate_parent_head=cast(str, kwargs["candidate_parent_head"]),
            candidate_head=cast(str, kwargs["candidate_head"]),
            publication_root=cast(str, kwargs["publication_root"]),
            expected_writer_epoch=cast(int, kwargs["expected_writer_epoch"]),
            certificate_root=certificate.certificate_root,
            attestation_root=certificate.signature_root,
        )


_TEST_FINALITY_VERIFIER = _TestFinalityVerifier()


class M6DurableLedgerStoreV1(_M6DurableLedgerStoreV1):
    """Inject the explicitly labelled research verifier into test stores."""

    @classmethod
    def create(cls, root, subject, initial_state):
        return super().create(
            root,
            subject,
            initial_state,
            finality_verifier=_TEST_FINALITY_VERIFIER,
        )


def verify_zeno_ledger_finality_v1(
    subject: M6PromotionSubjectV1,
    **kwargs: object,
) -> VerifiedZenoLedgerFinalityV1:
    """Test adapter standing in for the external cryptographic verifier port."""

    certificate = cast(ZenoLedgerFinalityCertificateV1, kwargs["certificate"])
    parent_head = cast(str, kwargs["candidate_parent_head"])
    expected_epoch = cast(int, kwargs.pop("expected_writer_epoch", certificate.writer_epoch))
    receipt = kwargs.pop("verification_receipt", None)
    if receipt is None:
        receipt = _issue_m6_finality_verification_receipt_v1(
            subject_root=subject.subject_root,
            candidate_parent_head=parent_head,
            candidate_head=certificate.candidate_head,
            publication_root=certificate.publication_root,
            expected_writer_epoch=expected_epoch,
            certificate_root=certificate.certificate_root,
            attestation_root=certificate.signature_root,
        )
    return _verify_zeno_ledger_finality_v1(
        subject,
        expected_writer_epoch=expected_epoch,
        verification_receipt=cast(object, receipt),
        **cast(dict[str, object], kwargs),
    )


def _zrpf_inputs(subject: M6PromotionSubjectV1, state: M6ApplicationStateV1):
    contexts: list[AuthenticatedExecutionContextV1] = []
    commands: list[GlobalCommandV1] = []
    current = state
    for nonce in range(1, ZRPF_COMMAND_COUNT_V1 + 1):
        command = _command(nonce, auction_id=f"auction-{nonce}")
        context = _context(subject, current, nonce)
        preview = run_m6_transition_v1(subject, current, context, command)
        assert isinstance(preview, AcceptCandidateV1)
        contexts.append(context)
        commands.append(command)
        current = preview.post_state
    return tuple(contexts), tuple(commands)


def _zrpf_finality_and_tau(
    subject: M6PromotionSubjectV1,
    state: M6ApplicationStateV1,
    verified: VerifiedZRPFRootV1,
) -> tuple[VerifiedZenoLedgerFinalityV1, TauBatchCertificateV1]:
    execution_batch = cast(ZRPFBatchCandidateV1, verified.execution_batch)
    command_hashes = tuple(command.command_hash for command in execution_batch.direct.commands)
    nonce_identities = tuple(command.nonce_identity for command in execution_batch.direct.commands)
    tau = TauBatchCertificateV1(
        batch_id="zrpf-batch-1",
        tau_profile_root=subject.tau_profile,
        chain_id=subject.chain_id,
        ordered_command_hashes=command_hashes,
        ordered_nonce_identities=nonce_identities,
        candidate_parent_head=state.head,
        certificate_root=hash_v1(
            "m6-tau-batch-certificate-v1",
            {
                "batch_id": "zrpf-batch-1",
                "tau_profile_root": subject.tau_profile,
                "chain_id": subject.chain_id,
                "ordered_command_hashes": command_hashes,
                "ordered_nonce_identities": nonce_identities,
                "candidate_parent_head": state.head,
            },
        ),
    )
    certificate = ZenoLedgerFinalityCertificateV1(
        finality_id=_root(901),
        candidate_head=verified.post_state.state_root,
        publication_root=verified.journal.journal_root,
        chain_id=subject.chain_id,
        validator_set_root=subject.validator_set,
        writer_epoch=state.writer_epoch,
        signer_ids=("v1", "v2", "v3", "v4", "v5"),
        quorum=5,
        mode=FinalityModeV1.TAU_ORDERED,
        signature_root=_root(902),
        execution_receipt_root=verified.proof_receipt.receipt_root,
    )
    finality = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=verified.post_state.state_root,
        publication_root=verified.journal.journal_root,
        candidate_parent_head=state.head,
        expected_command_root=verified.journal.command_root,
        expected_nonce_root=verified.journal.nonce_root,
        expected_execution_receipt_root=verified.proof_receipt.receipt_root,
        certificate=certificate,
        tau_certificate=tau,
    )
    return finality, tau


def test_reopen_reconstructs_canonical_chain_and_retry_is_idempotent(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    candidate = _candidate(subject, initial, 1, "auction-1")
    finality, tau = _finality_and_tau(subject, candidate, "batch-1")

    committed = store.publish(candidate, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED
    assert committed.block_id is not None

    reopened = M6DurableLedgerStoreV1(tmp_path / "ledger", subject).reopen()
    assert reopened.state.state_root == committed.state.state_root
    assert reopened.chain_block_ids == ("genesis", committed.block_id)
    assert len(reopened.records) == 1
    assert reopened.records[0] == committed.record
    assert committed.record is not None
    assert committed.record.finality_receipt is not None
    assert reopened.records[0].finality_receipt == committed.record.finality_receipt

    retry = store.publish(candidate, finality, tau)
    assert retry.status is CommitStatusV1.ALREADY_COMMITTED
    assert retry.block_id == committed.block_id
    assert retry.record == committed.record

    conflicting_finality = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        candidate_parent_head=candidate.context.parent_head,
        expected_command_root=finality.expected_command_root,
        expected_nonce_root=finality.expected_nonce_root,
        certificate=replace(finality.certificate, signature_root=_root(902)),
        tau_certificate=tau,
    )
    conflict = store.publish(candidate, conflicting_finality, tau)
    assert conflict.status is CommitStatusV1.FINALITY_REJECTED
    assert conflict.reason is not None
    assert store.reopen().head_block_id == committed.block_id


def test_reopen_of_absent_root_is_read_only_and_create_retry_succeeds(tmp_path: Path) -> None:
    """BDD/RIPR: a failed read cannot create a partial root that blocks genesis."""

    subject = _subject()
    root = tmp_path / "ledger"

    # Arrange: the caller has only allocated the parent directory.
    with pytest.raises(M6DurableCorruptionError, match="durable root"):
        # Act: probing an absent ledger must reject without creating layout.
        M6DurableLedgerStoreV1(root, subject).reopen()

    # Assert: the failed read has no filesystem effect and a valid create can retry.
    assert not root.exists()
    store = M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))
    assert store.reopen().head_block_id == "genesis"


def test_handle_created_before_root_binds_first_inode_and_rejects_replacement(
    tmp_path: Path,
) -> None:
    """RIPR: a retained pre-create handle cannot follow a replacement root."""

    subject = _subject()
    root = tmp_path / "ledger"
    retained = M6DurableLedgerStoreV1(root, subject)

    created = M6DurableLedgerStoreV1.create(
        root,
        subject,
        initial_application_state_v1(subject),
    )
    assert retained.reopen().head_block_id == "genesis"

    displaced = tmp_path / "displaced-ledger"
    root.rename(displaced)
    M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))

    with pytest.raises(M6DurableCorruptionError, match="root changed"):
        retained.reopen()
    with pytest.raises(M6DurableCorruptionError, match="root changed"):
        created.reopen()
    replacement = M6DurableLedgerStoreV1(root, subject)
    assert replacement.reopen().head_block_id == "genesis"


def test_reopen_of_existing_incomplete_root_does_not_add_layout_entries(tmp_path: Path) -> None:
    """RIPR: an incomplete existing root remains byte-for-byte unchanged on reject."""

    subject = _subject()
    root = tmp_path / "ledger"
    root.mkdir()
    # Arrange a valid lock so the read-only loader is reached.  Without this
    # file, reopen rejects in _file_lock before exercising _load_reopened_unlocked.
    (root / durable_store.LOCK_FILE_V1).write_bytes(b"")
    sentinel = root / "sentinel"
    sentinel.write_bytes(b"caller-owned")
    before = tuple(sorted((entry.name, entry.read_bytes()) for entry in root.iterdir()))

    with pytest.raises(M6DurableCorruptionError, match="durable"):
        M6DurableLedgerStoreV1(root, subject).reopen()

    after = tuple(sorted((entry.name, entry.read_bytes()) for entry in root.iterdir()))
    assert after == before


def test_create_rejects_file_root_without_mutation(tmp_path: Path) -> None:
    """BVA/RIPR: a non-directory root cannot become a durable authority."""

    subject = _subject()
    root = tmp_path / "ledger"
    root.write_bytes(b"caller-owned")

    with pytest.raises(M6DurableCorruptionError, match="root must be a directory"):
        M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))

    assert root.read_bytes() == b"caller-owned"


def test_create_rejects_root_symlinks_without_target_mutation(tmp_path: Path) -> None:
    """BVA/RIPR: directory and broken symlinks cannot redirect durable writes."""

    subject = _subject()
    target = tmp_path / "target"
    target.mkdir()
    directory_link = tmp_path / "directory-link"
    directory_link.symlink_to(target, target_is_directory=True)
    missing_target = tmp_path / "missing"
    broken_link = tmp_path / "broken-link"
    broken_link.symlink_to(missing_target, target_is_directory=True)

    for root in (directory_link, broken_link):
        with pytest.raises(M6DurableCorruptionError, match="root must not be a symlink"):
            M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))

    assert tuple(target.iterdir()) == ()
    assert directory_link.is_symlink()
    assert broken_link.is_symlink()
    assert not missing_target.exists()
    assert not missing_target.is_symlink()


def test_create_rejects_root_swap_between_validation_and_lock_open(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """RIPR: a root-directory swap cannot redirect the genesis bundle."""

    subject = _subject()
    root = tmp_path / "ledger"
    attacker = tmp_path / "attacker"
    displaced = tmp_path / "displaced"
    original_open = durable_store.os.open
    swapped = False

    def swapping_open(path: Any, flags: Any, *args: Any, **kwargs: Any) -> int:
        nonlocal swapped
        path_value = Path(path)
        lock_open = path_value == root / durable_store.LOCK_FILE_V1
        directory_fd_open = kwargs.get("dir_fd") is not None
        if not swapped and (lock_open or directory_fd_open):
            root.rename(displaced)
            attacker.mkdir()
            root.symlink_to(attacker, target_is_directory=True)
            swapped = True
        return original_open(path, flags, *args, **kwargs)

    monkeypatch.setattr(durable_store.os, "open", swapping_open)

    with pytest.raises(M6DurableCorruptionError, match="root changed during lock acquisition"):
        M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))

    assert swapped
    assert tuple(attacker.iterdir()) == ()
    assert tuple(displaced.iterdir()) == ()
    assert (tmp_path / ".ledger.m6-root.lock").is_file()


def test_lock_binds_all_later_io_to_original_root_after_path_swap(tmp_path: Path) -> None:
    """RIPR: post-lock pathname replacement cannot redirect durable reads or writes."""

    subject = _subject()
    root = tmp_path / "ledger"
    attacker = tmp_path / "attacker"
    displaced = tmp_path / "displaced"
    store = M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))

    with pytest.raises(
        M6DurableCorruptionError,
        match="configured durable root changed before commit acknowledgment",
    ):
        with store._file_lock():
            root.rename(displaced)
            attacker.mkdir()
            root.symlink_to(attacker, target_is_directory=True)
            store._load_reopened_unlocked()

    assert tuple(attacker.iterdir()) == ()
    assert {entry.name for entry in displaced.iterdir()} == {
        durable_store.LOCK_FILE_V1,
        durable_store.HEAD_FILE_V1,
        durable_store.BLOCKS_DIR_V1,
        durable_store.GENESIS_DIR_V1,
    }


def test_bound_root_helpers_reject_symlinked_descendant(tmp_path: Path) -> None:
    """RIPR: only the exact root descriptor may bypass symlink checks."""

    subject = _subject()
    root = tmp_path / "ledger"
    attacker = tmp_path / "attacker"
    displaced = tmp_path / "displaced-blocks"
    store = M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))
    attacker.mkdir()

    with store._file_lock():
        (root / durable_store.BLOCKS_DIR_V1).rename(displaced)
        (root / durable_store.BLOCKS_DIR_V1).symlink_to(attacker, target_is_directory=True)
        with pytest.raises(M6DurableCorruptionError, match="directory"):
            durable_store._ensure_directory(store._io_root() / durable_store.BLOCKS_DIR_V1)

    assert tuple(attacker.iterdir()) == ()
    assert tuple(displaced.iterdir()) == ()


def test_concurrent_create_has_exactly_one_winner(tmp_path: Path) -> None:
    """BDD/AAA/stateful: two writers racing for genesis yield one durable winner."""

    subject = _subject()
    root = tmp_path / "ledger"
    probe = tmp_path / "subject.json"

    results = _concurrent_creates(root, subject, probe)

    assert [code for code, _ in results] == [0, 0]
    statuses = [payload["status"] for _, payload in results]
    assert statuses.count("created") == 1
    assert statuses.count("rejected") == 1
    assert [payload.get("error") for _, payload in results if payload["status"] == "rejected"] == [
        "FileExistsError"
    ]
    reopened = M6DurableLedgerStoreV1(root, subject).reopen()
    assert reopened.head_block_id == "genesis"
    assert reopened.chain_block_ids == ("genesis",)
    assert reopened.records == ()
    assert {entry.name for entry in root.iterdir()} == {
        durable_store.LOCK_FILE_V1,
        durable_store.HEAD_FILE_V1,
        durable_store.BLOCKS_DIR_V1,
        durable_store.GENESIS_DIR_V1,
    }


def test_file_lock_blocks_competing_creator_until_release(tmp_path: Path) -> None:
    """RIPR: removing the exclusive lock must be observable before release."""

    _lock_handoff(tmp_path / "ledger", _subject(), tmp_path / "subject.json")


def test_create_enters_exclusive_lock_before_installing_genesis(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Architecture conformance: genesis creation must use the declared lock port."""

    calls: list[bool] = []
    original_file_lock = M6DurableLedgerStoreV1._file_lock

    @contextmanager
    def recording_file_lock(
        store: M6DurableLedgerStoreV1,
        *,
        create_lock: bool = False,
    ):
        calls.append(create_lock)
        with original_file_lock(store, create_lock=create_lock):
            yield

    monkeypatch.setattr(M6DurableLedgerStoreV1, "_file_lock", recording_file_lock)
    root = tmp_path / "ledger"
    subject = _subject()
    M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))

    assert calls == [True]


def test_durable_genesis_rejects_inconsistent_zusd_supply_and_debt(tmp_path: Path) -> None:
    """RIPR/mutation: durable authority cannot install forged monetary state."""

    subject = _subject()
    root = tmp_path / "ledger"
    invalid = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.SUPPLY, "__supply__", "zUSD", "ledger", 1),),
    )

    with pytest.raises(ValueError, match="zUSD supply/debt mismatch"):
        M6DurableLedgerStoreV1.create(root, subject, invalid)
    assert not root.exists()

    store = M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))
    assert store.reopen().state == initial_application_state_v1(subject)


def test_durable_decode_rejects_bad_enum_as_corruption() -> None:
    """RIPR/BVA: corrupted enum bytes stay inside the durable error algebra."""

    subject = _subject()
    raw_state = json.loads(canonical_bytes_v1(initial_application_state_v1(subject)))
    migration = dict(raw_state["migration"])
    migration["phase"] = "invalid-phase"
    raw_state["migration"] = migration

    with pytest.raises(M6DurableCorruptionError, match="migration phase is invalid"):
        durable_store._decode_state(raw_state)


def test_durable_decode_wraps_constructor_invariant_failures() -> None:
    """RIPR/BVA: typed-constructor failures stay in the durable error algebra."""

    subject = _subject()
    initial = initial_application_state_v1(subject)
    candidate = _candidate(subject, initial, 1, "decode-constructor")
    finality, _ = _finality_and_tau(subject, candidate, "decode-constructor-batch")
    raw_finality = dict(finality.certificate.to_canonical())
    raw_finality["signer_ids"] = ["v2", "v1", "v3", "v4", "v5"]

    with pytest.raises(M6DurableCorruptionError, match="invalid finality certificate"):
        durable_store._decode_finality(raw_finality)

    raw_state = json.loads(canonical_bytes_v1(initial))
    raw_state["finality_certificates"] = [raw_finality]
    with pytest.raises(M6DurableCorruptionError, match="invalid finality certificate"):
        durable_store._decode_state(raw_state)


def test_durable_genesis_rejects_unbacked_non_zusd_supply_without_artifacts(tmp_path: Path) -> None:
    """RIPR: unsupported issuance fails before filesystem authority exists."""

    subject = _subject()
    root = tmp_path / "ledger"
    invalid = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.SUPPLY, "__supply__", "PROTO", "ledger", 1),),
    )

    with pytest.raises(ValueError, match="non-zUSD supply requires a mounted issuance kernel"):
        M6DurableLedgerStoreV1.create(root, subject, invalid)
    assert not root.exists()

    store = M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))
    assert store.reopen().state == initial_application_state_v1(subject)


def test_durable_genesis_rejects_aggregate_overflow_without_artifacts(tmp_path: Path) -> None:
    """BVA/RIPR: aggregate overflow fails before filesystem authority exists."""

    subject = _subject()
    root = tmp_path / "ledger"
    invalid = replace(
        initial_application_state_v1(subject),
        economic_atoms=(
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", MAX_ATOMS_V1),
            EconomicAtomV1(EconomicAtomKindV1.BALANCE, "bob", "A", "ledger", 1),
        ),
    )

    with pytest.raises(ValueError, match="economic aggregate exceeds 128-bit atom domain"):
        M6DurableLedgerStoreV1.create(root, subject, invalid)
    assert not root.exists()

    store = M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))
    assert store.reopen().state == initial_application_state_v1(subject)


def test_durable_replay_rejects_finality_from_a_foreign_promotion_subject(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    candidate = _candidate(subject, initial, 1, "foreign-finality")
    finality, tau = _finality_and_tau(subject, candidate, "foreign-finality-batch")
    committed = store.publish(candidate, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED

    foreign_subject = replace(subject, deployment=_root(9_999))
    foreign_finality = verify_zeno_ledger_finality_v1(
        foreign_subject,
        candidate_head=candidate.post_state.state_root,
        publication_root=candidate.publication_atom.publication_root,
        candidate_parent_head=candidate.context.parent_head,
        expected_command_root=finality.expected_command_root,
        expected_nonce_root=finality.expected_nonce_root,
        certificate=finality.certificate,
        tau_certificate=tau,
    )

    result = store.publish(candidate, foreign_finality, tau)

    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason == "candidate or finality replay identity conflicts with durable record"
    assert store.reopen().head_block_id == committed.block_id


def test_durable_publish_rejects_caller_authored_finality_before_install(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    candidate = _candidate(subject, initial, 1, "raw-finality")
    verified_finality, tau = _finality_and_tau(subject, candidate, "raw-finality-batch")

    result = store.publish(candidate, cast(VerifiedZenoLedgerFinalityV1, verified_finality.certificate), tau)

    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason == "finality evidence must be verifier-created"
    assert result.state == initial
    assert tuple((root / "blocks").iterdir()) == ()
    assert store.reopen().head_block_id == "genesis"


def test_durable_replay_rejects_forged_outbox_projection(tmp_path: Path) -> None:
    subject = _subject()
    initial = replace(
        initial_application_state_v1(subject),
        economic_atoms=(EconomicAtomV1(EconomicAtomKindV1.BALANCE, "alice", "A", "ledger", 10),),
    )
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    command = GlobalCommandV1(
        kind=GlobalCommandKindV1.TAU_WITHDRAWAL,
        command_id=_root(1_100),
        sender="alice",
        nonce=1,
        payload={
            "withdrawal_id": "w1",
            "asset": "A",
            "amount_atoms": 2,
            "destination": "tau-alice",
        },
    )
    candidate_result = run_m6_transition_v1(subject, initial, _context(subject, initial, 1), command)
    assert isinstance(candidate_result, AcceptCandidateV1)
    assert candidate_result.outbox_atoms
    finality, tau = _finality_and_tau(subject, candidate_result, "batch-withdrawal")
    committed = store.publish(candidate_result, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED
    assert committed.block_id is not None

    forged = replace(candidate_result, outbox_atoms=())
    result = store.publish(forged, finality, tau)

    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason is not None and "replay identity" in result.reason
    assert store.reopen().head_block_id == committed.block_id


def test_canonical_json_decoder_rejects_oversized_before_decode(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)

    with pytest.raises(M6DurableCorruptionError, match="durable file limit"):
        durable_store._read_canonical_json(
            store.root / "HEAD.json",
            max_bytes=1,
        )


def test_canonical_json_decoder_wraps_excessive_nesting_as_corruption(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """RIPR/BVA: nesting depth cannot escape the durable error algebra."""

    path = tmp_path / "nested.json"
    payload = (b'{"x":' * 993) + b"0" + (b"}" * 993)
    monkeypatch.setattr(durable_store, "_read_nofollow", lambda *_args, **_kwargs: payload)

    with pytest.raises(M6DurableCorruptionError, match="invalid canonical JSON"):
        durable_store._read_canonical_json(path, max_bytes=len(payload) + 1)

    with pytest.raises(ValueError, match="canonical JSON bytes"):
        _decode_replay_body(payload.hex(), name="nested replay body")


def test_durable_reopen_wraps_stale_state_commitment_cache_as_corruption(
    tmp_path: Path,
) -> None:
    """RIPR: structurally valid stale archive caches stay in the durable error algebra."""

    subject = _subject()
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))
    state_path = root / "genesis" / "state.json"
    manifest_path = root / "genesis" / "manifest.json"
    state = json.loads(state_path.read_bytes())
    state["history_root_cache"] = _root(999)
    state_data = canonical_bytes_v1(state)
    state_path.write_bytes(state_data)
    manifest = json.loads(manifest_path.read_bytes())
    manifest["files"]["state.json"] = durable_store._file_digest(state_data)
    manifest_path.write_bytes(canonical_bytes_v1(manifest))

    with pytest.raises(M6DurableCorruptionError, match="durable state commitment invalid"):
        store.reopen()


def test_given_exact_durable_limit_when_reopening_then_one_byte_over_rejects(
    tmp_path: Path,
) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    M6DurableLedgerStoreV1.create(root, subject, initial)
    largest = max(root.rglob("*.json"), key=lambda path: path.stat().st_size)
    exact_limit = largest.stat().st_size
    assert durable_store._read_canonical_json(largest, max_bytes=exact_limit)[0]

    with pytest.raises(M6DurableCorruptionError, match="durable file limit"):
        durable_store._read_canonical_json(largest, max_bytes=exact_limit - 1)


def test_durable_write_rejects_oversized_file_without_replacing_existing_head(
    tmp_path: Path,
) -> None:
    subject = _subject()
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))
    path = root / "HEAD.json"
    before = path.read_bytes()
    with pytest.raises(M6DurableCorruptionError, match="durable file limit"):
        durable_store._atomic_replace_file(path, b"{}", max_bytes=1)

    assert path.read_bytes() == before
    assert store.reopen().head_block_id == "genesis"


def test_subject_bound_chain_profile_rejects_next_commit_without_install(tmp_path: Path) -> None:
    subject = replace(
        _subject(),
        durability_profile=M6DurabilityProfileV1(
            max_json_bytes=256 * 1024 * 1024,
            max_chain_blocks=2,
        ),
    )
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    first = _candidate(subject, initial, 1, "chain-1")
    first_finality, first_tau = _finality_and_tau(subject, first, "chain-batch-1")
    first_result = store.publish(first, first_finality, first_tau)
    assert first_result.status is CommitStatusV1.COMMITTED

    second = _candidate(subject, first_result.state, 2, "chain-2")
    second_finality, second_tau = _finality_and_tau(subject, second, "chain-batch-2")
    second_result = store.publish(second, second_finality, second_tau)
    assert second_result.status is CommitStatusV1.COMMITTED

    reopened = store.reopen()
    assert reopened.chain_block_ids == (
        "genesis",
        first_result.block_id,
        second_result.block_id,
    )

    third = _candidate(subject, second_result.state, 3, "chain-3")
    third_finality, third_tau = _finality_and_tau(subject, third, "chain-batch-3")
    rejected = store.publish(third, third_finality, third_tau)
    assert rejected.status is CommitStatusV1.FINALITY_REJECTED
    assert rejected.reason is not None and "chain limit" in rejected.reason
    assert store.reopen().head_block_id == second_result.block_id
    assert len(tuple((tmp_path / "ledger" / "blocks").iterdir())) == 2


def test_reopen_rejects_subject_bound_durability_profile_mismatch(tmp_path: Path) -> None:
    subject = _subject()
    root = tmp_path / "ledger"
    M6DurableLedgerStoreV1.create(root, subject, initial_application_state_v1(subject))
    mismatched_subject = replace(
        subject,
        durability_profile=M6DurabilityProfileV1(
            max_json_bytes=128 * 1024 * 1024,
            max_chain_blocks=2,
        ),
    )

    with pytest.raises(M6DurableCorruptionError, match="promotion subject mismatch"):
        M6DurableLedgerStoreV1(root, mismatched_subject).reopen()


@pytest.mark.parametrize(
    ("mutation", "error"),
    (
        ("missing_profile", "promotion subject keys mismatch"),
        ("extra_profile_field", "durability profile keys mismatch"),
        ("wrong_profile_schema", "durability profile schema mismatch"),
        ("zero_chain_limit", "must be positive"),
        ("boolean_chain_limit", "non-negative integer"),
    ),
)
def test_subject_codec_rejects_durability_profile_schema_mutants(
    mutation: str,
    error: str,
) -> None:
    raw = json.loads(canonical_bytes_v1(_subject()).decode("utf-8"))
    assert isinstance(raw, dict)
    profile = raw["durability_profile"]
    assert isinstance(profile, dict)
    if mutation == "missing_profile":
        del raw["durability_profile"]
    elif mutation == "extra_profile_field":
        profile["unexpected"] = 1
    elif mutation == "wrong_profile_schema":
        profile["schema"] = "zenodex/m6-durability-profile/v0"
    elif mutation == "zero_chain_limit":
        profile["max_chain_blocks"] = 0
    else:
        profile["max_chain_blocks"] = True

    with pytest.raises(M6DurableCorruptionError, match=error):
        _decode_subject(raw)


def test_reopen_rejects_head_rollback_that_orphans_newer_block(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    first = _candidate(subject, initial, 1, "rollback-1")
    first_finality, first_tau = _finality_and_tau(subject, first, "rollback-batch-1")
    first_result = store.publish(first, first_finality, first_tau)
    assert first_result.status is CommitStatusV1.COMMITTED
    assert first_result.block_id is not None

    second = _candidate(subject, first_result.state, 2, "rollback-2")
    second_finality, second_tau = _finality_and_tau(subject, second, "rollback-batch-2")
    second_result = store.publish(second, second_finality, second_tau)
    assert second_result.status is CommitStatusV1.COMMITTED

    head_path = root / "HEAD.json"
    head_path.write_bytes(
        canonical_bytes_v1(
            durable_store._head_payload(
                subject=subject,
                block_id=first_result.block_id,
                state=first_result.state,
            )
        )
    )

    with pytest.raises(M6DurableCorruptionError, match="unreachable or missing"):
        store.reopen()


def test_head_compare_and_swap_rejects_changed_parent_without_replacement(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    head_path = root / "HEAD.json"
    before = head_path.read_bytes()

    with pytest.raises(M6DurableCorruptionError, match="compare-and-swap"):
        store._write_head_unlocked(
            "genesis",
            initial,
            expected_block_id=_root(999),
            expected_state_root=initial.state_root,
        )

    assert head_path.read_bytes() == before
    assert store.reopen().head_block_id == "genesis"


def test_durable_replay_rejects_forged_history_archive(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    candidate = _candidate(subject, initial, 1, "auction-history")
    finality, tau = _finality_and_tau(subject, candidate, "batch-history")
    committed = store.publish(candidate, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED
    assert committed.block_id is not None

    forged = replace(candidate, post_state=replace(candidate.post_state, history=()))
    result = store.publish(forged, finality, tau)

    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason is not None and "replay identity" in result.reason
    assert store.reopen().head_block_id == committed.block_id


def test_durable_zrpf_replay_reverifies_the_exact_execution_batch(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    contexts, commands = _zrpf_inputs(subject, initial)
    batch = execute_zrpf_batch_v1(subject, initial, contexts, commands)
    verified = verify_zrpf_root_v1(
        subject,
        batch,
        receipt_verifier=_TEST_ZRPF_RECEIPT_VERIFIER,
    )
    finality, tau = _zrpf_finality_and_tau(subject, initial, verified)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)

    committed = store.publish_zrpf(verified, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED
    assert committed.block_id is not None
    assert committed.record is not None
    assert committed.record.zrpf_receipt is not None
    assert committed.record.zrpf_receipt.receipt_root == verified.proof_receipt.receipt_root
    reopened = store.reopen()
    assert reopened.records[0].zrpf_receipt == committed.record.zrpf_receipt

    # Mutation matrix: the durable replay boundary must retain the bindings
    # that survive after the in-memory execution witness is gone.
    mutations = (
        (
            replace(
                verified.journal,
                aggregate_statement_roots=(
                    _root(901),
                    *verified.journal.aggregate_statement_roots[1:],
                ),
            ),
            "publication binding",
        ),
        (replace(verified.journal, writer_epoch=99), "publication binding"),
        (replace(verified.journal, nonce_root=_root(902)), "publication binding"),
        (replace(verified.journal, promotion_subject_root=_root(903)), "subject binding"),
        (replace(verified.journal, verifier_image=_root(904)), "verifier image binding"),
    )
    for mutated_journal, _message in mutations:
        with pytest.raises(ValueError, match="published ZRPF journal"):
            replace(committed.record, zrpf_journal=mutated_journal)

    record_path = (
        tmp_path
        / "ledger"
        / durable_store.BLOCKS_DIR_V1
        / committed.block_id
        / durable_store.RECORD_FILE_V1
    )
    original_record_bytes = record_path.read_bytes()
    raw_record = json.loads(original_record_bytes)
    assert isinstance(raw_record, dict)
    raw_receipt = raw_record["zrpf_receipt"]
    assert isinstance(raw_receipt, dict)
    missing_receipt = dict(raw_record)
    missing_receipt["zrpf_receipt"] = None
    with pytest.raises(M6DurableCorruptionError, match="invalid published record"):
        durable_store._decode_record(missing_receipt)

    receipt_root_tampered = dict(raw_receipt)
    receipt_root_tampered["attestation_root"] = _root(906)
    with pytest.raises(M6DurableCorruptionError, match="receipt record root mismatch"):
        durable_store._decode_zrpf_receipt_record(receipt_root_tampered)

    raw_receipt["attestation_root"] = _root(905)
    record_path.write_bytes(canonical_bytes_v1(raw_record))
    with pytest.raises(M6DurableCorruptionError, match="durable file digest mismatch: record.json"):
        store.reopen()
    record_path.write_bytes(original_record_bytes)

    forged = VerifiedZRPFRootV1(
        _VERIFIED_ZRPF_TOKEN,
        verified.journal,
        verified.candidate_id,
        verified.post_state,
        object(),
        verified.proof_receipt,
    )
    result = store.publish_zrpf(forged, finality, tau)

    assert result.status is CommitStatusV1.FINALITY_REJECTED
    assert result.reason is not None and "checked execution batch" in result.reason
    assert store.reopen().head_block_id == committed.block_id


def test_durable_direct_batch_replay_survives_proof_capacity_degradation(
    tmp_path: Path,
) -> None:
    """BDD/AAA: a direct multi-command fallback has a durable replay shape."""

    subject = _subject()
    initial = initial_application_state_v1(subject)
    contexts: list[AuthenticatedExecutionContextV1] = []
    commands: list[GlobalCommandV1] = []
    current = initial
    for nonce in (1, 2):
        command = _command(nonce, auction_id=f"direct-{nonce}")
        context = _context(subject, current, nonce)
        preview = run_m6_transition_v1(subject, current, context, command)
        assert isinstance(preview, AcceptCandidateV1)
        contexts.append(context)
        commands.append(command)
        current = preview.post_state
    direct = execute_direct_batch_v1(subject, initial, tuple(contexts), tuple(commands))
    command_hashes = tuple(command.command_hash for command in direct.commands)
    nonce_identities = tuple(command.nonce_identity for command in direct.commands)
    tau = TauBatchCertificateV1(
        batch_id="direct-durable-batch",
        tau_profile_root=subject.tau_profile,
        chain_id=subject.chain_id,
        ordered_command_hashes=command_hashes,
        ordered_nonce_identities=nonce_identities,
        candidate_parent_head=direct.pre_head,
        certificate_root=hash_v1(
            "m6-tau-batch-certificate-v1",
            {
                "batch_id": "direct-durable-batch",
                "tau_profile_root": subject.tau_profile,
                "chain_id": subject.chain_id,
                "ordered_command_hashes": command_hashes,
                "ordered_nonce_identities": nonce_identities,
                "candidate_parent_head": direct.pre_head,
            },
        ),
    )
    certificate = ZenoLedgerFinalityCertificateV1(
        finality_id=_root(990),
        candidate_head=direct.post_state_root,
        publication_root=direct.publication_root,
        chain_id=subject.chain_id,
        validator_set_root=subject.validator_set,
        writer_epoch=initial.writer_epoch,
        signer_ids=("v1", "v2", "v3", "v4", "v5"),
        quorum=5,
        mode=FinalityModeV1.TAU_ORDERED,
        signature_root=_root(991),
    )
    finality = verify_zeno_ledger_finality_v1(
        subject,
        candidate_head=direct.post_state_root,
        publication_root=direct.publication_root,
        candidate_parent_head=direct.pre_head,
        expected_writer_epoch=initial.writer_epoch,
        expected_command_root=direct.command_root,
        expected_nonce_root=direct.nonce_root,
        certificate=certificate,
        tau_certificate=tau,
    )
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)

    committed = store.publish_direct_batch(direct, finality, tau)

    assert committed.status is CommitStatusV1.COMMITTED
    assert committed.record is not None
    assert committed.record.direct_batch_replay is not None
    assert len(committed.record.direct_batch_replay) == 2
    reopened = store.reopen()
    assert reopened.records[0] == committed.record
    retry = store.publish_direct_batch(direct, finality, tau)
    assert retry.status is CommitStatusV1.ALREADY_COMMITTED


def test_direct_batch_replay_mutation_cannot_retain_aggregate_da_root(
    tmp_path: Path,
) -> None:
    """RIPR: a changed context and local DA root cannot reuse the batch root."""

    subject = _subject()
    initial = initial_application_state_v1(subject)
    contexts: list[AuthenticatedExecutionContextV1] = []
    commands: list[GlobalCommandV1] = []
    current = initial
    for nonce in (1, 2):
        command = _command(nonce, auction_id=f"da-mutant-{nonce}")
        context = _context(subject, current, nonce)
        preview = run_m6_transition_v1(subject, current, context, command)
        assert isinstance(preview, AcceptCandidateV1)
        contexts.append(context)
        commands.append(command)
        current = preview.post_state
    direct = execute_direct_batch_v1(subject, initial, tuple(contexts), tuple(commands))
    finality, tau = _finality_and_tau_for_direct_batch(subject, initial, direct)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    committed = store.publish_direct_batch(direct, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED
    assert committed.record is not None

    raw_record = json.loads(canonical_bytes_v1(committed.record))
    raw_replay = raw_record["direct_batch_replay"][0]
    context_raw = json.loads(bytes.fromhex(raw_replay["context_body_hex"]).decode("utf-8"))
    context_raw["oracle_context"]["observed_height"] += 1
    context_body_hex = canonical_bytes_v1(context_raw).hex()
    candidate_raw = json.loads(bytes.fromhex(raw_replay["candidate_body_hex"]).decode("utf-8"))
    candidate_raw["publication_atom"]["execution_context_root"] = hash_v1(
        "m6-authenticated-execution-context-v1",
        context_raw,
    )
    candidate_body_hex = canonical_bytes_v1(candidate_raw).hex()
    raw_replay["context_body_hex"] = context_body_hex
    raw_replay["candidate_body_hex"] = candidate_body_hex
    raw_replay["data_availability_root"] = hash_v1(
        "m6-direct-data-availability-v1",
        {
            "command_body_hex": raw_replay["command_body_hex"],
            "context_body_hex": context_body_hex,
            "candidate_body_hex": candidate_body_hex,
        },
    )

    with pytest.raises(M6DurableCorruptionError, match="data-availability"):
        durable_store._decode_record(raw_record)
    assert store.reopen().head_block_id == committed.block_id


def test_durable_direct_record_persists_exact_command_context_and_da_tuple(tmp_path: Path) -> None:
    """BDD/AAA: reopen retains the complete direct replay body and DA binding."""

    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    candidate = _candidate(subject, initial, 1, "direct-replay-body")
    finality, tau = _finality_and_tau(subject, candidate, "direct-replay-body-batch")

    committed = store.publish(candidate, finality, tau)
    assert committed.status is CommitStatusV1.COMMITTED
    assert committed.record is not None
    replay = committed.record.direct_replay
    assert replay is not None
    assert replay.command_body_hex == canonical_bytes_v1(candidate.command).hex()
    assert replay.context_body_hex == canonical_bytes_v1(candidate.context).hex()
    assert replay.candidate_body_hex is None
    assert replay.command_hash == candidate.command.command_hash
    assert replay.context_parent_head == candidate.context.parent_head
    assert replay.data_availability_root

    reopened = store.reopen()
    assert reopened.records[0].direct_replay == replay


def test_durable_direct_replay_rejects_semantically_swapped_context_body(tmp_path: Path) -> None:
    """RIPR: removing typed context decode must fail at the reopen boundary."""

    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    candidate = _candidate(subject, initial, 1, "direct-replay-context-mutant")
    finality, tau = _finality_and_tau(subject, candidate, "direct-replay-context-mutant-batch")
    committed = store.publish(candidate, finality, tau)
    assert committed.record is not None
    replay = committed.record.direct_replay
    assert replay is not None

    context_raw = json.loads(bytes.fromhex(replay.context_body_hex).decode("utf-8"))
    context_raw["oracle_context"] = {"garbage": "accepted"}
    context_body_hex = canonical_bytes_v1(context_raw).hex()
    mutated_replay = {
        "command_body_hex": replay.command_body_hex,
        "context_body_hex": context_body_hex,
        "candidate_body_hex": None,
        "data_availability_root": hash_v1(
            "m6-direct-data-availability-v1",
            {
                "command_body_hex": replay.command_body_hex,
                "context_body_hex": context_body_hex,
                "candidate_body_hex": None,
            },
        ),
    }
    mutated_record = json.loads(canonical_bytes_v1(committed.record).decode("utf-8"))
    mutated_record["direct_replay"] = mutated_replay

    with pytest.raises(M6DurableCorruptionError, match="invalid direct execution replay"):
        durable_store._decode_record(mutated_record)

    bad_da_record = json.loads(canonical_bytes_v1(committed.record).decode("utf-8"))
    bad_da_record["direct_replay"]["data_availability_root"] = _root(999)
    with pytest.raises(M6DurableCorruptionError, match="invalid direct execution replay"):
        durable_store._decode_record(bad_da_record)


def test_cross_block_publication_rejects_valid_but_unbound_context_body(
    tmp_path: Path,
) -> None:
    """RIPR: a self-consistent replay body must remain in the finality surface."""

    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    candidate = _candidate(subject, initial, 1, "direct-replay-context-root-mutant")
    finality, tau = _finality_and_tau(subject, candidate, "direct-replay-context-root-mutant-batch")
    committed = store.publish(candidate, finality, tau)
    assert committed.record is not None
    replay = committed.record.direct_replay
    assert replay is not None

    context_raw = json.loads(bytes.fromhex(replay.context_body_hex).decode("utf-8"))
    context_raw["ledger_height"] = 1
    context_body_hex = canonical_bytes_v1(context_raw).hex()
    mutated_record_raw = json.loads(canonical_bytes_v1(committed.record).decode("utf-8"))
    mutated_record_raw["direct_replay"] = {
        "command_body_hex": replay.command_body_hex,
        "context_body_hex": context_body_hex,
        "candidate_body_hex": None,
        "data_availability_root": hash_v1(
            "m6-direct-data-availability-v1",
            {
                "command_body_hex": replay.command_body_hex,
                "context_body_hex": context_body_hex,
                "candidate_body_hex": None,
            },
        ),
    }
    mutated_record = durable_store._decode_record(mutated_record_raw)

    with pytest.raises(M6DurableCorruptionError, match="context root|publication"):
        _validate_cross_block_publication(
            initial,
            committed.state,
            mutated_record,
            subject=subject,
        )


def test_single_direct_replay_rejects_redundant_candidate_projection(
    tmp_path: Path,
) -> None:
    """RIPR/BVE: the single-command ABI cannot retain a malleable duplicate."""

    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    candidate = _candidate(subject, initial, 1, "direct-replay-no-duplicate")
    finality, tau = _finality_and_tau(subject, candidate, "direct-replay-no-duplicate-batch")
    committed = store.publish(candidate, finality, tau)
    assert committed.record is not None
    replay = committed.record.direct_replay
    assert replay is not None
    candidate_body_hex = canonical_bytes_v1(
        direct_candidate_data_availability_projection_v1(candidate),
    ).hex()
    mutated_record = json.loads(canonical_bytes_v1(committed.record).decode("utf-8"))
    mutated_record["direct_replay"]["candidate_body_hex"] = candidate_body_hex
    mutated_record["direct_replay"]["data_availability_root"] = hash_v1(
        "m6-direct-data-availability-v1",
        {
            "command_body_hex": replay.command_body_hex,
            "context_body_hex": replay.context_body_hex,
            "candidate_body_hex": candidate_body_hex,
        },
    )

    with pytest.raises(M6DurableCorruptionError, match="cannot carry a candidate projection"):
        durable_store._decode_record(mutated_record)


@pytest.mark.parametrize(
    "candidate_body",
    ["", 0, False, {}, [], "ABC", "00"],
    ids=["empty", "integer", "boolean", "object", "list", "uppercase", "bad-hex"],
)
def test_single_direct_replay_rejects_malformed_present_candidate_projection(
    tmp_path: Path,
    candidate_body: object,
) -> None:
    """BVA/RIPR: every non-null malformed duplicate stays in the typed error algebra."""

    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    candidate = _candidate(subject, initial, 1, "direct-replay-malformed-duplicate")
    finality, tau = _finality_and_tau(subject, candidate, "direct-replay-malformed-duplicate-batch")
    committed = store.publish(candidate, finality, tau)
    assert committed.record is not None
    mutated_record = json.loads(canonical_bytes_v1(committed.record).decode("utf-8"))
    mutated_record["direct_replay"]["candidate_body_hex"] = candidate_body

    with pytest.raises(M6DurableCorruptionError):
        durable_store._decode_record(mutated_record)


def test_single_direct_replay_garbage_projection_rejected_after_full_chain_rehash(
    tmp_path: Path,
) -> None:
    """RIPR/BDD: rehashing every unsigned durable link cannot authorize a duplicate."""

    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    candidate = _candidate(subject, initial, 1, "direct-replay-full-chain-mutant")
    finality, tau = _finality_and_tau(subject, candidate, "direct-replay-full-chain-mutant-batch")
    committed = store.publish(candidate, finality, tau)
    assert committed.block_id is not None
    assert committed.record is not None

    block = root / durable_store.BLOCKS_DIR_V1 / committed.block_id
    record_path = block / durable_store.RECORD_FILE_V1
    manifest_path = block / durable_store.MANIFEST_FILE_V1
    raw_record = json.loads(record_path.read_bytes())
    projection = json.loads(
        canonical_bytes_v1(
            direct_candidate_data_availability_projection_v1(candidate),
        )
    )
    projection["outbox_atoms"] = [{"garbage": "accepted"}]
    candidate_body_hex = canonical_bytes_v1(projection).hex()
    raw_record["direct_replay"]["candidate_body_hex"] = candidate_body_hex
    raw_record["direct_replay"]["data_availability_root"] = hash_v1(
        "m6-direct-data-availability-v1",
        {
            "command_body_hex": raw_record["direct_replay"]["command_body_hex"],
            "context_body_hex": raw_record["direct_replay"]["context_body_hex"],
            "candidate_body_hex": candidate_body_hex,
        },
    )
    record_data = canonical_bytes_v1(raw_record)
    record_root = hash_v1("m6-published-record-v1", raw_record)
    manifest = json.loads(manifest_path.read_bytes())
    manifest["record_root"] = record_root
    manifest["files"][durable_store.RECORD_FILE_V1] = durable_store._file_digest(record_data)
    new_block_id = hash_v1(
        "m6-durable-block-v1",
        {
            "subject_root": subject.subject_root,
            "parent_block_id": manifest["parent_block_id"],
            "parent_state_root": manifest["parent_state_root"],
            "parent_head": manifest["parent_head"],
            "candidate_id": raw_record["candidate_id"],
            "post_state_root": raw_record["post_state_root"],
            "receipt_root": record_root,
        },
    )
    manifest["block_id"] = new_block_id
    record_path.write_bytes(record_data)
    manifest_path.write_bytes(canonical_bytes_v1(manifest))
    new_block = block.with_name(new_block_id)
    block.rename(new_block)
    head = durable_store._head_payload(
        subject=subject,
        block_id=new_block_id,
        state=committed.state,
    )
    (root / durable_store.HEAD_FILE_V1).write_bytes(canonical_bytes_v1(head))

    fresh = _fresh_reopen(root, subject, tmp_path / "full-chain-mutant-subject.json")
    assert fresh.returncode == 2
    assert "single-command direct replay cannot carry a candidate projection body" in fresh.stdout


def test_cross_block_publication_binds_nullifier_finality_and_outbox_receipts(
    tmp_path: Path,
) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    candidate = _candidate(subject, initial, 1, "auction-1")
    finality, tau = _finality_and_tau(subject, candidate, "batch-1")
    committed = store.publish(candidate, finality, tau)
    assert committed.record is not None

    _validate_cross_block_publication(initial, committed.state, committed.record)

    with pytest.raises(M6DurableCorruptionError, match="nullifier receipt"):
        _validate_cross_block_publication(
            initial,
            committed.state,
            replace(committed.record, nullifier_root=_root(902)),
        )
    with pytest.raises(ValueError, match="published Tau certificate and command root"):
        replace(committed.record, command_root=_root(903))
    with pytest.raises(M6DurableCorruptionError, match="value-delta receipt"):
        _validate_cross_block_publication(
            initial,
            committed.state,
            replace(committed.record, value_delta_root=_root(904)),
        )
    with pytest.raises(M6DurableCorruptionError, match="business status"):
        _validate_cross_block_publication(
            initial,
            committed.state,
            replace(
                committed.record,
                business_status=BusinessStatusV1.ACCEPTED,
                business_reject_reason=None,
            ),
        )
    with pytest.raises(ValueError, match="published finality and publication root"):
        replace(
            committed.record,
            finality=replace(committed.record.finality, publication_root=_root(905)),
        )
    with pytest.raises(M6DurableCorruptionError, match="finality receipt suffix"):
        _validate_cross_block_publication(
            initial,
            replace(committed.state, finality_certificates=()),
            committed.record,
        )
    with pytest.raises(M6DurableCorruptionError, match="outbox receipt suffix"):
        _validate_cross_block_publication(
            initial,
            committed.state,
            replace(
                committed.record,
                outbox_atoms=(OutboxAtomV1("effect-1", "tau_withdrawal", "tau-alice", "A", 1, _root(777)),),
            ),
        )

    truncated = replace(
        committed.state,
        history=(),
        nullifiers=(),
        history_root_cache=None,
        nullifier_root_cache=None,
        outbox_root_cache=None,
    )
    rewritten_record = replace(
        committed.record,
        history_root=truncated.history_root,
        nullifier_root=truncated.nullifier_root,
    )
    with pytest.raises(M6DurableCorruptionError, match="history"):
        _validate_cross_block_publication(initial, truncated, rewritten_record)


def test_stale_candidate_does_not_advance_durable_head(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    store = M6DurableLedgerStoreV1.create(tmp_path / "ledger", subject, initial)
    first = _candidate(subject, initial, 1, "auction-1")
    second = _candidate(subject, initial, 1, "auction-2")
    first_finality, first_tau = _finality_and_tau(subject, first, "batch-1")
    second_finality, second_tau = _finality_and_tau(subject, second, "batch-2")

    committed = store.publish(first, first_finality, first_tau)
    stale = store.publish(second, second_finality, second_tau)
    assert committed.status is CommitStatusV1.COMMITTED
    assert stale.status is CommitStatusV1.STALE_HEAD
    assert store.reopen().head_block_id == committed.block_id


def test_orphan_block_after_install_before_head_update_fails_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    candidate = _candidate(subject, initial, 1, "auction-1")
    finality, tau = _finality_and_tau(subject, candidate, "batch-1")

    def fail_head(_block_id: str, _state: M6ApplicationStateV1, **_kwargs: object) -> None:
        raise RuntimeError("simulated crash before HEAD replacement")

    monkeypatch.setattr(store, "_write_head_unlocked", fail_head)
    with pytest.raises(RuntimeError, match="simulated crash"):
        store.publish(candidate, finality, tau)
    fresh = _fresh_reopen(root, subject, tmp_path / "orphan-subject.json")
    assert fresh.returncode == 2
    assert "unreachable or missing" in fresh.stdout


def test_temp_directory_fsync_failure_installs_no_commit_block(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    candidate = _candidate(subject, initial, 1, "fsync-temp")
    finality, tau = _finality_and_tau(subject, candidate, "fsync-temp-batch")
    original_fsync = durable_store._fsync_directory

    def fail_temp_directory(path: Path) -> None:
        if path.name.startswith(".m6-block-"):
            raise M6DurableCorruptionError("simulated temporary-directory fsync failure")
        original_fsync(path)

    monkeypatch.setattr(durable_store, "_fsync_directory", fail_temp_directory)
    with pytest.raises(M6DurableCorruptionError, match="temporary-directory fsync"):
        store.publish(candidate, finality, tau)

    assert tuple((root / "blocks").iterdir()) == ()
    reopened = M6DurableLedgerStoreV1(root, subject).reopen()
    assert reopened.head_block_id == "genesis"


def test_commit_parent_fsync_failure_leaves_orphan_rejected_on_reopen(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    candidate = _candidate(subject, initial, 1, "fsync-parent")
    finality, tau = _finality_and_tau(subject, candidate, "fsync-parent-batch")
    original_fsync = durable_store._fsync_directory

    def fail_commit_parent(path: Path) -> None:
        if path.name == durable_store.BLOCKS_DIR_V1:
            raise M6DurableCorruptionError("simulated commit-parent fsync failure")
        original_fsync(path)

    monkeypatch.setattr(durable_store, "_fsync_directory", fail_commit_parent)
    with pytest.raises(M6DurableCorruptionError, match="commit-parent fsync"):
        store.publish(candidate, finality, tau)

    installed = tuple((root / "blocks").iterdir())
    assert len(installed) == 1
    with pytest.raises(M6DurableCorruptionError, match="unreachable or missing"):
        M6DurableLedgerStoreV1(root, subject).reopen()


def test_head_parent_fsync_failure_reopens_and_retry_is_idempotent(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    candidate = _candidate(subject, initial, 1, "fsync-head-parent")
    finality, tau = _finality_and_tau(subject, candidate, "fsync-head-parent-batch")
    original_fsync = durable_store._fsync_directory

    def fail_head_parent(path: Path) -> None:
        if path.as_posix().startswith("/proc/self/fd/") and path.name.isdigit():
            raise M6DurableCorruptionError("simulated HEAD-parent fsync failure")
        original_fsync(path)

    monkeypatch.setattr(durable_store, "_fsync_directory", fail_head_parent)
    with pytest.raises(M6DurableCorruptionError, match="HEAD-parent fsync"):
        store.publish(candidate, finality, tau)

    monkeypatch.setattr(durable_store, "_fsync_directory", original_fsync)
    fresh = _fresh_reopen(root, subject, tmp_path / "head-fsync-subject.json")
    assert fresh.returncode == 0, fresh.stderr
    fresh_state = json.loads(fresh.stdout)
    assert fresh_state["state_root"] == candidate.post_state.state_root
    installed_block_id = next(path.name for path in (root / "blocks").iterdir())
    assert fresh_state["head_block_id"] == installed_block_id

    retry = store.publish(candidate, finality, tau)
    assert retry.status is CommitStatusV1.ALREADY_COMMITTED
    assert retry.block_id == installed_block_id


def test_tampered_state_file_is_rejected_by_manifest_digest(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    candidate = _candidate(subject, initial, 1, "auction-1")
    finality, tau = _finality_and_tau(subject, candidate, "batch-1")
    committed = store.publish(candidate, finality, tau)
    assert committed.block_id is not None

    state_path = root / "blocks" / committed.block_id / "state.json"
    state = json.loads(state_path.read_text(encoding="utf-8"))
    state["head"] = _root(999)
    state_path.write_text(json.dumps(state, sort_keys=True, separators=(",", ":")), encoding="utf-8")
    with pytest.raises(M6DurableCorruptionError, match="digest"):
        M6DurableLedgerStoreV1(root, subject).reopen()


def test_reopen_rejects_path_traversal_in_head_block_id(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    head_path = root / "HEAD.json"
    head = json.loads(head_path.read_text(encoding="utf-8"))
    head["block_id"] = "../genesis"
    head_path.write_bytes(canonical_bytes_v1(head))

    with pytest.raises(M6DurableCorruptionError, match="HEAD block id"):
        store.reopen()


def test_reopen_rejects_unexpected_genesis_entries(tmp_path: Path) -> None:
    subject = _subject()
    initial = initial_application_state_v1(subject)
    root = tmp_path / "ledger"
    store = M6DurableLedgerStoreV1.create(root, subject, initial)
    (root / "genesis" / "unexpected.bin").write_bytes(b"unexpected")

    with pytest.raises(M6DurableCorruptionError, match="genesis block entries mismatch"):
        store.reopen()
