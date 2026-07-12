from __future__ import annotations

import os
import sqlite3
import stat
import threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pytest

import src.integration._recursive_stark_admission_store_history as admission_history
import src.integration.recursive_stark_admission_store as admission_store
from src.core.recursive_stark_admission import (
    RecursiveStarkAdmissionRejectReason,
    RecursiveStarkAdmissionState,
    RecursiveStarkRootFacts,
    TrustedRecursiveStarkAdmissionPolicy,
    _admit_authenticated_recursive_stark_root,
    _AuthenticatedRecursiveStarkRootFacts,
    _mint_recursive_stark_root_facts_after_verification,
    _RecursiveStarkVerificationProvenance,
    recursive_child_verification_claims_root_v1,
    recursive_message_ids_root_v1,
    recursive_receipt_ids_root_v1,
)
from src.integration.recursive_stark_admission_store import (
    STORE_APPLICATION_ID,
    STORE_SCHEMA_VERSION,
    DurableRecursiveStarkAdmissionCursor,
    DurableRecursiveStarkAdmissionDisposition,
    DurableRecursiveStarkAdmissionResult,
    RecursiveStarkAdmissionStoreError,
    SQLiteRecursiveStarkAdmissionStore,
)


def _hash(index: int) -> str:
    assert index > 0
    return f"0x{index:064x}"


def _facts(
    *,
    root: int = 1,
    epoch: int = 7,
    child_ids: tuple[str, ...] | None = None,
    receipt_ids: tuple[str, ...] | None = None,
    message_ids: tuple[str, ...] | None = None,
) -> RecursiveStarkRootFacts:
    base = root * 1_000
    children = child_ids if child_ids is not None else (_hash(base + 100), _hash(base + 101))
    receipts = receipt_ids if receipt_ids is not None else (_hash(base + 200), _hash(base + 201))
    messages = message_ids if message_ids is not None else (_hash(base + 300), _hash(base + 301))
    return RecursiveStarkRootFacts(
        chain_id="zenodex-devnet",
        epoch_id=epoch,
        proof_profile="recursive_epoch_v1",
        root_journal_hash=_hash(root),
        verifier_set_root=_hash(10_001),
        public_policy_hash=_hash(10_002),
        child_verification_claim_hashes=children,
        child_verification_claims_root=recursive_child_verification_claims_root_v1(children),
        accepted_receipt_ids=receipts,
        accepted_receipts_root=recursive_receipt_ids_root_v1(receipts),
        cross_shard_message_ids=messages,
        cross_shard_message_ids_root=recursive_message_ids_root_v1(messages),
    )


def _authenticated(
    facts: RecursiveStarkRootFacts,
    *,
    request_byte: str = "33",
    authority_byte: str = "11",
    executable_byte: str = "22",
    release_byte: str = "44",
    replay_byte: str = "55",
    release_bound: bool = True,
) -> _AuthenticatedRecursiveStarkRootFacts:
    policy = TrustedRecursiveStarkAdmissionPolicy(
        expected_chain_id=facts.chain_id,
        expected_epoch_id=facts.epoch_id,
        expected_proof_profile=facts.proof_profile,
        expected_verifier_set_root=facts.verifier_set_root,
        expected_public_policy_hash=facts.public_policy_hash,
    )
    provenance = _RecursiveStarkVerificationProvenance(
        authority_manifest_sha256=authority_byte * 32,
        verifier_executable_sha256=executable_byte * 32,
        verification_request_sha256=request_byte * 32,
        release_binding_config_digest="0x" + release_byte * 32 if release_bound else None,
        replay_manifest_sha256="sha256:" + replay_byte * 32 if release_bound else None,
    )
    return _mint_recursive_stark_root_facts_after_verification(
        facts,
        policy,
        provenance,
    )


def _store(
    tmp_path: Path, name: str = "zrpf-admission.sqlite3"
) -> SQLiteRecursiveStarkAdmissionStore:
    return SQLiteRecursiveStarkAdmissionStore(tmp_path / name)


def test_store_initializes_private_delete_extra_schema_and_genesis(tmp_path: Path) -> None:
    store = _store(tmp_path)

    cursor = store.read_cursor()
    assert cursor.revision == 0
    assert cursor.chain_id is None
    assert cursor.root_count == 0
    assert cursor.state_root != "0x" + "00" * 32
    assert stat.S_IMODE(store.path.stat().st_mode) == 0o600
    with sqlite3.connect(store.path) as connection:
        assert connection.execute("PRAGMA application_id").fetchone()[0] == STORE_APPLICATION_ID
        assert connection.execute("PRAGMA user_version").fetchone()[0] == STORE_SCHEMA_VERSION
        assert connection.execute("PRAGMA journal_mode").fetchone()[0] == "delete"
    with store._connect() as connection:
        assert connection.execute("PRAGMA synchronous").fetchone()[0] == 3
        assert connection.execute("PRAGMA busy_timeout").fetchone()[0] == 5_000


def test_restart_recovers_private_empty_file_left_before_schema_commit(tmp_path: Path) -> None:
    path = tmp_path / "interrupted-initialization.sqlite3"
    path.touch(mode=0o600)
    path.chmod(0o600)

    store = SQLiteRecursiveStarkAdmissionStore(path)

    assert store.read_cursor().revision == 0
    assert store.read_cursor().state_root != "0x" + "00" * 32


def test_concurrent_store_initializers_converge_on_one_genesis(tmp_path: Path) -> None:
    path = tmp_path / "initializer-race.sqlite3"
    with ThreadPoolExecutor(max_workers=2) as pool:
        stores = list(pool.map(SQLiteRecursiveStarkAdmissionStore, (path, path)))

    assert stores[0].read_cursor() == stores[1].read_cursor()
    assert stores[0].read_cursor().revision == 0


def test_restart_history_validation_holds_one_snapshot_against_writer(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    path = tmp_path / "history-writer-race.sqlite3"
    store = SQLiteRecursiveStarkAdmissionStore(path)
    first = store._commit_authenticated_recursive_stark_root(
        expected_cursor=store.read_cursor(),
        authenticated_root=_authenticated(_facts(root=1, epoch=7)),
    )
    writer_store = SQLiteRecursiveStarkAdmissionStore(path)
    entered_validation = threading.Event()
    release_validation = threading.Event()
    writer_started = threading.Event()
    original_facts_from_row = admission_history._facts_from_row

    def blocking_facts_from_row(
        row: sqlite3.Row,
        children: tuple[str, ...],
        receipts: tuple[str, ...],
        messages: tuple[str, ...],
    ) -> RecursiveStarkRootFacts:
        entered_validation.set()
        if not release_validation.wait(timeout=5):
            raise TimeoutError("test did not release restart history validation")
        return original_facts_from_row(row, children, receipts, messages)

    def commit_second_root() -> DurableRecursiveStarkAdmissionResult:
        writer_started.set()
        return writer_store._commit_authenticated_recursive_stark_root(
            expected_cursor=first.head_cursor,
            authenticated_root=_authenticated(
                _facts(root=2, epoch=8),
                request_byte="66",
            ),
        )

    monkeypatch.setattr(admission_history, "_facts_from_row", blocking_facts_from_row)
    with ThreadPoolExecutor(max_workers=2) as pool:
        restart_future = pool.submit(SQLiteRecursiveStarkAdmissionStore, path)
        assert entered_validation.wait(timeout=5)
        writer_future = pool.submit(commit_second_root)
        assert writer_started.wait(timeout=5)
        assert writer_future.done() is False
        release_validation.set()
        restarted = restart_future.result(timeout=5)
        committed = writer_future.result(timeout=5)

    assert committed.committed is True
    assert restarted.read_cursor().revision == 2


def test_cursor_rejects_revision_count_split_view() -> None:
    with pytest.raises(ValueError, match="revision and root count must match"):
        DurableRecursiveStarkAdmissionCursor(
            revision=1,
            state_root=_hash(99),
            chain_id="zenodex-devnet",
            root_count=0,
            slot_count=0,
            child_claim_count=0,
            receipt_count=0,
            message_count=0,
        )


def test_first_commit_survives_restart_and_exact_retry_returns_same_outcome(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    initial = store.read_cursor()
    authenticated = _authenticated(_facts(epoch=(1 << 64) - 1))

    committed = store._commit_authenticated_recursive_stark_root(
        expected_cursor=initial,
        authenticated_root=authenticated,
    )
    restarted = SQLiteRecursiveStarkAdmissionStore(store.path)
    replay = restarted._commit_authenticated_recursive_stark_root(
        expected_cursor=initial,
        authenticated_root=authenticated,
    )

    assert committed.disposition is DurableRecursiveStarkAdmissionDisposition.COMMITTED
    assert committed.receipt is not None
    assert committed.receipt.slot.epoch_id == (1 << 64) - 1
    assert committed.receipt.outcome_key == (
        "0xc70aefcb7b5fbacb36e04daca5ab63a76cfdd82c12c6d71bb29dd6a90cc251a4"
    )
    assert committed.head_cursor.state_root == (
        "0xaa1f685f614e5bf801e6fcf63030bfb0cb4e2d2269db114309aa948baab26eb1"
    )
    assert restarted.read_cursor() == committed.head_cursor
    assert replay.disposition is DurableRecursiveStarkAdmissionDisposition.IDEMPOTENT_REPLAY
    assert replay.receipt == committed.receipt
    assert restarted.get_committed_receipt(_hash(1)) == committed.receipt


def test_stale_cursor_rejects_disjoint_root_without_mutation_then_retry_commits(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    initial = store.read_cursor()
    first = store._commit_authenticated_recursive_stark_root(
        expected_cursor=initial,
        authenticated_root=_authenticated(_facts(root=1, epoch=7)),
    )

    stale = store._commit_authenticated_recursive_stark_root(
        expected_cursor=initial,
        authenticated_root=_authenticated(_facts(root=2, epoch=8), request_byte="66"),
    )
    assert stale.accepted is False
    assert stale.reject_reason is RecursiveStarkAdmissionRejectReason.DURABLE_CURSOR_MISMATCH
    assert stale.head_cursor == first.head_cursor
    assert store.get_committed_receipt(_hash(2)) is None

    retried = store._commit_authenticated_recursive_stark_root(
        expected_cursor=first.head_cursor,
        authenticated_root=_authenticated(_facts(root=2, epoch=8), request_byte="66"),
    )
    assert retried.committed is True
    assert retried.head_cursor.revision == 2


@pytest.mark.parametrize(
    ("candidate", "expected"),
    (
        (
            _authenticated(_facts(root=1, epoch=7), request_byte="77"),
            RecursiveStarkAdmissionRejectReason.DUPLICATE_ROOT_JOURNAL,
        ),
        (
            _authenticated(_facts(root=2, epoch=7), request_byte="77"),
            RecursiveStarkAdmissionRejectReason.DUPLICATE_ADMISSION_SLOT,
        ),
        (
            _authenticated(
                _facts(root=3, epoch=9, child_ids=(_hash(1_100), _hash(9_999))),
                request_byte="77",
            ),
            RecursiveStarkAdmissionRejectReason.DUPLICATE_CHILD_VERIFICATION_CLAIM,
        ),
        (
            _authenticated(
                _facts(root=4, epoch=10, receipt_ids=(_hash(1_200), _hash(9_999))),
                request_byte="77",
            ),
            RecursiveStarkAdmissionRejectReason.DUPLICATE_ACCEPTED_RECEIPT,
        ),
        (
            _authenticated(
                _facts(root=5, epoch=11, message_ids=(_hash(1_300), _hash(9_999))),
                request_byte="77",
            ),
            RecursiveStarkAdmissionRejectReason.DUPLICATE_CROSS_SHARD_MESSAGE,
        ),
    ),
)
def test_replay_conflicts_preserve_core_precedence_and_are_database_noops(
    tmp_path: Path,
    candidate: _AuthenticatedRecursiveStarkRootFacts,
    expected: RecursiveStarkAdmissionRejectReason,
) -> None:
    store = _store(tmp_path)
    committed = store._commit_authenticated_recursive_stark_root(
        expected_cursor=store.read_cursor(),
        authenticated_root=_authenticated(_facts(root=1, epoch=7)),
    )

    result = store._commit_authenticated_recursive_stark_root(
        expected_cursor=committed.head_cursor,
        authenticated_root=candidate,
    )

    assert result.accepted is False
    assert result.reject_reason is expected
    assert result.head_cursor == committed.head_cursor
    assert store.read_cursor() == committed.head_cursor


def test_release_unbound_authenticated_value_cannot_enter_durable_store(tmp_path: Path) -> None:
    store = _store(tmp_path)

    with pytest.raises(TypeError, match="requires release-bound verification provenance"):
        store._commit_authenticated_recursive_stark_root(
            expected_cursor=store.read_cursor(),
            authenticated_root=_authenticated(_facts(), release_bound=False),
        )

    assert store.read_cursor().revision == 0


def test_sqlite_snapshot_decisions_match_in_memory_reference_sequence(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    cursor = store.read_cursor()
    memory_state = RecursiveStarkAdmissionState()
    candidates = (
        _authenticated(_facts(root=1, epoch=7), request_byte="61"),
        _authenticated(_facts(root=2, epoch=7), request_byte="62"),
        _authenticated(
            _facts(root=3, epoch=8, child_ids=(_hash(1_100), _hash(3_999))),
            request_byte="63",
        ),
        _authenticated(
            _facts(root=4, epoch=9, receipt_ids=(_hash(1_200), _hash(4_999))),
            request_byte="64",
        ),
        _authenticated(
            _facts(root=5, epoch=10, message_ids=(_hash(1_300), _hash(5_999))),
            request_byte="65",
        ),
        _authenticated(_facts(root=6, epoch=8), request_byte="66"),
        _authenticated(
            _facts(root=7, epoch=11, child_ids=(_hash(6_100), _hash(7_999))),
            request_byte="67",
        ),
        _authenticated(_facts(root=8, epoch=9), request_byte="68"),
    )

    for candidate in candidates:
        memory_result = _admit_authenticated_recursive_stark_root(memory_state, candidate)
        durable_result = store._commit_authenticated_recursive_stark_root(
            expected_cursor=cursor,
            authenticated_root=candidate,
        )

        assert durable_result.accepted is memory_result.accepted
        assert durable_result.reject_reason is memory_result.reject_reason
        memory_state = memory_result.state
        cursor = durable_result.head_cursor

    assert cursor.revision == 3
    assert len(memory_state.accepted_root_journal_hashes) == 3


def test_two_connections_racing_same_root_commit_once_and_recover_one_outcome(
    tmp_path: Path,
) -> None:
    path = tmp_path / "race.sqlite3"
    first_store = SQLiteRecursiveStarkAdmissionStore(path)
    second_store = SQLiteRecursiveStarkAdmissionStore(path)
    initial = first_store.read_cursor()
    authenticated = _authenticated(_facts())

    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [
            pool.submit(
                store._commit_authenticated_recursive_stark_root,
                expected_cursor=initial,
                authenticated_root=authenticated,
            )
            for store in (first_store, second_store)
        ]
    results = [future.result() for future in futures]

    assert sorted(result.disposition.value for result in results) == [
        "committed",
        "idempotent_replay",
    ]
    assert results[0].receipt == results[1].receipt
    assert first_store.read_cursor().revision == 1


def test_two_connections_racing_same_slot_commit_one_and_reject_one(tmp_path: Path) -> None:
    path = tmp_path / "slot-race.sqlite3"
    stores = (SQLiteRecursiveStarkAdmissionStore(path), SQLiteRecursiveStarkAdmissionStore(path))
    initial = stores[0].read_cursor()
    candidates = (
        _authenticated(_facts(root=1, epoch=7), request_byte="66"),
        _authenticated(_facts(root=2, epoch=7), request_byte="77"),
    )

    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [
            pool.submit(
                store._commit_authenticated_recursive_stark_root,
                expected_cursor=initial,
                authenticated_root=candidate,
            )
            for store, candidate in zip(stores, candidates, strict=True)
        ]
    results = [future.result() for future in futures]

    assert sum(result.committed for result in results) == 1
    rejected = next(result for result in results if not result.accepted)
    assert rejected.reject_reason is RecursiveStarkAdmissionRejectReason.DUPLICATE_ADMISSION_SLOT
    assert stores[0].read_cursor().revision == 1


def test_disjoint_writers_from_one_cursor_preserve_winner_then_loser_retries(
    tmp_path: Path,
) -> None:
    path = tmp_path / "disjoint-race.sqlite3"
    stores = (SQLiteRecursiveStarkAdmissionStore(path), SQLiteRecursiveStarkAdmissionStore(path))
    initial = stores[0].read_cursor()
    candidates = (
        _authenticated(_facts(root=1, epoch=7), request_byte="66"),
        _authenticated(_facts(root=2, epoch=8), request_byte="77"),
    )

    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [
            pool.submit(
                store._commit_authenticated_recursive_stark_root,
                expected_cursor=initial,
                authenticated_root=candidate,
            )
            for store, candidate in zip(stores, candidates, strict=True)
        ]
    results = [future.result() for future in futures]

    assert sum(result.committed for result in results) == 1
    stale_index = next(index for index, result in enumerate(results) if not result.accepted)
    assert (
        results[stale_index].reject_reason
        is RecursiveStarkAdmissionRejectReason.DURABLE_CURSOR_MISMATCH
    )
    retry = stores[stale_index]._commit_authenticated_recursive_stark_root(
        expected_cursor=stores[stale_index].read_cursor(),
        authenticated_root=candidates[stale_index],
    )
    assert retry.committed is True
    assert retry.head_cursor.revision == 2


@pytest.mark.skipif(not hasattr(os, "fork"), reason="requires POSIX writer processes")
def test_two_processes_racing_same_root_commit_once_and_recover_one_outcome(
    tmp_path: Path,
) -> None:
    path = tmp_path / "process-race.sqlite3"
    store = SQLiteRecursiveStarkAdmissionStore(path)
    initial = store.read_cursor()
    authenticated = _authenticated(_facts())
    start_read, start_write = os.pipe()
    result_pipes = (os.pipe(), os.pipe())
    process_ids: list[int] = []

    for own_index in range(2):
        process_id = os.fork()
        if process_id == 0:
            os.close(start_write)
            for index, (read_fd, write_fd) in enumerate(result_pipes):
                os.close(read_fd)
                if index != own_index:
                    os.close(write_fd)
            os.read(start_read, 1)
            child_store = SQLiteRecursiveStarkAdmissionStore(path)
            result = child_store._commit_authenticated_recursive_stark_root(
                expected_cursor=initial,
                authenticated_root=authenticated,
            )
            os.write(result_pipes[own_index][1], result.disposition.value.encode("ascii"))
            os._exit(0)
        process_ids.append(process_id)

    os.close(start_read)
    for _, write_fd in result_pipes:
        os.close(write_fd)
    os.write(start_write, b"12")
    os.close(start_write)
    dispositions = sorted(
        os.read(read_fd, 64).decode("ascii") for read_fd, _ in result_pipes
    )
    for read_fd, _ in result_pipes:
        os.close(read_fd)
    statuses = [os.waitpid(process_id, 0)[1] for process_id in process_ids]

    assert dispositions == ["committed", "idempotent_replay"]
    assert [os.waitstatus_to_exitcode(status) for status in statuses] == [0, 0]
    assert SQLiteRecursiveStarkAdmissionStore(path).read_cursor().revision == 1


@pytest.mark.skipif(not hasattr(os, "fork"), reason="requires POSIX process crash semantics")
def test_process_crash_after_rows_before_meta_cas_rolls_back_everything(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store = _store(tmp_path)
    initial = store.read_cursor()
    authenticated = _authenticated(_facts())
    original = admission_store._cas_meta

    def crash_before_cas(*args: object, **kwargs: object) -> None:
        del args, kwargs
        os._exit(91)

    monkeypatch.setattr(admission_store, "_cas_meta", crash_before_cas)
    process_id = os.fork()
    if process_id == 0:
        store._commit_authenticated_recursive_stark_root(
            expected_cursor=initial,
            authenticated_root=authenticated,
        )
        os._exit(90)
    _, status = os.waitpid(process_id, 0)
    monkeypatch.setattr(admission_store, "_cas_meta", original)

    assert os.waitstatus_to_exitcode(status) == 91
    restarted = SQLiteRecursiveStarkAdmissionStore(store.path)
    assert restarted.read_cursor() == initial
    assert restarted.get_committed_receipt(_hash(1)) is None


@pytest.mark.skipif(not hasattr(os, "fork"), reason="requires POSIX process crash semantics")
def test_process_crash_after_meta_cas_before_commit_rolls_back_everything(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store = _store(tmp_path)
    initial = store.read_cursor()
    authenticated = _authenticated(_facts())
    original = admission_store._cas_meta

    def crash_after_cas(
        connection: sqlite3.Connection,
        previous: DurableRecursiveStarkAdmissionCursor,
        result: DurableRecursiveStarkAdmissionCursor,
    ) -> None:
        original(connection, previous, result)
        os._exit(93)

    monkeypatch.setattr(admission_store, "_cas_meta", crash_after_cas)
    process_id = os.fork()
    if process_id == 0:
        store._commit_authenticated_recursive_stark_root(
            expected_cursor=initial,
            authenticated_root=authenticated,
        )
        os._exit(90)
    _, status = os.waitpid(process_id, 0)
    monkeypatch.setattr(admission_store, "_cas_meta", original)

    assert os.waitstatus_to_exitcode(status) == 93
    restarted = SQLiteRecursiveStarkAdmissionStore(store.path)
    assert restarted.read_cursor() == initial
    assert restarted.get_committed_receipt(_hash(1)) is None


@pytest.mark.skipif(not hasattr(os, "fork"), reason="requires POSIX lost-response semantics")
def test_process_crash_after_commit_before_response_is_reconciled_by_retry(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    initial = store.read_cursor()
    authenticated = _authenticated(_facts())

    process_id = os.fork()
    if process_id == 0:
        result = store._commit_authenticated_recursive_stark_root(
            expected_cursor=initial,
            authenticated_root=authenticated,
        )
        assert result.committed
        os._exit(92)
    _, status = os.waitpid(process_id, 0)

    assert os.waitstatus_to_exitcode(status) == 92
    restarted = SQLiteRecursiveStarkAdmissionStore(store.path)
    replay = restarted._commit_authenticated_recursive_stark_root(
        expected_cursor=initial,
        authenticated_root=authenticated,
    )
    assert replay.idempotent_replay is True
    assert replay.receipt == restarted.get_committed_receipt(_hash(1))
    assert restarted.read_cursor().revision == 1


def test_unknown_schema_object_and_application_id_drift_fail_closed(tmp_path: Path) -> None:
    store = _store(tmp_path)
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            "CREATE TRIGGER attacker AFTER INSERT ON zrpf_child_claims BEGIN SELECT 1; END"
        )
    with pytest.raises(RecursiveStarkAdmissionStoreError, match="schema object set mismatch"):
        store.read_cursor()

    second = _store(tmp_path, "app-id.sqlite3")
    with sqlite3.connect(second.path) as connection:
        connection.execute("PRAGMA application_id = 1")
    with pytest.raises(RecursiveStarkAdmissionStoreError, match="application_id mismatch"):
        second.read_cursor()


def test_restart_rejects_metadata_count_drift(tmp_path: Path) -> None:
    store = _store(tmp_path)
    store._commit_authenticated_recursive_stark_root(
        expected_cursor=store.read_cursor(),
        authenticated_root=_authenticated(_facts()),
    )
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            "UPDATE zrpf_store_meta SET child_claim_count = child_claim_count + 1 "
            "WHERE singleton = 1"
        )

    with pytest.raises(
        RecursiveStarkAdmissionStoreError,
        match="metadata counts disagree with indexes",
    ):
        SQLiteRecursiveStarkAdmissionStore(store.path)


def test_restart_recomputes_identifier_roots_and_rejects_same_count_bit_flip(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    store._commit_authenticated_recursive_stark_root(
        expected_cursor=store.read_cursor(),
        authenticated_root=_authenticated(_facts()),
    )
    original_identifier = bytes.fromhex(_hash(1_100)[2:])
    substituted_identifier = bytes.fromhex(_hash(9_999)[2:])
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            "UPDATE zrpf_child_claims SET identifier = ? WHERE identifier = ?",
            (substituted_identifier, original_identifier),
        )

    with pytest.raises(
        RecursiveStarkAdmissionStoreError,
        match="child_verification_claims_root mismatch",
    ):
        SQLiteRecursiveStarkAdmissionStore(store.path)


@pytest.mark.parametrize(
    ("statement", "match"),
    (
        (
            "UPDATE zrpf_admissions SET facts_digest = zeroblob(32)",
            "stored facts digest mismatch",
        ),
        (
            "UPDATE zrpf_admissions SET outcome_key = zeroblob(32)",
            "stored durable admission outcome key is inconsistent",
        ),
        (
            "UPDATE zrpf_admissions SET previous_state_root = zeroblob(32)",
            "stored hash must be 32 nonzero bytes",
        ),
        (
            "UPDATE zrpf_child_claims SET ordinal = ordinal + 2",
            "ordinals must be dense",
        ),
    ),
)
def test_restart_rejects_history_layer_mutation(
    tmp_path: Path,
    statement: str,
    match: str,
) -> None:
    store = _store(tmp_path)
    store._commit_authenticated_recursive_stark_root(
        expected_cursor=store.read_cursor(),
        authenticated_root=_authenticated(_facts()),
    )
    with sqlite3.connect(store.path) as connection:
        connection.execute(statement)

    with pytest.raises(RecursiveStarkAdmissionStoreError, match=match):
        SQLiteRecursiveStarkAdmissionStore(store.path)


def test_store_rejects_symlink_and_nonprivate_parent(tmp_path: Path) -> None:
    target = tmp_path / "target.sqlite3"
    target.write_bytes(b"")
    target.chmod(0o600)
    link = tmp_path / "link.sqlite3"
    link.symlink_to(target)
    with pytest.raises(ValueError, match="canonical and symlink-free"):
        SQLiteRecursiveStarkAdmissionStore(link)

    public_parent = tmp_path / "public"
    public_parent.mkdir(mode=0o755)
    public_parent.chmod(0o755)
    with pytest.raises(ValueError, match="group or world access"):
        SQLiteRecursiveStarkAdmissionStore(public_parent / "store.sqlite3")


def test_directory_sync_failure_is_typed_and_never_silently_skipped(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fail_sync(_path: Path) -> None:
        raise OSError("injected directory sync failure")

    monkeypatch.setattr(admission_store, "_fsync_directory", fail_sync)
    with pytest.raises(
        RecursiveStarkAdmissionStoreError,
        match="STORE_DIRECTORY_SYNC_FAILED",
    ):
        _store(tmp_path)


def test_directory_sync_failure_must_succeed_on_restart_before_store_opens(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    sync_attempts = 0

    def fail_first_sync(_path: Path) -> None:
        nonlocal sync_attempts
        sync_attempts += 1
        if sync_attempts == 1:
            raise OSError("injected first directory sync failure")

    monkeypatch.setattr(admission_store, "_fsync_directory", fail_first_sync)
    with pytest.raises(
        RecursiveStarkAdmissionStoreError,
        match="STORE_DIRECTORY_SYNC_FAILED",
    ):
        _store(tmp_path)

    restarted = _store(tmp_path)

    assert restarted.read_cursor().revision == 0
    assert sync_attempts == 2


def test_injected_commit_failure_rolls_back_all_rows(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store = _store(tmp_path)
    initial = store.read_cursor()

    def fail_cas(*_args: object, **_kwargs: object) -> None:
        raise sqlite3.OperationalError("injected storage failure")

    monkeypatch.setattr(admission_store, "_cas_meta", fail_cas)
    with pytest.raises(RecursiveStarkAdmissionStoreError, match="STORE_COMMIT_FAILED"):
        store._commit_authenticated_recursive_stark_root(
            expected_cursor=initial,
            authenticated_root=_authenticated(_facts()),
        )

    assert SQLiteRecursiveStarkAdmissionStore(store.path).read_cursor() == initial
    assert store.get_committed_receipt(_hash(1)) is None


def test_outcome_key_changes_with_verification_request_provenance(tmp_path: Path) -> None:
    store = _store(tmp_path)
    initial = store.read_cursor()
    committed = store._commit_authenticated_recursive_stark_root(
        expected_cursor=initial,
        authenticated_root=_authenticated(_facts(), request_byte="66"),
    )

    different_request = store._commit_authenticated_recursive_stark_root(
        expected_cursor=committed.head_cursor,
        authenticated_root=_authenticated(_facts(), request_byte="77"),
    )

    assert different_request.accepted is False
    assert (
        different_request.reject_reason
        is RecursiveStarkAdmissionRejectReason.DUPLICATE_ROOT_JOURNAL
    )
    assert committed.receipt is not None
    assert committed.receipt.verification_request_sha256 == "66" * 32
    assert store.get_committed_receipt(_hash(1)) == committed.receipt


def test_same_root_under_different_governed_authority_is_duplicate_not_idempotent(
    tmp_path: Path,
) -> None:
    store = _store(tmp_path)
    committed = store._commit_authenticated_recursive_stark_root(
        expected_cursor=store.read_cursor(),
        authenticated_root=_authenticated(_facts()),
    )

    substituted = store._commit_authenticated_recursive_stark_root(
        expected_cursor=committed.head_cursor,
        authenticated_root=_authenticated(
            _facts(),
            authority_byte="aa",
            release_byte="bb",
        ),
    )

    assert substituted.accepted is False
    assert substituted.idempotent_replay is False
    assert substituted.reject_reason is RecursiveStarkAdmissionRejectReason.DUPLICATE_ROOT_JOURNAL
    assert store.read_cursor() == committed.head_cursor


@pytest.mark.parametrize(
    "candidate",
    (
        _authenticated(_facts(), authority_byte="aa"),
        _authenticated(_facts(), executable_byte="aa"),
        _authenticated(_facts(), request_byte="aa"),
        _authenticated(_facts(), release_byte="aa"),
        _authenticated(_facts(), replay_byte="aa"),
    ),
)
def test_each_outcome_provenance_field_prevents_false_idempotency(
    tmp_path: Path,
    candidate: _AuthenticatedRecursiveStarkRootFacts,
) -> None:
    store = _store(tmp_path)
    committed = store._commit_authenticated_recursive_stark_root(
        expected_cursor=store.read_cursor(),
        authenticated_root=_authenticated(_facts()),
    )

    substituted = store._commit_authenticated_recursive_stark_root(
        expected_cursor=committed.head_cursor,
        authenticated_root=candidate,
    )

    assert substituted.idempotent_replay is False
    assert substituted.reject_reason is RecursiveStarkAdmissionRejectReason.DUPLICATE_ROOT_JOURNAL
    assert store.read_cursor() == committed.head_cursor
