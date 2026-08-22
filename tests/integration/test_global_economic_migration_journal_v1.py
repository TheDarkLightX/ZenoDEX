"""Adversarial evidence for the durable migration activation journal."""

from __future__ import annotations

import hashlib
import sqlite3
import subprocess
import sys
import threading
from dataclasses import replace
from pathlib import Path

import pytest

import src.integration.global_economic_migration_journal_v1 as journal_module
from src.core.economic_initial_state_atom_coverage_v1 import EconomicInitialStateKindV1
from src.core.global_economic_durable_activation_v1 import (
    MAX_DURABLE_ECONOMIC_COMPONENT_BYTES_V1,
    DurableEconomicActivationRecordV1,
    DurableEconomicComponentKindV1,
    DurableEconomicComponentV1,
    DurableEconomicInitialStateBundleV1,
    decode_durable_economic_initial_state_bundle_v1,
    prepare_durable_economic_initial_state_bundle_v1,
)
from src.integration.global_economic_migration_journal_v1 import (
    DurableEconomicCommitStatusV1,
    GlobalEconomicMigrationJournalV1,
    _DurableEconomicCommitFaultV1,
    _SimulatedDurableEconomicCrashV1,
)
from tests.core.test_global_settlement_abi_v1 import (
    _initial_state_admission,
    _migration_admission_for_source_head,
    _profile,
    _source_manifest_for_state_v1,
    _state,
)


def _bundles_v1() -> tuple[
    DurableEconomicInitialStateBundleV1,
    DurableEconomicInitialStateBundleV1,
]:
    profile, _ = _profile()
    state = _state(profile, height=0)
    genesis = prepare_durable_economic_initial_state_bundle_v1(
        _initial_state_admission(profile, state),
        source_head=None,
    )
    _, _, migration_admission = _migration_admission_for_source_head(profile, state)
    migration = prepare_durable_economic_initial_state_bundle_v1(
        migration_admission,
        source_head=genesis.head,
    )
    return genesis, migration


def _alternate_migration_v1(
    source_bundle: DurableEconomicInitialStateBundleV1,
) -> DurableEconomicInitialStateBundleV1:
    profile, _ = _profile()
    state = _state(profile, height=0)
    _, _, admission = _migration_admission_for_source_head(profile, state)
    receipt_bytes = b"alternate-succinct-migration-receipt"
    receipt_root = "0x" + hashlib.sha256(receipt_bytes).hexdigest()
    alternate = replace(
        admission,
        certificate=replace(admission.certificate, receipt_root=receipt_root),
        receipt_bytes=receipt_bytes,
    )
    return prepare_durable_economic_initial_state_bundle_v1(
        alternate,
        source_head=source_bundle.head,
    )


def _migration_chain_v1() -> tuple[
    DurableEconomicInitialStateBundleV1,
    DurableEconomicInitialStateBundleV1,
    DurableEconomicInitialStateBundleV1,
]:
    source_profile, _ = _profile()
    source_state = _state(source_profile, height=0)
    genesis = prepare_durable_economic_initial_state_bundle_v1(
        _initial_state_admission(source_profile, source_state),
        source_head=None,
    )
    first_profile, first_state, first_admission = _migration_admission_for_source_head(
        source_profile,
        source_state,
    )
    first = prepare_durable_economic_initial_state_bundle_v1(
        first_admission,
        source_head=genesis.head,
    )
    provisional_second_state = replace(
        first_state,
        writer_epoch=first_state.writer_epoch + 1,
        height=first_state.height + 1,
    )
    second_manifest = _source_manifest_for_state_v1(
        EconomicInitialStateKindV1.MIGRATION,
        provisional_second_state,
    )
    second_profile, _ = _profile(
        source_manifest=second_manifest,
        authority_epoch=first_profile.authority_epoch + 1,
    )
    second_state = replace(
        provisional_second_state,
        writer_epoch=second_profile.authority_epoch,
        profile_root=second_profile.profile_id,
    )
    second_admission = _initial_state_admission(
        second_profile,
        second_state,
        kind=EconomicInitialStateKindV1.MIGRATION,
        source_manifest=second_manifest,
        source_profile_root=first_profile.profile_id,
        source_state_root=first_state.state_root,
        source_writer_epoch=first_state.writer_epoch,
        source_height=first_state.height,
        predecessor_state=first_state,
    )
    second = prepare_durable_economic_initial_state_bundle_v1(
        second_admission,
        source_head=first.head,
    )
    return genesis, first, second


def _direct_rows_v1(path: Path) -> tuple[int, str, bytes]:
    with sqlite3.connect(path) as connection:
        count = connection.execute("SELECT COUNT(*) FROM activations").fetchone()[0]
        head_id = connection.execute(
            "SELECT activation_id FROM current_head WHERE singleton = 1"
        ).fetchone()[0]
        bundle_bytes = connection.execute(
            "SELECT bundle_bytes FROM activations WHERE activation_id = ?",
            (head_id,),
        ).fetchone()[0]
    assert type(count) is int
    assert type(head_id) is str
    assert type(bundle_bytes) is bytes
    return count, head_id, bundle_bytes


def _replace_record_fragment_v1(
    bundle: DurableEconomicInitialStateBundleV1,
    old: bytes,
    new: bytes,
) -> bytes:
    encoded = bundle.canonical_bytes
    magic_size = len(b"ZGDAJ1\x00")
    record_size = int.from_bytes(encoded[magic_size : magic_size + 4], "big")
    record_start = magic_size + 4
    record_end = record_start + record_size
    record = encoded[record_start:record_end]
    if record.count(old) != 1:
        raise AssertionError("test mutation fragment must occur exactly once")
    mutated_record = record.replace(old, new, 1)
    return (
        encoded[:magic_size]
        + len(mutated_record).to_bytes(4, "big")
        + mutated_record
        + encoded[record_end:]
    )


def test_given_genesis_when_created_and_reopened_then_exact_complete_head_survives(
    tmp_path: Path,
) -> None:
    # Arrange: Alice has one complete, structurally admitted genesis bundle.
    genesis, _ = _bundles_v1()
    path = tmp_path / "economic-activation.sqlite"

    # Act: the operator creates, closes, and reopens the durable checkpoint.
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    journal.close()
    reopened = GlobalEconomicMigrationJournalV1.open(path)

    # Assert: the typed view and independent stored-byte oracle agree exactly.
    assert reopened.head == genesis.head
    count, head_id, stored_bytes = _direct_rows_v1(path)
    assert (count, head_id) == (1, genesis.record.activation_id)
    assert stored_bytes == genesis.canonical_bytes
    assert decode_durable_economic_initial_state_bundle_v1(stored_bytes) == genesis
    reopened.close()


def test_given_current_cas_token_when_migration_commits_then_full_bundle_is_atomic(
    tmp_path: Path,
) -> None:
    # Arrange: the sequencer holds a CAS snapshot token for the exact genesis head.
    genesis, migration = _bundles_v1()
    path = tmp_path / "economic-activation.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    token = journal.acquire_cas_head_token()

    # Act: publish one adjacent migration activation.
    outcome = journal.commit_migration(migration, token)
    journal.close()

    # Assert: SQLite contains one complete successor and points only at it.
    assert outcome.status is DurableEconomicCommitStatusV1.COMMITTED
    assert outcome.head == migration.head
    count, head_id, stored_bytes = _direct_rows_v1(path)
    assert (count, head_id) == (2, migration.record.activation_id)
    assert stored_bytes == migration.canonical_bytes
    with GlobalEconomicMigrationJournalV1.open(path) as reopened:
        assert reopened.head == migration.head


def test_given_lost_ack_when_exact_bundle_retries_then_result_is_idempotent(
    tmp_path: Path,
) -> None:
    # Arrange: one migration committed and the caller retained its old CAS token.
    genesis, migration = _bundles_v1()
    path = tmp_path / "economic-activation.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    token = journal.acquire_cas_head_token()
    assert (
        journal.commit_migration(migration, token).status
        is DurableEconomicCommitStatusV1.COMMITTED
    )

    # Act: the same caller retries the byte-identical activation after losing the ACK.
    retry = journal.commit_migration(migration, token)

    # Assert: retry classification is exact and introduces no duplicate history row.
    assert retry.status is DurableEconomicCommitStatusV1.ALREADY_COMMITTED
    assert retry.head == migration.head
    assert _direct_rows_v1(path)[:2] == (2, migration.record.activation_id)
    journal.close()


def test_historical_exact_retry_returns_original_activation_and_current_head(
    tmp_path: Path,
) -> None:
    # Arrange: two later generations commit after the caller loses generation-1's ACK.
    genesis, first, second = _migration_chain_v1()
    path = tmp_path / "historical-retry.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    first_token = journal.acquire_cas_head_token()
    journal.commit_migration(first, first_token)
    journal.commit_migration(second, journal.acquire_cas_head_token())

    # Act: retry the byte-identical historical generation through its original token.
    retry = journal.commit_migration(first, first_token)

    # Assert: valid history is idempotent, and current vs committed heads stay distinct.
    assert retry.status is DurableEconomicCommitStatusV1.ALREADY_COMMITTED
    assert retry.committed_activation == first.head
    assert retry.head == second.head
    assert _direct_rows_v1(path)[:2] == (3, second.record.activation_id)
    journal.close()


def test_bundle_rejects_declared_target_roots_that_contradict_stored_body() -> None:
    # Arrange: reproduce the reviewer's forged-head counterexample over valid payloads.
    _, migration = _bundles_v1()
    record = migration.record
    forged_record = DurableEconomicActivationRecordV1.build(
        kind=record.kind,
        generation=record.generation,
        chain_id=record.chain_id,
        deployment_root=record.deployment_root,
        profile_root="0x" + "aa" * 32,
        state_root="0x" + "bb" * 32,
        writer_epoch=record.writer_epoch,
        height=record.height,
        source_activation_id=record.source_activation_id,
        source_profile_root=record.source_profile_root,
        source_state_root=record.source_state_root,
        source_writer_epoch=record.source_writer_epoch,
        source_height=record.source_height,
        certificate_root="0x" + "cc" * 32,
        component_commitments=record.component_commitments,
    )

    # Act and assert: the bundle derives roots from bodies and rejects contradiction.
    with pytest.raises(ValueError, match="target profile or state binding mismatch"):
        DurableEconomicInitialStateBundleV1(forged_record, migration.components)


def test_commit_resnapshots_bundle_after_hostile_frozen_object_mutation(
    tmp_path: Path,
) -> None:
    # Arrange: bypass frozen-dataclass guards after the bundle validated once.
    genesis, migration = _bundles_v1()
    path = tmp_path / "hostile-object-mutation.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    token = journal.acquire_cas_head_token()
    record = migration.record
    forged_record = DurableEconomicActivationRecordV1.build(
        kind=record.kind,
        generation=record.generation,
        chain_id=record.chain_id,
        deployment_root=record.deployment_root,
        profile_root="0x" + "aa" * 32,
        state_root="0x" + "bb" * 32,
        writer_epoch=record.writer_epoch,
        height=record.height,
        source_activation_id=record.source_activation_id,
        source_profile_root=record.source_profile_root,
        source_state_root=record.source_state_root,
        source_writer_epoch=record.source_writer_epoch,
        source_height=record.source_height,
        certificate_root="0x" + "cc" * 32,
        component_commitments=record.component_commitments,
    )
    object.__setattr__(migration, "record", forged_record)

    # Act and assert: commit snapshots bytes into a newly validated owned bundle.
    with pytest.raises(ValueError, match="target profile or state binding mismatch"):
        journal.commit_migration(migration, token)
    assert _direct_rows_v1(path)[:2] == (1, genesis.record.activation_id)
    journal.close()


def test_given_two_writers_when_one_wins_then_stale_alternative_is_no_effect(
    tmp_path: Path,
) -> None:
    # Arrange: two sequencers snapshot the same source and propose distinct receipts.
    genesis, migration = _bundles_v1()
    alternate = _alternate_migration_v1(genesis)
    path = tmp_path / "economic-activation.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    first_token = journal.acquire_cas_head_token()
    second_token = journal.acquire_cas_head_token()

    # Act: the first wins, then the second attempts its different successor.
    winner = journal.commit_migration(migration, first_token)
    loser = journal.commit_migration(alternate, second_token)

    # Assert: one history row wins and the losing proposal leaves no residue.
    assert winner.status is DurableEconomicCommitStatusV1.COMMITTED
    assert loser.status is DurableEconomicCommitStatusV1.STALE_HEAD
    assert loser.head == migration.head
    count, head_id, stored_bytes = _direct_rows_v1(path)
    assert (count, head_id, stored_bytes) == (
        2,
        migration.record.activation_id,
        migration.canonical_bytes,
    )
    journal.close()


def test_given_two_open_instances_when_one_commits_then_old_cas_token_is_stale(
    tmp_path: Path,
) -> None:
    # Arrange: two independent process shells snapshot the same durable head.
    genesis, migration = _bundles_v1()
    alternate = _alternate_migration_v1(genesis)
    path = tmp_path / "cross-instance-race.sqlite"
    first = GlobalEconomicMigrationJournalV1.create(path, genesis)
    second = GlobalEconomicMigrationJournalV1.open(path)
    first_token = first.acquire_cas_head_token()
    second_token = second.acquire_cas_head_token()

    # Act: the first instance commits before the second submits its distinct target.
    winner = first.commit_migration(migration, first_token)
    loser = second.commit_migration(alternate, second_token)

    # Assert: SQLite serialization plus source CAS permanently rejects the old view.
    assert winner.status is DurableEconomicCommitStatusV1.COMMITTED
    assert loser.status is DurableEconomicCommitStatusV1.STALE_HEAD
    assert loser.head == migration.head
    assert _direct_rows_v1(path)[:2] == (2, migration.record.activation_id)
    first.close()
    second.close()


def test_snapshot_reader_cannot_mix_history_and_head_across_concurrent_commit(
    tmp_path: Path,
) -> None:
    # Arrange: pause a reader after history while a second connection starts its commit.
    genesis, migration = _bundles_v1()
    path = tmp_path / "coherent-read.sqlite"
    writer = GlobalEconomicMigrationJournalV1.create(path, genesis)
    reader = GlobalEconomicMigrationJournalV1.open(path)
    token = writer.acquire_cas_head_token()
    history_read = threading.Event()
    writer_attempting = threading.Event()
    original_read_history = reader._read_history_v1

    def coordinated_history_read() -> tuple[DurableEconomicInitialStateBundleV1, ...]:
        history = original_read_history()
        history_read.set()
        assert writer_attempting.wait(timeout=5)
        return history

    reader._read_history_v1 = coordinated_history_read  # type: ignore[method-assign]
    writer_outcomes: list[object] = []

    def commit_after_history() -> None:
        assert history_read.wait(timeout=5)
        writer_attempting.set()
        writer_outcomes.append(writer.commit_migration(migration, token))

    thread = threading.Thread(target=commit_after_history)
    thread.start()

    # Act: one deferred read transaction observes a complete PRE snapshot.
    observed = reader.head
    thread.join(timeout=5)

    # Assert: no false corruption occurs; writer proceeds after the read commits.
    assert not thread.is_alive()
    assert observed == genesis.head
    assert len(writer_outcomes) == 1
    assert writer_outcomes[0].status is DurableEconomicCommitStatusV1.COMMITTED
    assert writer.head == migration.head
    reader.close()
    writer.close()


@pytest.mark.parametrize(
    ("fault", "expected_post"),
    (
        (_DurableEconomicCommitFaultV1.AFTER_BEGIN, False),
        (_DurableEconomicCommitFaultV1.AFTER_INSERT, False),
        (_DurableEconomicCommitFaultV1.AFTER_HEAD_UPDATE_BEFORE_COMMIT, False),
        (_DurableEconomicCommitFaultV1.AFTER_COMMIT_BEFORE_ACK, True),
    ),
)
def test_given_crash_boundary_when_reopened_then_store_is_exact_pre_or_post(
    tmp_path: Path,
    fault: _DurableEconomicCommitFaultV1,
    expected_post: bool,
) -> None:
    # Arrange: one deterministic failure point surrounds the SQLite commit boundary.
    genesis, migration = _bundles_v1()
    path = tmp_path / f"economic-activation-{fault.value}.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    token = journal.acquire_cas_head_token()

    # Act: simulate process loss at the selected boundary, then reopen from disk.
    with pytest.raises(_SimulatedDurableEconomicCrashV1, match=fault.value):
        journal._commit_migration_with_fault_for_test_v1(migration, token, fault)
    journal.close()
    reopened = GlobalEconomicMigrationJournalV1.open(path)

    # Assert: no mixed state exists; pre-commit faults yield PRE and post-commit yields POST.
    expected = migration if expected_post else genesis
    expected_count = 2 if expected_post else 1
    assert reopened.head == expected.head
    assert _direct_rows_v1(path)[:2] == (
        expected_count,
        expected.record.activation_id,
    )
    if expected_post:
        retry = reopened.commit_migration(migration, reopened.acquire_cas_head_token())
        assert retry.status is DurableEconomicCommitStatusV1.ALREADY_COMMITTED
    reopened.close()


@pytest.mark.parametrize(
    ("fault", "expected_post"),
    (
        (_DurableEconomicCommitFaultV1.AFTER_BEGIN, False),
        (_DurableEconomicCommitFaultV1.AFTER_INSERT, False),
        (_DurableEconomicCommitFaultV1.AFTER_HEAD_UPDATE_BEFORE_COMMIT, False),
        (_DurableEconomicCommitFaultV1.AFTER_COMMIT_BEFORE_ACK, True),
    ),
)
def test_given_abrupt_process_exit_when_reopened_then_sqlite_recovers_pre_or_post(
    tmp_path: Path,
    fault: _DurableEconomicCommitFaultV1,
    expected_post: bool,
) -> None:
    # Arrange: create the source checkpoint before transferring work to a child process.
    genesis, migration = _bundles_v1()
    path = tmp_path / f"hard-exit-{fault.value}.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    journal.close()
    child_program = """
import os
import sys

import src.integration.global_economic_migration_journal_v1 as journal_module
from tests.integration.test_global_economic_migration_journal_v1 import _bundles_v1

path = sys.argv[1]
fault = journal_module._DurableEconomicCommitFaultV1(sys.argv[2])
_, migration = _bundles_v1()
journal = journal_module.GlobalEconomicMigrationJournalV1.open(path)
token = journal.acquire_cas_head_token()
journal_module._SimulatedDurableEconomicCrashV1 = lambda _message: os._exit(97)
journal._commit_migration_with_fault_for_test_v1(migration, token, fault)
raise RuntimeError("hard-exit mutation unexpectedly returned")
"""

    # Act: terminate without Python exception unwinding or the explicit rollback handler.
    child = subprocess.run(
        [sys.executable, "-c", child_program, str(path), fault.value],
        cwd=Path(__file__).resolve().parents[2],
        check=False,
        timeout=20,
    )

    # Assert: SQLite recovery exposes the same fixed PRE/POST oracle as clean injection.
    assert child.returncode == 97
    expected = migration if expected_post else genesis
    expected_count = 2 if expected_post else 1
    with GlobalEconomicMigrationJournalV1.open(path) as reopened:
        assert reopened.head == expected.head
    assert _direct_rows_v1(path)[:2] == (
        expected_count,
        expected.record.activation_id,
    )


def test_given_foreign_cas_token_when_used_then_commit_rejects_without_effect(
    tmp_path: Path,
) -> None:
    # Arrange: Mallory obtains a valid token from a different journal instance.
    genesis, migration = _bundles_v1()
    first_path = tmp_path / "first.sqlite"
    second_path = tmp_path / "second.sqlite"
    first = GlobalEconomicMigrationJournalV1.create(first_path, genesis)
    second = GlobalEconomicMigrationJournalV1.create(second_path, genesis)
    foreign_token = second.acquire_cas_head_token()

    # Act and assert: process-local token ownership rejects before mutation.
    with pytest.raises(ValueError, match="foreign or forged"):
        first.commit_migration(migration, foreign_token)
    assert _direct_rows_v1(first_path)[:2] == (1, genesis.record.activation_id)
    first.close()
    second.close()


def test_cas_head_token_is_immutable_and_registry_bound(tmp_path: Path) -> None:
    # Arrange: a sequencer receives a journal-minted CAS token for one exact head.
    genesis, migration = _bundles_v1()
    path = tmp_path / "immutable-cas-token.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    token = journal.acquire_cas_head_token()

    # Act and assert: ordinary mutation is blocked and the original binding still commits.
    with pytest.raises(TypeError, match="immutable"):
        token._DurableEconomicCasHeadTokenV1__generation = 99  # type: ignore[attr-defined]
    outcome = journal.commit_migration(migration, token)
    assert outcome.status is DurableEconomicCommitStatusV1.COMMITTED
    journal.close()


def test_given_stale_source_head_when_preparing_then_bundle_construction_rejects() -> None:
    # Arrange: a migration admission names genesis while the supplied head claims another root.
    genesis, _ = _bundles_v1()
    profile, _ = _profile()
    state = _state(profile, height=0)
    _, _, admission = _migration_admission_for_source_head(profile, state)
    stale_head = replace(genesis.head, state_root="0x" + "ab" * 32)

    # Act and assert: source binding fails in the pure constructor.
    with pytest.raises(ValueError, match="source state root mismatch"):
        prepare_durable_economic_initial_state_bundle_v1(
            admission,
            source_head=stale_head,
        )


def test_generation_upper_boundary_rejects_successor_before_overflow() -> None:
    # Arrange: BVA at u64::MAX models a source generation with no successor.
    genesis, _ = _bundles_v1()
    profile, _ = _profile()
    state = _state(profile, height=0)
    _, _, admission = _migration_admission_for_source_head(profile, state)
    exhausted = replace(genesis.head, generation=(1 << 64) - 1)

    # Act and assert: no wraparound or implicit large-integer behavior is permitted.
    with pytest.raises(ValueError, match="source generation cannot advance"):
        prepare_durable_economic_initial_state_bundle_v1(
            admission,
            source_head=exhausted,
        )


def test_history_capacity_accepts_max_and_rejects_max_plus_one_without_effect(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: V1's bounded test oracle uses a two-record cap for a short replay.
    genesis, first, second = _migration_chain_v1()
    path = tmp_path / "history-capacity.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    monkeypatch.setattr(journal_module, "_MAX_ACTIVATION_HISTORY_V1", 2)

    # Act: max-1 advances exactly to max; a further valid successor is refused.
    at_max = journal.commit_migration(first, journal.acquire_cas_head_token())
    over_max = journal.commit_migration(second, journal.acquire_cas_head_token())

    # Assert: capacity is typed, durable state remains reopenable, and no row leaks.
    assert at_max.status is DurableEconomicCommitStatusV1.COMMITTED
    assert over_max.status is DurableEconomicCommitStatusV1.CAPACITY_EXCEEDED
    assert over_max.committed_activation is None
    assert over_max.head == first.head
    assert _direct_rows_v1(path)[:2] == (2, first.record.activation_id)
    journal.close()
    with GlobalEconomicMigrationJournalV1.open(path) as reopened:
        assert reopened.head == first.head


@pytest.mark.parametrize("remaining_byte_delta", (0, -1))
def test_store_byte_capacity_has_exact_inclusive_boundary(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    remaining_byte_delta: int,
) -> None:
    # Arrange: set the store ceiling to target-size exact or one byte below.
    genesis, migration = _bundles_v1()
    path = tmp_path / f"byte-capacity-{remaining_byte_delta}.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    current_bytes = len(genesis.canonical_bytes)
    target_bytes = len(migration.canonical_bytes)
    monkeypatch.setattr(
        journal_module,
        "_MAX_ACTIVATION_STORE_BYTES_V1",
        current_bytes + target_bytes + remaining_byte_delta,
    )

    # Act: attempt the adjacent migration at the selected BVA point.
    outcome = journal.commit_migration(migration, journal.acquire_cas_head_token())

    # Assert: equality accepts; one byte less rejects and preserves exact PRE.
    expected_status = (
        DurableEconomicCommitStatusV1.COMMITTED
        if remaining_byte_delta == 0
        else DurableEconomicCommitStatusV1.CAPACITY_EXCEEDED
    )
    assert outcome.status is expected_status
    expected = migration if remaining_byte_delta == 0 else genesis
    expected_count = 2 if remaining_byte_delta == 0 else 1
    assert _direct_rows_v1(path)[:2] == (expected_count, expected.record.activation_id)
    journal.close()
    with GlobalEconomicMigrationJournalV1.open(path) as reopened:
        assert reopened.head == expected.head


@pytest.mark.parametrize("mutation", ("truncate", "append"))
def test_given_corrupt_bundle_bytes_when_reopened_then_journal_fails_closed(
    tmp_path: Path,
    mutation: str,
) -> None:
    # Arrange: an offline attacker corrupts the current immutable activation payload.
    genesis, _ = _bundles_v1()
    path = tmp_path / f"corrupt-{mutation}.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    journal.close()
    with sqlite3.connect(path) as connection:
        raw = connection.execute("SELECT bundle_bytes FROM activations").fetchone()[0]
        corrupted = raw[:-1] if mutation == "truncate" else raw + b"x"
        connection.execute("UPDATE activations SET bundle_bytes = ?", (corrupted,))

    # Act and assert: exact framing and commitment validation refuse the store.
    with pytest.raises(ValueError):
        GlobalEconomicMigrationJournalV1.open(path)


def test_given_head_rollback_when_reopened_then_non_tip_pointer_fails_closed(
    tmp_path: Path,
) -> None:
    # Arrange: commit a migration, then tamper the singleton pointer back to genesis.
    genesis, migration = _bundles_v1()
    path = tmp_path / "rolled-back-head.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    journal.commit_migration(migration, journal.acquire_cas_head_token())
    journal.close()
    with sqlite3.connect(path) as connection:
        connection.execute("PRAGMA foreign_keys = ON")
        connection.execute(
            "UPDATE current_head SET activation_id = ? WHERE singleton = 1",
            (genesis.record.activation_id,),
        )

    # Act and assert: history remains present, so pointer rollback cannot masquerade as PRE.
    with pytest.raises(ValueError, match="not the history tip"):
        GlobalEconomicMigrationJournalV1.open(path)


def test_given_unknown_schema_object_when_reopened_then_journal_fails_closed(
    tmp_path: Path,
) -> None:
    # Arrange: a sidecar table appears inside the authority database.
    genesis, _ = _bundles_v1()
    path = tmp_path / "extra-table.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    journal.close()
    with sqlite3.connect(path) as connection:
        connection.execute("CREATE TABLE shadow_writer(value TEXT)")

    # Act and assert: the schema object set is closed, so the added surface is rejected.
    with pytest.raises(RuntimeError, match="exact schema mismatch"):
        GlobalEconomicMigrationJournalV1.open(path)


def test_given_rebuilt_non_strict_metadata_when_reopened_then_schema_rejects(
    tmp_path: Path,
) -> None:
    # Arrange: reproduce a schema that preserves columns while dropping STRICT/CHECK.
    genesis, _ = _bundles_v1()
    path = tmp_path / "weak-schema.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    journal.close()
    with sqlite3.connect(path) as connection:
        connection.execute("ALTER TABLE metadata RENAME TO metadata_old")
        connection.execute(
            "CREATE TABLE metadata(singleton INTEGER PRIMARY KEY, schema_name TEXT NOT NULL)"
        )
        connection.execute(
            "INSERT INTO metadata(singleton, schema_name) "
            "SELECT singleton, schema_name FROM metadata_old"
        )
        connection.execute("DROP TABLE metadata_old")

    # Act and assert: exact DDL validation rejects the weakened authority schema.
    with pytest.raises(RuntimeError, match="exact schema mismatch"):
        GlobalEconomicMigrationJournalV1.open(path)


def test_given_rebuilt_head_without_foreign_key_then_schema_rejects(
    tmp_path: Path,
) -> None:
    # Arrange: preserve rows and columns while deleting the head-to-history FK.
    genesis, _ = _bundles_v1()
    path = tmp_path / "missing-foreign-key.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    journal.close()
    with sqlite3.connect(path) as connection:
        connection.execute("ALTER TABLE current_head RENAME TO current_head_old")
        connection.execute(
            "CREATE TABLE current_head("
            "singleton INTEGER PRIMARY KEY CHECK (singleton = 1), "
            "activation_id TEXT NOT NULL"
            ") STRICT"
        )
        connection.execute(
            "INSERT INTO current_head(singleton, activation_id) "
            "SELECT singleton, activation_id FROM current_head_old"
        )
        connection.execute("DROP TABLE current_head_old")

    # Act and assert: column equivalence cannot hide the missing FK contract.
    with pytest.raises(RuntimeError, match="exact schema mismatch"):
        GlobalEconomicMigrationJournalV1.open(path)


def test_given_rebuilt_history_without_unique_generation_then_schema_rejects(
    tmp_path: Path,
) -> None:
    # Arrange: preserve history data while deleting generation uniqueness.
    genesis, _ = _bundles_v1()
    path = tmp_path / "missing-unique-index.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    journal.close()
    with sqlite3.connect(path) as connection:
        connection.execute("PRAGMA foreign_keys = OFF")
        connection.execute("ALTER TABLE activations RENAME TO activations_old")
        connection.execute(
            "CREATE TABLE activations("
            "activation_id TEXT PRIMARY KEY NOT NULL, "
            "generation_decimal TEXT NOT NULL, "
            "bundle_bytes BLOB NOT NULL"
            ") STRICT"
        )
        connection.execute(
            "INSERT INTO activations(activation_id, generation_decimal, bundle_bytes) "
            "SELECT activation_id, generation_decimal, bundle_bytes FROM activations_old"
        )
        connection.execute("DROP TABLE activations_old")

    # Act and assert: exact DDL and index checks reject the weakened uniqueness rule.
    with pytest.raises(RuntimeError, match="exact schema mismatch"):
        GlobalEconomicMigrationJournalV1.open(path)


def test_trusted_schema_configuration_regression_is_detected(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: create a valid store, then mutate connection setup back to trusted schema.
    genesis, _ = _bundles_v1()
    path = tmp_path / "trusted-schema.sqlite"
    journal = GlobalEconomicMigrationJournalV1.create(path, genesis)
    journal.close()
    original_configure = journal_module._configure_connection_v1

    def enable_trusted_schema(connection: sqlite3.Connection) -> None:
        original_configure(connection)
        connection.execute("PRAGMA trusted_schema = ON")

    monkeypatch.setattr(
        journal_module,
        "_configure_connection_v1",
        enable_trusted_schema,
    )

    # Act and assert: the live connection pragma is part of the store contract.
    with pytest.raises(RuntimeError, match="trusted schema must be disabled"):
        GlobalEconomicMigrationJournalV1.open(path)


def test_bundle_decoder_rejects_non_bytes_and_trailing_data() -> None:
    # Arrange: exact canonical bytes are the sole accepted decode boundary.
    genesis, _ = _bundles_v1()

    # Act and assert: hostile type substitution and extension bytes both fail.
    with pytest.raises(TypeError, match="exact bytes"):
        decode_durable_economic_initial_state_bundle_v1(bytearray(genesis.canonical_bytes))  # type: ignore[arg-type]
    with pytest.raises(ValueError, match="trailing bytes"):
        decode_durable_economic_initial_state_bundle_v1(genesis.canonical_bytes + b"\x00")


def test_bundle_decoder_rejects_duplicate_noncanonical_and_unknown_record_shapes() -> None:
    # Arrange: each mutation preserves framing while attacking one canonical-record rule.
    genesis, _ = _bundles_v1()
    activation_fragment = (
        b'"activation_id":"' + genesis.record.activation_id.encode("ascii") + b'"'
    )
    duplicate_key = _replace_record_fragment_v1(
        genesis,
        activation_fragment,
        activation_fragment + b"," + activation_fragment,
    )
    writer_epoch_fragment = (
        b'"writer_epoch":' + str(genesis.record.writer_epoch).encode("ascii") + b"}"
    )
    noncanonical_space = _replace_record_fragment_v1(
        genesis,
        writer_epoch_fragment,
        writer_epoch_fragment[:-1] + b" }",
    )
    unknown_component = _replace_record_fragment_v1(
        genesis,
        b'"kind":"PROFILE"',
        b'"kind":"UNKNOWN"',
    )
    float_generation = _replace_record_fragment_v1(
        genesis,
        b'"generation":0',
        b'"generation":0.0',
    )

    # Act and assert: duplicate keys, alternate whitespace, open variants and floats fail.
    for mutated in (
        duplicate_key,
        noncanonical_space,
        unknown_component,
        float_generation,
    ):
        with pytest.raises((TypeError, ValueError)):
            decode_durable_economic_initial_state_bundle_v1(mutated)


def test_component_byte_count_boundary_accepts_max_and_rejects_neighbors() -> None:
    # Arrange: the component contract has an explicit closed interval [1, 8 MiB].
    one_atom = b"x"
    maximum = b"x" * MAX_DURABLE_ECONOMIC_COMPONENT_BYTES_V1

    # Act and assert: zero and max+1 reject while both inclusive boundaries survive.
    assert DurableEconomicComponentV1(
        DurableEconomicComponentKindV1.RECEIPT,
        one_atom,
    ).commitment.byte_count == 1
    assert DurableEconomicComponentV1(
        DurableEconomicComponentKindV1.RECEIPT,
        maximum,
    ).commitment.byte_count == MAX_DURABLE_ECONOMIC_COMPONENT_BYTES_V1
    with pytest.raises(ValueError, match="outside the byte bound"):
        DurableEconomicComponentV1(DurableEconomicComponentKindV1.RECEIPT, b"")
    with pytest.raises(ValueError, match="outside the byte bound"):
        DurableEconomicComponentV1(
            DurableEconomicComponentKindV1.RECEIPT,
            maximum + b"x",
        )


def test_durable_migration_journal_remains_unmounted_from_runtime_sources() -> None:
    # Arrange: mounting requires a separate verifier-owned authority change.
    root = Path(__file__).resolve().parents[2]
    module_name = "global_economic_migration_journal_v1"
    defining_path = root / "src" / "integration" / f"{module_name}.py"

    # Act: inspect all other Python runtime sources for an import/reference.
    mounted_references = []
    for path in sorted((root / "src").rglob("*.py")):
        if path == defining_path:
            continue
        if module_name in path.read_text(encoding="utf-8"):
            mounted_references.append(path.relative_to(root).as_posix())

    # Assert: tested durability infrastructure has no publication caller.
    assert mounted_references == []
