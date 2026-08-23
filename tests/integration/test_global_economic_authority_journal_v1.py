"""Canonical, transition, and CAS evidence for the shared authority head."""

from __future__ import annotations

import os
import sqlite3
import stat
from dataclasses import replace
from pathlib import Path
from threading import Event, Thread

import pytest

import src.integration.global_economic_authority_journal_v1 as authority_journal_module
from src.core.global_economic_authority_head_v1 import (
    MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V1,
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
    decode_global_economic_authority_head_v1,
    require_global_economic_authority_successor_v1,
)
from src.integration.global_economic_authority_journal_v1 import (
    GlobalEconomicAuthorityBootstrapBusyV1,
    GlobalEconomicAuthorityCommitStatusV1,
    GlobalEconomicAuthorityJournalV1,
    _attach_authority_store_v1,
)


def _root(byte: int) -> str:
    return "0x" + f"{byte:02x}" * 32


def _head() -> GlobalEconomicAuthorityHeadV1:
    return GlobalEconomicAuthorityHeadV1(
        generation=0,
        activation_id=_root(1),
        chain_id="tau-testnet",
        deployment_root=_root(2),
        epoch_store_root=_root(8),
        profile_root=_root(3),
        writer_epoch=7,
        verifier_registry_root=_root(4),
        verifier_release_id=_root(5),
        verifier_binding_root=_root(6),
        root_image_id=_root(7),
        status=GlobalEconomicAuthorityStatusV1.ACTIVE,
    )


def test_authority_head_canonical_roundtrip_binds_every_coordinate() -> None:
    # Arrange: one complete active authority generation.
    head = _head()

    # Act: cross the canonical byte boundary and reconstruct an owned value.
    decoded = decode_global_economic_authority_head_v1(head.canonical_bytes)

    # Assert: exact coordinates and the content-derived root are stable.
    assert decoded == head
    assert decoded.authority_root == head.authority_root


def test_revocation_is_adjacent_coordinate_preserving_and_terminal() -> None:
    # Arrange: Alice holds one active authority head.
    active = _head()

    # Act: governance constructs its only legal emergency revocation successor.
    revoked = active.revoked_successor()

    # Assert: revocation changes only generation and status, then becomes terminal.
    require_global_economic_authority_successor_v1(active, revoked)
    assert revoked.generation == active.generation + 1
    assert revoked.status is GlobalEconomicAuthorityStatusV1.REVOKED
    with pytest.raises(ValueError, match="terminal"):
        require_global_economic_authority_successor_v1(
            revoked,
            replace(revoked, generation=revoked.generation + 1),
        )


def test_revocation_cannot_smuggle_a_profile_or_verifier_change() -> None:
    # Arrange: Mallory labels a changed verifier release as a revocation.
    active = _head()
    forged = replace(
        active.revoked_successor(),
        verifier_release_id=_root(8),
    )

    # Act and assert: the closed transition rejects mixed rotation classes.
    with pytest.raises(ValueError, match="revocation changed coordinates"):
        require_global_economic_authority_successor_v1(active, forged)


def test_generation_bva_rejects_boolean_alias_and_maximum_successor() -> None:
    # Arrange: one Boolean-alias constructor and one exact u64-maximum head.
    active = _head()

    # Act and assert: bool never aliases generation zero at the typed boundary.
    with pytest.raises(TypeError, match="exact integer"):
        replace(active, generation=False)

    # Act and assert: the maximum generation cannot mint any successor.
    at_max = replace(active, generation=(1 << 64) - 1)
    with pytest.raises(ValueError, match="cannot advance"):
        at_max.revoked_successor()


def test_decoder_rejects_one_byte_over_the_public_head_bound() -> None:
    # Arrange: one hostile payload exactly one byte beyond the decode budget.
    oversized = b"x" * (MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V1 + 1)

    # Act and assert: size rejection occurs before JSON parsing or allocation.
    with pytest.raises(ValueError, match="outside the bound"):
        decode_global_economic_authority_head_v1(oversized)


def test_decoder_normalizes_hostile_json_nesting_to_typed_rejection() -> None:
    # Arrange: deeply nested JSON remains under the byte budget.
    hostile = (b"[" * 1_500) + (b"]" * 1_500)
    assert len(hostile) < MAX_GLOBAL_ECONOMIC_AUTHORITY_HEAD_BYTES_V1

    # Act and assert: parser recursion never escapes as an untyped crash.
    with pytest.raises(ValueError, match="nesting exceeds"):
        decode_global_economic_authority_head_v1(hostile)


def test_profile_migration_requires_new_profile_activation_and_same_store() -> None:
    # Arrange: Mallory proposes verifier-only and store-switching successors.
    active = _head()
    verifier_only = replace(
        active,
        generation=1,
        verifier_release_id=_root(9),
    )
    changed_store = replace(
        active,
        generation=1,
        activation_id=_root(10),
        epoch_store_root=_root(11),
        profile_root=_root(12),
        writer_epoch=active.writer_epoch + 1,
    )

    # Act and assert: ABI V1 admits neither semantic shortcut.
    with pytest.raises(ValueError, match="exact profile migration"):
        require_global_economic_authority_successor_v1(active, verifier_only)
    with pytest.raises(ValueError, match="epoch store changed"):
        require_global_economic_authority_successor_v1(active, changed_store)


def test_journal_commit_reopen_and_exact_retry_preserve_one_authority_tip(
    tmp_path: Path,
) -> None:
    # Arrange: one generation-zero authority journal and its current CAS token.
    path = tmp_path / "authority.sqlite"
    active = _head()
    journal = GlobalEconomicAuthorityJournalV1.create(path, active)
    token = journal._acquire_cas_head_token_for_unmounted_control_plane_v1()
    revoked = active.revoked_successor()

    # Act: commit revocation, reopen, and retry after a lost acknowledgement.
    committed = journal._commit_successor_for_unmounted_control_plane_v1(
        revoked,
        token,
    )
    journal.close()
    reopened = GlobalEconomicAuthorityJournalV1.open(path)
    retried = reopened._commit_successor_for_unmounted_control_plane_v1(
        revoked,
        reopened._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )

    # Assert: one durable successor exists and retry adds no generation.
    assert committed.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    assert retried.status is (
        GlobalEconomicAuthorityCommitStatusV1.ALREADY_COMMITTED
    )
    assert reopened.head == revoked
    reopened.close()


def test_concurrent_authority_bootstrap_has_one_winner_and_one_typed_busy(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: hold the first installer after it owns the directory lock.
    path = tmp_path / "concurrent-authority-create.sqlite"
    active = _head()
    original_initialize = authority_journal_module._initialize_authority_candidate_v1
    entered = Event()
    release = Event()

    def blocking_initialize(
        candidate_path: Path,
        initial_head: GlobalEconomicAuthorityHeadV1,
    ) -> None:
        entered.set()
        if not release.wait(timeout=10):
            raise RuntimeError("test authority bootstrap release timed out")
        original_initialize(candidate_path, initial_head)

    monkeypatch.setattr(
        authority_journal_module,
        "_initialize_authority_candidate_v1",
        blocking_initialize,
    )
    journals: list[GlobalEconomicAuthorityJournalV1] = []
    errors: list[BaseException] = []

    def create() -> None:
        try:
            journals.append(GlobalEconomicAuthorityJournalV1.create(path, active))
        except BaseException as exc:
            errors.append(exc)

    first = Thread(target=create)
    second = Thread(target=create)

    # Act: the second creator reaches the same directory while install is live.
    first.start()
    assert entered.wait(timeout=10)
    second.start()
    second.join(timeout=15)
    release.set()
    first.join(timeout=15)

    # Assert: no SQLite lock timeout leaks and only one complete store installs.
    assert not first.is_alive()
    assert not second.is_alive()
    assert len(journals) == 1
    assert len(errors) == 1
    assert type(errors[0]) is GlobalEconomicAuthorityBootstrapBusyV1
    assert journals[0].head == active
    journals[0].close()
    with GlobalEconomicAuthorityJournalV1.open(path) as reopened:
        assert reopened.head == active


def test_authority_create_never_adopts_preexisting_namespace_entries(
    tmp_path: Path,
) -> None:
    # Arrange: Mallory places empty, SQLite, malformed, hardlinked, and FIFO
    # entries at paths an authority installer may be asked to use.
    active = _head()
    zero = tmp_path / "preexisting-zero.sqlite"
    zero.write_bytes(b"")
    empty_sqlite = tmp_path / "preexisting-empty-sqlite.sqlite"
    with sqlite3.connect(empty_sqlite) as connection:
        connection.execute("VACUUM")
    malformed = tmp_path / "preexisting-malformed.sqlite"
    malformed.write_bytes(b"not a sqlite database")
    hardlink_source = tmp_path / "preexisting-hardlink-source"
    hardlink_source.write_bytes(b"")
    hardlink = tmp_path / "preexisting-hardlink.sqlite"
    os.link(hardlink_source, hardlink)
    symlink = tmp_path / "preexisting-symlink.sqlite"
    symlink.symlink_to(zero)
    directory = tmp_path / "preexisting-directory.sqlite"
    directory.mkdir()
    fifo = tmp_path / "preexisting-fifo.sqlite"
    os.mkfifo(fifo)
    before = {
        zero: zero.read_bytes(),
        empty_sqlite: empty_sqlite.read_bytes(),
        malformed: malformed.read_bytes(),
        hardlink: hardlink.read_bytes(),
    }

    # Act and assert: every existing namespace entry gets one stable rejection;
    # no file is opened writable, initialized, truncated, or followed.
    for target in (
        zero,
        empty_sqlite,
        malformed,
        hardlink,
        symlink,
        directory,
        fifo,
    ):
        with pytest.raises(FileExistsError, match="already exists"):
            GlobalEconomicAuthorityJournalV1.create(target, active)
    assert {path: path.read_bytes() for path in before} == before
    assert stat.S_ISFIFO(fifo.lstat().st_mode)


def test_authority_open_rejects_alias_and_mode_mismatch(tmp_path: Path) -> None:
    # Arrange: one valid store gains a hardlink alias, then a second valid store
    # receives a broader mode than the exact private-store contract.
    active = _head()
    linked = tmp_path / "linked-authority.sqlite"
    journal = GlobalEconomicAuthorityJournalV1.create(linked, active)
    journal.close()
    os.link(linked, tmp_path / "linked-authority-alias.sqlite")
    broad = tmp_path / "broad-mode-authority.sqlite"
    broad_journal = GlobalEconomicAuthorityJournalV1.create(broad, active)
    broad_journal.close()
    broad.chmod(0o640)

    # Act and assert: aliases and mode drift cannot become authority handles.
    with pytest.raises(PermissionError, match="exactly one filesystem link"):
        GlobalEconomicAuthorityJournalV1.open(linked)
    with pytest.raises(PermissionError, match="mode must be exactly 0600"):
        GlobalEconomicAuthorityJournalV1.open(broad)


def test_authority_crash_left_bootstrap_candidate_fails_closed(
    tmp_path: Path,
) -> None:
    # Arrange: a prior failed installer left the reserved private candidate.
    candidate = tmp_path / ".global-economic-authority-bootstrap-v1.sqlite"
    candidate.write_bytes(b"crash-left")
    target = tmp_path / "authority-after-crash.sqlite"

    # Act and assert: recovery never deletes or adopts an unverified candidate.
    with pytest.raises(RuntimeError, match="crash-left bootstrap candidate"):
        GlobalEconomicAuthorityJournalV1.create(target, _head())
    assert not target.exists()
    assert candidate.read_bytes() == b"crash-left"


def test_historical_retry_after_a_later_generation_is_a_stale_noop(
    tmp_path: Path,
) -> None:
    # Arrange: two profile migrations have already advanced the authority tip.
    path = tmp_path / "historical-retry.sqlite"
    active = _head()
    journal = GlobalEconomicAuthorityJournalV1.create(path, active)
    first = replace(
        active,
        generation=1,
        activation_id=_root(20),
        profile_root=_root(21),
        writer_epoch=active.writer_epoch + 1,
    )
    second = replace(
        first,
        generation=2,
        activation_id=_root(22),
        profile_root=_root(23),
        writer_epoch=first.writer_epoch + 1,
    )
    assert journal._commit_successor_for_unmounted_control_plane_v1(
        first,
        journal._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    ).status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    assert journal._commit_successor_for_unmounted_control_plane_v1(
        second,
        journal._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    ).status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED

    # Act: a lost acknowledgement for the older generation is retried.
    retry = journal._commit_successor_for_unmounted_control_plane_v1(
        first,
        journal._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )

    # Assert: historical presence never masquerades as current authority.
    assert retry.status is GlobalEconomicAuthorityCommitStatusV1.STALE_HEAD
    assert retry.head == second
    assert retry.committed_authority is None
    journal.close()


def test_active_rotation_reserves_capacity_for_emergency_revocation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: a three-row test budget permits genesis, one rotation, and revoke.
    monkeypatch.setattr(authority_journal_module, "_MAX_AUTHORITY_GENERATIONS_V1", 3)
    path = tmp_path / "revocation-reserve.sqlite"
    active = _head()
    journal = GlobalEconomicAuthorityJournalV1.create(path, active)
    rotated = replace(
        active,
        generation=1,
        activation_id=_root(30),
        profile_root=_root(31),
        writer_epoch=active.writer_epoch + 1,
    )
    accepted = journal._commit_successor_for_unmounted_control_plane_v1(
        rotated,
        journal._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )
    would_exhaust = replace(
        rotated,
        generation=2,
        activation_id=_root(32),
        profile_root=_root(33),
        writer_epoch=rotated.writer_epoch + 1,
    )

    # Act: another active rotation is denied, while revocation consumes reserve.
    denied = journal._commit_successor_for_unmounted_control_plane_v1(
        would_exhaust,
        journal._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )
    revoked = journal._commit_successor_for_unmounted_control_plane_v1(
        rotated.revoked_successor(),
        journal._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )

    # Assert: capacity pressure cannot strand an active unrevokable authority.
    assert accepted.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    assert denied.status is GlobalEconomicAuthorityCommitStatusV1.CAPACITY_EXCEEDED
    assert revoked.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    assert journal.head.status is GlobalEconomicAuthorityStatusV1.REVOKED
    journal.close()


def test_open_checks_history_byte_budget_before_decoding_rows(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: a row exceeds a narrowed aggregate byte budget by one byte.
    path = tmp_path / "authority-byte-prequery.sqlite"
    active = _head()
    journal = GlobalEconomicAuthorityJournalV1.create(path, active)
    journal.close()
    hostile = active.canonical_bytes + b"x"
    with sqlite3.connect(path) as connection:
        connection.execute(
            "UPDATE authority_history SET head_bytes = ?",
            (hostile,),
        )
    monkeypatch.setattr(
        authority_journal_module,
        "_MAX_AUTHORITY_STORE_BYTES_V1",
        len(active.canonical_bytes),
    )

    # Act and assert: bounded aggregate rejection precedes row decoding.
    with pytest.raises(ValueError, match="history exceeds byte capacity"):
        GlobalEconomicAuthorityJournalV1.open(path)


def test_competing_authority_successors_make_the_loser_a_stale_noop(
    tmp_path: Path,
) -> None:
    # Arrange: two operators snapshot the same active authority generation.
    path = tmp_path / "authority-race.sqlite"
    active = _head()
    first = GlobalEconomicAuthorityJournalV1.create(path, active)
    second = GlobalEconomicAuthorityJournalV1.open(path)
    first_token = first._acquire_cas_head_token_for_unmounted_control_plane_v1()
    second_token = second._acquire_cas_head_token_for_unmounted_control_plane_v1()
    revoked = active.revoked_successor()
    rotated = replace(
        active,
        generation=1,
        activation_id=_root(12),
        profile_root=_root(13),
        writer_epoch=active.writer_epoch + 1,
        verifier_registry_root=_root(8),
        verifier_release_id=_root(9),
        verifier_binding_root=_root(10),
        root_image_id=_root(11),
    )

    # Act: the profile migration wins before the revocation reaches CAS.
    winner = first._commit_successor_for_unmounted_control_plane_v1(
        rotated,
        first_token,
    )
    loser = second._commit_successor_for_unmounted_control_plane_v1(
        revoked,
        second_token,
    )

    # Assert: the stale branch publishes no second authority generation.
    assert winner.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    assert loser.status is GlobalEconomicAuthorityCommitStatusV1.STALE_HEAD
    assert first.head == second.head == rotated
    first.close()
    second.close()


def test_authority_open_rejects_an_unregistered_sidecar_table(
    tmp_path: Path,
) -> None:
    # Arrange: Mallory adds an unowned table to an otherwise valid authority DB.
    path = tmp_path / "authority-sidecar.sqlite"
    journal = GlobalEconomicAuthorityJournalV1.create(path, _head())
    journal.close()
    with sqlite3.connect(path) as connection:
        connection.execute("CREATE TABLE bypass(value TEXT) STRICT")

    # Act and assert: exact schema validation fails before a writable reopen.
    with pytest.raises(RuntimeError, match="exact schema mismatch"):
        GlobalEconomicAuthorityJournalV1.open(path)


def test_attached_epoch_transaction_serializes_authority_revocation(
    tmp_path: Path,
) -> None:
    # Arrange: an epoch connection begins its publication transaction with the
    # shared authority DB attached, while governance holds a valid successor.
    authority_path = tmp_path / "authority-linearization.sqlite"
    authority = GlobalEconomicAuthorityJournalV1.create(authority_path, _head())
    token = authority._acquire_cas_head_token_for_unmounted_control_plane_v1()
    revoked = authority.head.revoked_successor()
    epoch_path = tmp_path / "epoch-linearization.sqlite"
    blocker = sqlite3.connect(
        epoch_path,
        timeout=5.0,
        isolation_level=None,
        check_same_thread=False,
    )
    blocker.execute("PRAGMA journal_mode = DELETE")
    blocker.execute("PRAGMA synchronous = FULL")
    _attach_authority_store_v1(blocker, authority_path, immutable=False)
    blocker.execute("BEGIN IMMEDIATE")
    authority._connection.execute("PRAGMA busy_timeout = 0")

    # Act: revocation fails immediately while publication owns the attached
    # write transaction, then succeeds after that interval ends.
    with pytest.raises(sqlite3.OperationalError, match="locked"):
        authority._commit_successor_for_unmounted_control_plane_v1(
            revoked,
            token,
        )
    blocker.execute("COMMIT")
    outcome = authority._commit_successor_for_unmounted_control_plane_v1(
        revoked,
        authority._acquire_cas_head_token_for_unmounted_control_plane_v1(),
    )

    # Assert: authority rotation serializes after the epoch transaction.
    assert outcome.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    assert authority.head == revoked
    blocker.close()
    authority.close()


def test_journal_exposes_no_public_authority_mutation_method(tmp_path: Path) -> None:
    # Arrange: one unmounted reference journal exists.
    journal = GlobalEconomicAuthorityJournalV1.create(
        tmp_path / "private-control-plane.sqlite",
        _head(),
    )

    # Act and assert: ordinary callers receive no public successor mutation API.
    assert not hasattr(journal, "commit_successor")
    assert not hasattr(journal, "acquire_cas_head_token")
    journal.close()


def test_authority_cas_tokens_are_bounded_and_single_use(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange: shrink the outstanding-token budget to one for exact BVA.
    monkeypatch.setattr(
        authority_journal_module,
        "_MAX_OUTSTANDING_AUTHORITY_CAS_TOKENS_V1",
        1,
    )
    journal = GlobalEconomicAuthorityJournalV1.create(
        tmp_path / "bounded-cas-tokens.sqlite",
        _head(),
    )
    token = journal._acquire_cas_head_token_for_unmounted_control_plane_v1()

    # Act and assert: one-over rejects, then consuming the token frees capacity.
    with pytest.raises(RuntimeError, match="token capacity exceeded"):
        journal._acquire_cas_head_token_for_unmounted_control_plane_v1()
    outcome = journal._commit_successor_for_unmounted_control_plane_v1(
        journal.head.revoked_successor(),
        token,
    )
    assert outcome.status is GlobalEconomicAuthorityCommitStatusV1.COMMITTED
    journal._acquire_cas_head_token_for_unmounted_control_plane_v1()
    journal.close()
