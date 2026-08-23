"""Canonical, transition, and CAS evidence for the shared authority head."""

from __future__ import annotations

import sqlite3
from dataclasses import replace
from pathlib import Path

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
