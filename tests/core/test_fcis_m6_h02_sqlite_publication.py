"""Focused H02 SQLite publication tests."""

from __future__ import annotations

import sqlite3
from dataclasses import replace
from typing import Final, cast

import pytest

from experiments.fcis_m6_d08_combined_anf_check import build_instance
from experiments.fcis_m6_h02_sqlite_publication import (
    ANFPublicationWitnessV1,
    H02CodeV1,
    H02CommitV1,
    H02Error,
    H02RejectV1,
    SQLitePublicationRequestV1,
    create_database,
    publish_atom,
    read_state,
)
from src.core import fcis_durable_retraction as dra
from src.core.fcis_m6_d08_combined_anf import (
    D08CombinedANFAcceptV1,
    D08CombinedANFInstanceV1,
    verify_combined_anf_v1,
)

_TABLES: Final = (
    "publication_atoms",
    "publication_evidence",
    "publication_nullifiers",
    "publication_outbox",
    "anf_publications",
)


def _prepare() -> tuple[
    sqlite3.Connection,
    D08CombinedANFInstanceV1,
    ANFPublicationWitnessV1,
    SQLitePublicationRequestV1,
]:
    instance = build_instance()
    verified = verify_combined_anf_v1(instance)
    if type(verified) is not D08CombinedANFAcceptV1:
        raise AssertionError(f"D08 fixture was not accepted: {verified!r}")
    witness = ANFPublicationWitnessV1(instance, verified)
    connection = create_database(instance.pre_snapshot)
    pre_state = read_state(connection)
    request = SQLitePublicationRequestV1(
        atom=instance.publication_atom,
        anf_witness=witness,
        expected_snapshot_root=pre_state.snapshot.snapshot_root,
        expected_publication_root=pre_state.publication_root,
        expected_state_root=pre_state.snapshot.current_state_root,
        expected_authority_epoch=pre_state.snapshot.authority_epochs[-1].epoch_index,
        expected_authority_root=pre_state.snapshot.authority_epochs[-1].root,
    )
    return connection, instance, witness, request


def _assert_rejected(result: object, code: H02CodeV1) -> None:
    if type(result) is not H02RejectV1:
        raise AssertionError(f"expected H02 rejection, got {result!r}")
    assert cast(H02RejectV1, result).code is code


def test_one_transaction_publishes_complete_post() -> None:
    connection, instance, witness, request = _prepare()
    pre_state = read_state(connection)

    result = publish_atom(connection, request)

    assert type(result) is H02CommitV1
    assert result.post_snapshot == instance.post_snapshot
    assert result.anf_root == witness.anf_root
    post_state = read_state(connection)
    assert post_state.snapshot == instance.post_snapshot
    assert len(post_state.anf_rows) == 1
    assert post_state.anf_rows[0].commit_id == instance.publication_atom.commit_id
    assert post_state.anf_rows[0].atom_root == instance.publication_atom.atom_root
    assert post_state.anf_rows[0].anf_root == witness.anf_root
    assert post_state.publication_root == result.publication_root
    assert pre_state.snapshot.current_state_root != post_state.snapshot.current_state_root
    assert pre_state.publication_root != post_state.publication_root

    for table, expected in (
        ("snapshot_meta", 1),
        ("authority_epochs", 1),
        ("publication_atoms", 1),
        ("publication_evidence", 7),
        ("publication_nullifiers", 1),
        ("publication_outbox", len(instance.publication_atom.outbox)),
        ("anf_publications", 1),
    ):
        actual = connection.execute(f"SELECT COUNT(*) FROM {table}").fetchone()
        assert actual is not None
        assert actual[0] == expected


def test_stale_snapshot_cas_is_a_no_op() -> None:
    connection, _, _, request = _prepare()
    before = read_state(connection)
    stale = replace(request, expected_snapshot_root=dra.tagged_digest("stale-snapshot"))

    result = publish_atom(connection, stale)

    _assert_rejected(result, H02CodeV1.STALE_SNAPSHOT_CAS)
    assert read_state(connection) == before


def test_stale_state_cas_is_a_no_op() -> None:
    connection, _, _, request = _prepare()
    before = read_state(connection)
    stale = replace(request, expected_state_root=dra.tagged_digest("stale-state"))

    result = publish_atom(connection, stale)

    _assert_rejected(result, H02CodeV1.STALE_STATE_CAS)
    assert read_state(connection) == before


def test_stale_authority_cas_is_a_no_op() -> None:
    connection, _, _, request = _prepare()
    before = read_state(connection)
    stale = replace(request, expected_authority_root=dra.tagged_digest("stale-authority"))

    result = publish_atom(connection, stale)

    _assert_rejected(result, H02CodeV1.STALE_AUTHORITY_CAS)
    assert read_state(connection) == before


def test_sql_abort_after_partial_insert_rolls_back_every_row() -> None:
    connection, _, _, request = _prepare()
    before = read_state(connection)
    connection.execute(
        """
        CREATE TRIGGER force_h02_abort
        AFTER INSERT ON publication_evidence
        BEGIN
            SELECT RAISE(ABORT, 'forced H02 abort');
        END
        """
    )

    result = publish_atom(connection, request)

    _assert_rejected(result, H02CodeV1.SQL_ROLLBACK)
    assert read_state(connection) == before
    for table in _TABLES:
        count = connection.execute(f"SELECT COUNT(*) FROM {table}").fetchone()
        assert count is not None
        assert count[0] == 0


def test_foreign_verifier_acceptance_cannot_form_an_anf_witness() -> None:
    instance = build_instance()
    forged = object.__new__(D08CombinedANFAcceptV1)
    object.__setattr__(forged, "anf_root", "0x" + ("f" * 64))

    with pytest.raises(H02Error, match="verifier result"):
        ANFPublicationWitnessV1(instance, forged)


def test_atom_history_requires_an_f_row_when_seed_has_atoms() -> None:
    instance = build_instance()
    with pytest.raises(H02Error, match="ANF row cardinality"):
        create_database(instance.post_snapshot)


def test_request_rejects_crossed_atom_and_verifier_witness() -> None:
    instance = build_instance()
    verified = verify_combined_anf_v1(instance)
    if type(verified) is not D08CombinedANFAcceptV1:
        raise AssertionError("D08 fixture was unexpectedly rejected")
    witness = ANFPublicationWitnessV1(instance, verified)
    with pytest.raises(H02Error, match="crossed"):
        SQLitePublicationRequestV1(
            atom=replace(
                instance.publication_atom,
                commit_id=dra.tagged_digest("foreign-commit"),
            ),
            anf_witness=witness,
            expected_snapshot_root=instance.pre_snapshot.snapshot_root,
            expected_publication_root=dra.tagged_digest("unused"),
            expected_state_root=instance.pre_snapshot.current_state_root,
            expected_authority_epoch=instance.pre_snapshot.authority_epochs[-1].epoch_index,
            expected_authority_root=instance.pre_snapshot.authority_epochs[-1].root,
        )
