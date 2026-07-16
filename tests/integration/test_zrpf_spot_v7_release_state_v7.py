from __future__ import annotations

import copy
import pickle
import sqlite3
import threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import cast

import pytest

from src.integration import _zrpf_spot_v7_release_state_engine_v7 as engine_v7
from src.integration import zrpf_spot_v7_authenticated_release_selection_v1 as select_auth
from tests import test_zrpf_spot_v7_authenticated_release_state_store_v3 as v3_fx
from tests.test_zrpf_spot_v7_release_store_cutover_v1 import (
    _cutover_selected_store,
)
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools import zrpf_spot_v7_highest_observed_release_event_watermark_v1 as watermark_v1
from tools import zrpf_spot_v7_release_state_checkpoint_v1 as checkpoint_v1
from tools import zrpf_spot_v7_release_store_cutover_v1 as cutover_v1


def _open(
    path: Path,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> sqlite3.Connection:
    return cutover_v1.open_unified_release_store_v7_for_maintenance_v1(
        path,
        identity=identity,
    )


def _open_cross_thread(
    path: Path,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
) -> sqlite3.Connection:
    connection = sqlite3.connect(
        path,
        isolation_level=None,
        timeout=30,
        check_same_thread=False,
    )
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys = ON")
    connection.execute("PRAGMA trusted_schema = OFF")
    connection.execute("PRAGMA busy_timeout = 30000")
    connection.execute("BEGIN IMMEDIATE")
    engine_v7._validate_complete_release_history_locked_v7(
        connection,
        identity=identity,
    )
    connection.rollback()
    return connection


def _watermark_for_locked_v7(
    connection: sqlite3.Connection,
    identity: store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3,
    *,
    position: int,
    commitment: str,
    parent_commitment: str,
    backend_id: str = "test-finalized-release-log",
) -> bytes:
    cursors = engine_v7._cursor_history_v7(connection, identity)
    checkpoint_bytes = engine_v7._head_checkpoint_bytes(identity, cursors)
    checkpoint = checkpoint_v1.parse_exact_spot_v7_release_state_checkpoint_v1(checkpoint_bytes)
    return watermark_v1.build_spot_v7_highest_observed_release_event_watermark_v1(
        application_id=checkpoint.application_id,
        chain_id=checkpoint.chain_id,
        domain_id=checkpoint.domain_id,
        release_profile=checkpoint.release_profile,
        store_identity_hash=checkpoint.store_identity_hash,
        external_backend_id=backend_id,
        external_position=position,
        external_backend_commitment=commitment,
        external_parent_commitment=parent_commitment,
        latest_finalized_checkpoint_hash=checkpoint.release_checkpoint_hash,
        latest_finalized_database_revision=checkpoint.database_revision,
        highest_observed_checkpoint_hash=checkpoint.release_checkpoint_hash,
        highest_observed_database_revision=checkpoint.database_revision,
        highest_observed_release_state_root=checkpoint.release_state_root,
        highest_observed_event_kind=watermark_v1.ObservedReleaseEventKindV1.SELECT,
        highest_observed_select_input_id=checkpoint.current_select_input_id,
        highest_observed_revocation_record_id=None,
    )


def test_current_release_projection_is_transaction_bound_and_authority_false(
    tmp_path: Path,
) -> None:
    store, _selection, _revocation, destination, _watermark = _cutover_selected_store(tmp_path)
    connection = _open(destination, store.identity)
    try:
        connection.execute("BEGIN IMMEDIATE")
        release = engine_v7._current_release_for_atomic_join_locked_v7(
            connection,
            identity=store.identity,
        )
        assert release.database_revision == 1
        assert release.release_and_settlement_share_write_transaction is True
        assert release.external_monotonic_anchor_authenticated is False
        assert release.currentness_at_settlement_verified is False
        assert release.release_authority is False
        assert release.settlement_authority is False
        assert release.production_authority is False
        assert (
            engine_v7._require_current_release_still_locked_v7(
                connection,
                identity=store.identity,
                release=release,
            )
            is release
        )
        connection.rollback()
        transaction_still_open: bool = release.release_and_settlement_share_write_transaction
        assert not transaction_still_open
        with pytest.raises(engine_v7.SpotV7ReleaseStateEngineRejectV7, match="TRANSACTION_ENDED"):
            engine_v7._require_current_release_still_locked_v7(
                connection,
                identity=store.identity,
                release=release,
            )
        with pytest.raises(TypeError, match="verified locked construction"):
            type(release)()
        with pytest.raises(TypeError, match="immutable"):
            release._database_revision = 9
        with pytest.raises(TypeError, match="cannot be copied"):
            copy.copy(release)
        with pytest.raises(TypeError, match="cannot be deep-copied"):
            copy.deepcopy(release)
        with pytest.raises(TypeError, match="cannot be serialized"):
            pickle.dumps(release)
    finally:
        connection.close()


def test_native_selection_requires_new_observation_before_current_projection(
    tmp_path: Path,
) -> None:
    store, _selection, _revocation, destination, _watermark = _cutover_selected_store(tmp_path)
    connection = _open(destination, store.identity)
    try:
        connection.execute("BEGIN IMMEDIATE")
        initial = engine_v7._validate_complete_release_history_locked_v7(
            connection,
            identity=store.identity,
        )
        successor = v3_fx._successor_selection(initial, variant=17)
        advanced = engine_v7._apply_authenticated_release_event_locked_v7(
            connection,
            identity=store.identity,
            capability=successor,
        )
        assert advanced.database_revision == 2
        with pytest.raises(
            engine_v7.SpotV7ReleaseStateEngineRejectV7,
            match="RELEASE_OBSERVATION_STALE",
        ):
            engine_v7._current_release_for_atomic_join_locked_v7(
                connection,
                identity=store.identity,
            )
        exact_watermark = _watermark_for_locked_v7(
            connection,
            store.identity,
            position=2,
            commitment="ef" * 32,
            parent_commitment="ab" * 32,
        )
        engine_v7._record_authority_neutral_watermark_locked_v7(
            connection,
            identity=store.identity,
            exact_watermark_bytes=exact_watermark,
        )
        current = engine_v7._current_release_for_atomic_join_locked_v7(
            connection,
            identity=store.identity,
        )
        assert current.database_revision == 2
        assert current.current_candidate_id == successor.selected_candidate_id
        connection.commit()
    finally:
        connection.close()

    reopened = _open(destination, store.identity)
    try:
        reopened.execute("BEGIN IMMEDIATE")
        assert (
            engine_v7._validate_complete_release_history_locked_v7(
                reopened,
                identity=store.identity,
            ).database_revision
            == 2
        )
        reopened.rollback()
    finally:
        reopened.close()


def test_revocation_committed_first_prevents_settlement_projection(tmp_path: Path) -> None:
    store, _selection, revocation, destination, _watermark = _cutover_selected_store(tmp_path)
    revoke_connection = _open(destination, store.identity)
    try:
        revoke_connection.execute("BEGIN IMMEDIATE")
        revoked = engine_v7._apply_authenticated_release_event_locked_v7(
            revoke_connection,
            identity=store.identity,
            capability=revocation,
        )
        assert revoked.current_revoked is True
        revoke_connection.commit()
    finally:
        revoke_connection.close()

    settlement_connection = _open(destination, store.identity)
    try:
        settlement_connection.execute("BEGIN IMMEDIATE")
        with pytest.raises(
            engine_v7.SpotV7ReleaseStateEngineRejectV7,
            match="CURRENT_RELEASE_UNAVAILABLE",
        ):
            engine_v7._current_release_for_atomic_join_locked_v7(
                settlement_connection,
                identity=store.identity,
            )
        settlement_connection.rollback()
    finally:
        settlement_connection.close()


def test_settlement_lock_serializes_revocation_after_currentness_check(
    tmp_path: Path,
) -> None:
    store, _selection, revocation, destination, _watermark = _cutover_selected_store(tmp_path)
    first = _open(destination, store.identity)
    second = _open_cross_thread(destination, store.identity)
    barrier = threading.Barrier(2)
    revocation_started = threading.Event()

    def revoke() -> int:
        try:
            barrier.wait(timeout=5)
            revocation_started.set()
            second.execute("BEGIN IMMEDIATE")
            cursor = engine_v7._apply_authenticated_release_event_locked_v7(
                second,
                identity=store.identity,
                capability=revocation,
            )
            second.commit()
            return cursor.database_revision
        finally:
            second.close()

    try:
        first.execute("BEGIN IMMEDIATE")
        release = engine_v7._current_release_for_atomic_join_locked_v7(
            first,
            identity=store.identity,
        )
        with ThreadPoolExecutor(max_workers=1) as executor:
            future = executor.submit(revoke)
            barrier.wait(timeout=5)
            assert revocation_started.wait(timeout=5)
            assert not future.done()
            engine_v7._require_current_release_still_locked_v7(
                first,
                identity=store.identity,
                release=release,
            )
            first.commit()
            assert future.result(timeout=30) == 2
    finally:
        if first.in_transaction:
            first.rollback()
        first.close()


def test_deferred_transaction_is_upgraded_before_current_release_projection(
    tmp_path: Path,
) -> None:
    store, _selection, revocation, destination, _watermark = _cutover_selected_store(tmp_path)
    first = _open(destination, store.identity)
    second = _open_cross_thread(destination, store.identity)
    revocation_started = threading.Event()

    def revoke() -> int:
        try:
            revocation_started.set()
            second.execute("BEGIN IMMEDIATE")
            cursor = engine_v7._apply_authenticated_release_event_locked_v7(
                second,
                identity=store.identity,
                capability=revocation,
            )
            second.commit()
            return cursor.database_revision
        finally:
            second.close()

    try:
        first.execute("BEGIN")
        release = engine_v7._current_release_for_atomic_join_locked_v7(
            first,
            identity=store.identity,
        )
        with ThreadPoolExecutor(max_workers=1) as executor:
            future = executor.submit(revoke)
            assert revocation_started.wait(timeout=5)
            assert not future.done()
            engine_v7._require_current_release_still_locked_v7(
                first,
                identity=store.identity,
                release=release,
            )
            first.commit()
            assert future.result(timeout=30) == 2
    finally:
        if first.in_transaction:
            first.rollback()
        first.close()


@pytest.mark.parametrize(
    ("table", "column"),
    (
        ("spot_v7_release_state_v7", "release_authority"),
        ("spot_v7_release_cutover_v7", "settlement_authority"),
        ("spot_v7_release_events_v7", "production_authority"),
        ("spot_v7_release_observations_v7", "external_finality_authenticated"),
    ),
)
def test_authority_flag_tamper_rejects_reopen(
    tmp_path: Path,
    table: str,
    column: str,
) -> None:
    store, _selection, _revocation, destination, _watermark = _cutover_selected_store(tmp_path)
    with sqlite3.connect(destination) as connection:
        connection.execute("PRAGMA ignore_check_constraints = ON")
        connection.execute(f"UPDATE {table} SET {column} = 1")

    with pytest.raises(engine_v7.SpotV7ReleaseStateEngineRejectV7):
        _open(destination, store.identity)


def test_event_and_observation_tamper_reject_complete_replay(tmp_path: Path) -> None:
    event_store, _selection, _revocation, event_path, _watermark = _cutover_selected_store(
        tmp_path, destination_name="event.sqlite3"
    )
    with sqlite3.connect(event_path) as connection:
        connection.execute(
            "UPDATE spot_v7_release_events_v7 SET candidate_bytes = ?",
            (b"mutated",),
        )
    with pytest.raises(engine_v7.SpotV7ReleaseStateEngineRejectV7):
        _open(event_path, event_store.identity)

    observation_store, _selection, _revocation, observation_path, _watermark = (
        _cutover_selected_store(
            tmp_path,
            source_name="observation-source.sqlite3",
            destination_name="observation.sqlite3",
        )
    )
    with sqlite3.connect(observation_path) as connection:
        connection.execute("PRAGMA ignore_check_constraints = ON")
        connection.execute(
            "UPDATE spot_v7_release_observations_v7 SET exact_watermark_bytes = zeroblob(length(exact_watermark_bytes))"
        )
    with pytest.raises(engine_v7.SpotV7ReleaseStateEngineRejectV7):
        _open(observation_path, observation_store.identity)

    cutover_store, _selection, _revocation, cutover_path, _watermark = _cutover_selected_store(
        tmp_path,
        source_name="cutover-source.sqlite3",
        destination_name="cutover.sqlite3",
    )
    with sqlite3.connect(cutover_path) as connection:
        connection.execute(
            "UPDATE spot_v7_release_cutover_v7 SET external_anchor_commitment = ?",
            (bytes.fromhex("ff" * 32),),
        )
    with pytest.raises(engine_v7.SpotV7ReleaseStateEngineRejectV7):
        _open(cutover_path, cutover_store.identity)


def test_release_table_trigger_injection_rejects_reopen(tmp_path: Path) -> None:
    store, _selection, _revocation, destination, _watermark = _cutover_selected_store(tmp_path)
    with sqlite3.connect(destination) as connection:
        connection.execute(
            """
            CREATE TRIGGER attacker_release_update
            AFTER UPDATE ON spot_v7_release_state_v7
            BEGIN
                SELECT 1;
            END
            """
        )
    with pytest.raises(ValueError, match="unexpected triggers"):
        _open(destination, store.identity)


def test_nominal_or_wrong_kind_values_cannot_cross_release_boundary(tmp_path: Path) -> None:
    store, _selection, _revocation, destination, _watermark = _cutover_selected_store(tmp_path)
    connection = _open(destination, store.identity)
    try:
        connection.execute("BEGIN IMMEDIATE")
        before = engine_v7._validate_complete_release_history_locked_v7(
            connection,
            identity=store.identity,
        )
        for value in (True, {"verified": True}, b"release"):
            with pytest.raises(TypeError, match="authenticated"):
                engine_v7._apply_authenticated_release_event_locked_v7(
                    connection,
                    identity=store.identity,
                    capability=cast(
                        select_auth._AuthenticatedSpotV7ReleaseSelectionV1,
                        value,
                    ),
                )
        after = engine_v7._validate_complete_release_history_locked_v7(
            connection,
            identity=store.identity,
        )
        assert after == before
        connection.rollback()
    finally:
        connection.close()


def test_watermark_backend_switch_rejects_without_changing_history(tmp_path: Path) -> None:
    store, _selection, _revocation, destination, _watermark = _cutover_selected_store(tmp_path)
    connection = _open(destination, store.identity)
    try:
        connection.execute("BEGIN IMMEDIATE")
        before = engine_v7._validate_complete_release_history_locked_v7(
            connection,
            identity=store.identity,
        )
        switched = _watermark_for_locked_v7(
            connection,
            store.identity,
            position=2,
            commitment="de" * 32,
            parent_commitment="ab" * 32,
            backend_id="attacker-selected-release-log",
        )
        with pytest.raises(
            engine_v7.SpotV7ReleaseStateEngineRejectV7,
            match="EXTERNAL_BACKEND_CHANGED",
        ):
            engine_v7._record_authority_neutral_watermark_locked_v7(
                connection,
                identity=store.identity,
                exact_watermark_bytes=switched,
            )
        after = engine_v7._validate_complete_release_history_locked_v7(
            connection,
            identity=store.identity,
        )
        assert after == before
        connection.rollback()
    finally:
        connection.close()
