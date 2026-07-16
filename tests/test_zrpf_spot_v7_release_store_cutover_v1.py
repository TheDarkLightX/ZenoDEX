from __future__ import annotations

import copy
import os
import pickle
import shutil
import sqlite3
import threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pytest

from src.integration.zrpf_spot_v7_authenticated_release_revocation_v1 import (
    _AuthenticatedSpotV7ReleaseRevocationV1,
)
from src.integration.zrpf_spot_v7_authenticated_release_selection_v1 import (
    _AuthenticatedSpotV7ReleaseSelectionV1,
)
from tests import test_zrpf_spot_v7_authenticated_release_state_store_v3 as v3_fx
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools import zrpf_spot_v7_highest_observed_release_event_watermark_v1 as watermark_v1
from tools import zrpf_spot_v7_release_state_checkpoint_v1 as checkpoint_v1
from tools import zrpf_spot_v7_release_store_cutover_v1 as cutover_v1
from tools import zrpf_spot_v7_store_derived_release_checkpoint_v1 as derived_v1


def _watermark_for_store(
    store: store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3,
    *,
    external_position: int = 1,
    external_commitment: str = "ab" * 32,
    external_parent_commitment: str = "cd" * 32,
) -> bytes:
    derived = derived_v1.derive_store_release_state_checkpoint_v1(store)
    document = checkpoint_v1.parse_exact_spot_v7_release_state_checkpoint_v1(
        derived.canonical_bytes
    )
    if document.current_revocation_record_id is not None:
        kind = watermark_v1.ObservedReleaseEventKindV1.REVOKE
    elif document.database_revision == 0:
        kind = watermark_v1.ObservedReleaseEventKindV1.GENESIS
    else:
        kind = watermark_v1.ObservedReleaseEventKindV1.SELECT
    return watermark_v1.build_spot_v7_highest_observed_release_event_watermark_v1(
        application_id=document.application_id,
        chain_id=document.chain_id,
        domain_id=document.domain_id,
        release_profile=document.release_profile,
        store_identity_hash=document.store_identity_hash,
        external_backend_id="test-finalized-release-log",
        external_position=external_position,
        external_backend_commitment=external_commitment,
        external_parent_commitment=external_parent_commitment,
        latest_finalized_checkpoint_hash=document.release_checkpoint_hash,
        latest_finalized_database_revision=document.database_revision,
        highest_observed_checkpoint_hash=document.release_checkpoint_hash,
        highest_observed_database_revision=document.database_revision,
        highest_observed_release_state_root=document.release_state_root,
        highest_observed_event_kind=kind,
        highest_observed_select_input_id=document.current_select_input_id,
        highest_observed_revocation_record_id=document.current_revocation_record_id,
    )


def _selected_v3_store(
    tmp_path: Path,
    *,
    name: str = "release-source-v3.sqlite3",
) -> tuple[
    store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3,
    _AuthenticatedSpotV7ReleaseSelectionV1,
    _AuthenticatedSpotV7ReleaseRevocationV1,
]:
    os.chmod(tmp_path, 0o700)
    store, selection, revocation, _candidate = v3_fx._new_store(tmp_path, name=name)
    store.commit_selection(selection)
    return store, selection, revocation


def _cutover_selected_store(
    tmp_path: Path,
    *,
    source_name: str = "release-source-v3.sqlite3",
    destination_name: str = "unified-release-v7.sqlite3",
) -> tuple[
    store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3,
    _AuthenticatedSpotV7ReleaseSelectionV1,
    _AuthenticatedSpotV7ReleaseRevocationV1,
    Path,
    bytes,
]:
    store, selection, revocation = _selected_v3_store(tmp_path, name=source_name)
    watermark = _watermark_for_store(store)
    destination = (tmp_path / destination_name).resolve()
    cutover_v1.cutover_spot_v7_release_store_v1(
        store,
        destination_path=destination,
        exact_watermark_bytes=watermark,
    )
    return store, selection, revocation, destination, watermark


def test_cutover_replays_history_retires_source_and_keeps_authority_false(
    tmp_path: Path,
) -> None:
    store, _selection, _revocation, destination, _watermark = _cutover_selected_store(tmp_path)

    with pytest.raises(
        store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3,
        match="user_version mismatch",
    ):
        store.read_cursor()
    with sqlite3.connect(store.path) as source:
        assert int(source.execute("PRAGMA user_version").fetchone()[0]) == 307
    with sqlite3.connect(destination) as destination_connection:
        destination_connection.row_factory = sqlite3.Row
        state = destination_connection.execute(
            "SELECT * FROM spot_v7_release_state_v7 WHERE singleton = 1"
        ).fetchone()
        cutover = destination_connection.execute(
            "SELECT * FROM spot_v7_release_cutover_v7 WHERE singleton = 1"
        ).fetchone()
        assert state is not None and cutover is not None
        assert int(state["old_store_retired"]) == 1
        assert int(state["release_event_writer_active"]) == 1
        assert int(cutover["new_release_writer_active"]) == 1
        for field in (
            "external_monotonic_anchor_authenticated",
            "currentness_at_settlement_verified",
            "release_authority",
            "settlement_authority",
            "production_authority",
        ):
            assert int(state[field]) == 0


def test_cutover_result_is_private_immutable_and_nonserializable(tmp_path: Path) -> None:
    store, _selection, _revocation = _selected_v3_store(tmp_path)
    result = cutover_v1.cutover_spot_v7_release_store_v1(
        store,
        destination_path=(tmp_path / "v7.sqlite3").resolve(),
        exact_watermark_bytes=_watermark_for_store(store),
    )

    assert result.database_revision == 1
    assert result.old_store_retired is True
    assert result.new_release_writer_active is True
    assert result.external_monotonic_anchor_authenticated is False
    assert result.release_authority is False
    assert result.settlement_authority is False
    assert result.production_authority is False
    with pytest.raises(TypeError, match="module-private seal"):
        type(result)()
    with pytest.raises(TypeError, match="immutable"):
        result._database_revision = 9
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(result)
    with pytest.raises(TypeError, match="cannot be deep-copied"):
        copy.deepcopy(result)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(result)


def test_bad_watermark_rolls_back_retirement_and_removes_destination(tmp_path: Path) -> None:
    store, _selection, _revocation = _selected_v3_store(tmp_path)
    destination = (tmp_path / "v7.sqlite3").resolve()
    watermark = bytearray(_watermark_for_store(store))
    watermark[-2] ^= 1

    with pytest.raises(cutover_v1.SpotV7ReleaseStoreCutoverRejectV1):
        cutover_v1.cutover_spot_v7_release_store_v1(
            store,
            destination_path=destination,
            exact_watermark_bytes=bytes(watermark),
        )

    assert not destination.exists()
    assert store.read_cursor().database_revision == 1
    with sqlite3.connect(store.path) as source:
        assert int(source.execute("PRAGMA user_version").fetchone()[0]) == 3


def test_source_event_tamper_rejects_without_retirement(tmp_path: Path) -> None:
    store, selection, _revocation = _selected_v3_store(tmp_path)
    watermark = _watermark_for_store(store)
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            "UPDATE spot_v7_authenticated_release_state_events_v3 "
            "SET candidate_bytes = ? WHERE selector_input_id = ?",
            (b"mutated", selection.selector_input_id),
        )

    with pytest.raises(cutover_v1.SpotV7ReleaseStoreCutoverRejectV1):
        cutover_v1.cutover_spot_v7_release_store_v1(
            store,
            destination_path=(tmp_path / "v7.sqlite3").resolve(),
            exact_watermark_bytes=watermark,
        )
    with sqlite3.connect(store.path) as source:
        assert int(source.execute("PRAGMA user_version").fetchone()[0]) == 3


def test_injected_failure_before_commit_leaves_source_live_and_no_destination(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store, _selection, _revocation = _selected_v3_store(tmp_path)
    destination = (tmp_path / "v7.sqlite3").resolve()

    def fail_cutover(*_args: object, **_kwargs: object) -> object:
        raise ValueError("injected cutover failure")

    monkeypatch.setattr(
        cutover_v1.engine_v7,
        "_cutover_attached_v3_history_locked_v7",
        fail_cutover,
    )
    with pytest.raises(cutover_v1.SpotV7ReleaseStoreCutoverRejectV1):
        cutover_v1.cutover_spot_v7_release_store_v1(
            store,
            destination_path=destination,
            exact_watermark_bytes=_watermark_for_store(store),
        )
    assert not destination.exists()
    assert store.read_cursor().database_revision == 1


def test_older_valid_snapshot_cannot_match_newer_watermark(tmp_path: Path) -> None:
    store, selection, _revocation = _selected_v3_store(tmp_path)
    old_snapshot = (tmp_path / "old.sqlite3").resolve()
    shutil.copyfile(store.path, old_snapshot)
    os.chmod(old_snapshot, 0o600)
    successor = v3_fx._successor_selection(store.read_cursor(), variant=1)
    store.commit_selection(successor)
    newest_watermark = _watermark_for_store(store)
    os.replace(old_snapshot, store.path)
    rolled_back = store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
        store.path,
        identity=store.identity,
    )
    assert rolled_back.read_cursor().current_candidate_id == selection.selected_candidate_id

    with pytest.raises(
        cutover_v1.SpotV7ReleaseStoreCutoverRejectV1,
        match="WATERMARK_REJECTED",
    ):
        cutover_v1.cutover_spot_v7_release_store_v1(
            rolled_back,
            destination_path=(tmp_path / "v7.sqlite3").resolve(),
            exact_watermark_bytes=newest_watermark,
        )


def test_two_concurrent_cutovers_retire_source_once(tmp_path: Path) -> None:
    store, _selection, _revocation = _selected_v3_store(tmp_path)
    watermark = _watermark_for_store(store)
    barrier = threading.Barrier(2)

    def run(index: int) -> object:
        barrier.wait(timeout=5)
        try:
            return cutover_v1.cutover_spot_v7_release_store_v1(
                store,
                destination_path=(tmp_path / f"v7-{index}.sqlite3").resolve(),
                exact_watermark_bytes=watermark,
                busy_timeout_ms=30_000,
            )
        except cutover_v1.SpotV7ReleaseStoreCutoverRejectV1 as exc:
            return exc

    with ThreadPoolExecutor(max_workers=2) as executor:
        results = [
            future.result(timeout=45)
            for future in (executor.submit(run, 1), executor.submit(run, 2))
        ]

    assert sum(not isinstance(result, Exception) for result in results) == 1
    assert (
        sum(isinstance(result, cutover_v1.SpotV7ReleaseStoreCutoverRejectV1) for result in results)
        == 1
    )
    with sqlite3.connect(store.path) as source:
        assert int(source.execute("PRAGMA user_version").fetchone()[0]) == 307


def test_path_and_existing_destination_checks_fail_closed(tmp_path: Path) -> None:
    store, _selection, _revocation = _selected_v3_store(tmp_path)
    watermark = _watermark_for_store(store)
    existing = (tmp_path / "existing.sqlite3").resolve()
    existing.write_bytes(b"occupied")
    os.chmod(existing, 0o600)
    with pytest.raises(
        cutover_v1.SpotV7ReleaseStoreCutoverRejectV1,
        match="DESTINATION_EXISTS",
    ):
        cutover_v1.cutover_spot_v7_release_store_v1(
            store,
            destination_path=existing,
            exact_watermark_bytes=watermark,
        )

    alias = (tmp_path / "source-alias.sqlite3").resolve()
    os.link(store.path, alias)
    with pytest.raises(
        cutover_v1.SpotV7ReleaseStoreCutoverRejectV1,
        match="one regular file with one link",
    ):
        cutover_v1.cutover_spot_v7_release_store_v1(
            store,
            destination_path=(tmp_path / "v7.sqlite3").resolve(),
            exact_watermark_bytes=watermark,
        )
    alias.unlink()
