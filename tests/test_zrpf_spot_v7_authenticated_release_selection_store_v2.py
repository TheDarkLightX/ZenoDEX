from __future__ import annotations

import copy
import json
import os
import pickle
import shutil
import sqlite3
import threading
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

import pytest

from src.integration._zrpf_spot_v7_release_selection_envelope_v1 import (
    SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
    spot_v7_release_selection_envelope_payload_hash_v1,
)
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
from src.integration.zrpf_spot_v7_authenticated_release_selection_v1 import (
    SpotV7ReleaseSelectionExternalTrustPinsV1,
    _AuthenticatedSpotV7ReleaseSelectionV1,
    authenticate_spot_v7_release_selection_v1,
    build_spot_v7_release_selection_envelope_v1,
)
from tests.integration.test_zrpf_spot_v7_authenticated_release_selection_v1 import (
    PRIVATE_KEY_0,
    PRIVATE_KEY_1,
    REGISTRY_ACTIVATION_EPOCH,
    REGISTRY_REVISION,
    _registry,
)
from tests.test_zrpf_spot_v7_governed_release_selection_store_v1 import (
    _candidate_body,
    _candidate_lineage,
    _checked_candidate,
    _position_bytes,
    _selector_bytes,
)
from tools import zrpf_spot_v7_authenticated_release_selection_store_v2 as store_v2
from tools import zrpf_spot_v7_governed_release_selection_store_v1 as store_v1
from tools import zrpf_spot_v7_governed_release_selector_input_v1 as selector_v1
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate_v1

EVALUATION_EPOCH = 0x0102_0304_0506
REVOCATION_REGISTRY_ROOT = _position_bytes(180)
EXTERNAL_TRUST_PIN_IDENTITY = _position_bytes(250)


def _candidate_with_static_policies(
    *,
    revision: int,
    parent_candidate_id: bytes | None,
    variant: int,
) -> candidate_v1.SpotV7ReleaseCandidateManifestV1:
    if variant == 0:
        return _checked_candidate(
            revision=revision,
            parent_candidate_id=parent_candidate_id,
            variant=0,
        )
    baseline = _candidate_body(
        revision=1,
        parent_candidate_id=None,
        variant=0,
    )
    body = _candidate_body(
        revision=revision,
        parent_candidate_id=parent_candidate_id,
        variant=variant,
    )
    baseline_inventory = {
        row["role"]: row for row in cast(list[dict[str, Any]], baseline["evidence_inventory"])
    }
    inventory = cast(list[dict[str, Any]], body["evidence_inventory"])
    for index, row in enumerate(inventory):
        if row["role"] in {"rollback_policy", "revocation_policy"}:
            inventory[index] = dict(baseline_inventory[row["role"]])
    digest_by_role = {row["role"]: row["bound_identity"] for row in inventory}
    lineage = cast(dict[str, Any], body["lineage"])
    lineage["rollback_policy_root"] = digest_by_role["rollback_policy"]
    lineage["revocation_policy_root"] = digest_by_role["revocation_policy"]
    raw = candidate_v1.recompose_spot_v7_release_candidate_manifest_v1(body)
    parsed = candidate_v1.parse_exact_spot_v7_release_candidate_manifest_v1(raw)
    return candidate_v1.check_exact_spot_v7_release_candidate_manifest_v1(
        raw,
        expected_candidate_id=parsed.candidate_id,
    )


def _v1_cursor(
    cursor: store_v2.SpotV7AuthenticatedReleaseSelectionCursorV2,
) -> store_v1.SpotV7ReleaseSelectionCursorV1:
    return store_v1.SpotV7ReleaseSelectionCursorV1(
        database_revision=cursor.database_revision,
        state_root=cursor.state_root,
        last_evaluation_epoch=cursor.last_evaluation_epoch,
        current_candidate_id=cursor.current_candidate_id,
        current_candidate_sha256=cursor.current_candidate_sha256,
        current_release_revision=cursor.current_release_revision,
        current_select_input_id=cursor.current_selector_input_id,
        current_scope_id=None,
        current_revoked=False,
        current_revocation_record_id=None,
    )


def _pins(
    *,
    candidate: candidate_v1.SpotV7ReleaseCandidateManifestV1,
    cursor: store_v2.SpotV7AuthenticatedReleaseSelectionCursorV2,
    evaluation_epoch: int,
    registry: dict[str, Any],
) -> SpotV7ReleaseSelectionExternalTrustPinsV1:
    document = cast(dict[str, Any], json.loads(candidate.canonical_bytes))
    scope = cast(dict[str, Any], document["scope"])
    lineage = _candidate_lineage(candidate)
    return SpotV7ReleaseSelectionExternalTrustPinsV1(
        application_id=cast(str, scope["application_id"]),
        chain_id=cast(str, scope["chain_id"]),
        domain_id=cast(str, scope["domain_id"]),
        release_profile=cast(str, scope["release_profile"]),
        trusted_evaluation_epoch=evaluation_epoch,
        expected_database_revision=cursor.database_revision,
        expected_current_candidate_id=cursor.current_candidate_id,
        expected_current_select_input_id=cursor.current_selector_input_id,
        minimum_target_release_revision=candidate.release_revision,
        rollback_policy_root=bytes.fromhex(cast(str, lineage["rollback_policy_root"])),
        revocation_policy_root=bytes.fromhex(cast(str, lineage["revocation_policy_root"])),
        revocation_registry_root=REVOCATION_REGISTRY_ROOT,
        signer_registry_id=cast(str, registry["registry_id"]),
        expected_signer_registry_hash=cast(str, registry["registry_hash"]),
        signer_registry_revision=REGISTRY_REVISION,
        signer_registry_activation_epoch=REGISTRY_ACTIVATION_EPOCH,
        signer_registry_revocation_epoch=None,
        expected_quorum_threshold=cast(int, registry["threshold"]),
    )


def _authenticated_selection(
    *,
    cursor: store_v2.SpotV7AuthenticatedReleaseSelectionCursorV2,
    revision: int,
    parent_candidate_id: bytes | None,
    variant: int,
    evaluation_epoch: int,
    registry_override: dict[str, Any] | None = None,
) -> tuple[
    _AuthenticatedSpotV7ReleaseSelectionV1,
    candidate_v1.SpotV7ReleaseCandidateManifestV1,
    SpotV7ReleaseSelectionExternalTrustPinsV1,
]:
    candidate = _candidate_with_static_policies(
        revision=revision,
        parent_candidate_id=parent_candidate_id,
        variant=variant,
    )
    selector_bytes, selector_id = _selector_bytes(
        operation=selector_v1.SelectorOperationV1.SELECT,
        candidate=candidate,
        cursor=_v1_cursor(cursor),
        evaluation_epoch=evaluation_epoch,
        nonce_index=200 + variant,
        revocation_registry_root=REVOCATION_REGISTRY_ROOT,
    )
    registry = _registry() if registry_override is None else registry_override
    pins = _pins(
        candidate=candidate,
        cursor=cursor,
        evaluation_epoch=evaluation_epoch,
        registry=registry,
    )
    envelope = build_spot_v7_release_selection_envelope_v1(
        selector_input_bytes=selector_bytes,
        expected_selector_input_id=selector_id,
        candidate_bytes=candidate.canonical_bytes,
        external_trust_pins=pins,
        trusted_signer_registry=registry,
    )
    payload_hash = spot_v7_release_selection_envelope_payload_hash_v1(envelope)
    signatures = (
        build_bls_signed_artifact_envelope_v0(
            payload_kind=SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id="release-selection-signer-0",
            key_id="release-selection-key-0",
            private_key_hex=PRIVATE_KEY_0,
        ),
        build_bls_signed_artifact_envelope_v0(
            payload_kind=SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id="release-selection-signer-1",
            key_id="release-selection-key-1",
            private_key_hex=PRIVATE_KEY_1,
        ),
    )
    authenticated = authenticate_spot_v7_release_selection_v1(
        envelope,
        selector_input_bytes=selector_bytes,
        expected_selector_input_id=selector_id,
        candidate_bytes=candidate.canonical_bytes,
        external_trust_pins=pins,
        trusted_signer_registry=registry,
        signature_envelopes=signatures,
    )
    return authenticated, candidate, pins


def _identity(
    pins: SpotV7ReleaseSelectionExternalTrustPinsV1,
) -> store_v2.SpotV7AuthenticatedReleaseSelectionStoreIdentityV2:
    return store_v2.SpotV7AuthenticatedReleaseSelectionStoreIdentityV2(
        application_id=pins.application_id,
        chain_id=pins.chain_id,
        domain_id=pins.domain_id,
        release_profile=pins.release_profile,
        signer_registry_id=pins.signer_registry_id,
        expected_signer_registry_hash=pins.expected_signer_registry_hash,
        expected_signer_registry_revision=pins.signer_registry_revision,
        signer_registry_activation_epoch=pins.signer_registry_activation_epoch,
        signer_registry_revocation_epoch=pins.signer_registry_revocation_epoch,
        expected_quorum_threshold=pins.expected_quorum_threshold,
        rollback_policy_root=pins.rollback_policy_root,
        revocation_policy_root=pins.revocation_policy_root,
        revocation_registry_root=pins.revocation_registry_root,
        external_trust_pin_identity=EXTERNAL_TRUST_PIN_IDENTITY,
    )


def _new_store(
    tmp_path: Path,
    *,
    name: str = "authenticated-selection-v2.sqlite3",
) -> tuple[
    store_v2.SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2,
    _AuthenticatedSpotV7ReleaseSelectionV1,
    candidate_v1.SpotV7ReleaseCandidateManifestV1,
]:
    os.chmod(tmp_path, 0o700)
    provisional_identity = store_v2.SpotV7AuthenticatedReleaseSelectionStoreIdentityV2(
        application_id="zenodex",
        chain_id="tau-chain-314159",
        domain_id="spot-domain-271828",
        release_profile=candidate_v1.SPOT_V7_RELEASE_PROFILE_V1,
        signer_registry_id="zrpf-spot-v7-release-selection-signers",
        expected_signer_registry_hash=cast(str, _registry()["registry_hash"]),
        expected_signer_registry_revision=REGISTRY_REVISION,
        signer_registry_activation_epoch=REGISTRY_ACTIVATION_EPOCH,
        signer_registry_revocation_epoch=None,
        expected_quorum_threshold=2,
        rollback_policy_root=bytes.fromhex(
            cast(
                str,
                _candidate_lineage(
                    _candidate_with_static_policies(
                        revision=1,
                        parent_candidate_id=None,
                        variant=0,
                    )
                )["rollback_policy_root"],
            )
        ),
        revocation_policy_root=bytes.fromhex(
            cast(
                str,
                _candidate_lineage(
                    _candidate_with_static_policies(
                        revision=1,
                        parent_candidate_id=None,
                        variant=0,
                    )
                )["revocation_policy_root"],
            )
        ),
        revocation_registry_root=REVOCATION_REGISTRY_ROOT,
        external_trust_pin_identity=EXTERNAL_TRUST_PIN_IDENTITY,
    )
    genesis_cursor = store_v2._genesis_cursor(provisional_identity)
    authenticated, candidate, pins = _authenticated_selection(
        cursor=genesis_cursor,
        revision=1,
        parent_candidate_id=None,
        variant=0,
        evaluation_epoch=EVALUATION_EPOCH,
    )
    identity = _identity(pins)
    assert identity == provisional_identity
    store = store_v2.SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2(
        (tmp_path / name).resolve(),
        identity=identity,
    )
    return store, authenticated, candidate


def test_authenticated_selection_commits_replays_and_revalidates_after_restart(
    tmp_path: Path,
) -> None:
    store, authenticated, candidate = _new_store(tmp_path)

    committed = store.commit(authenticated)
    replay = store.commit(authenticated)
    restarted = store_v2.SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2(
        store.path,
        identity=store.identity,
    )

    assert committed.disposition is store_v2.AuthenticatedReleaseSelectionDispositionV2.COMMITTED
    assert committed.code == "AUTHENTICATED_SELECT_COMMITTED"
    assert committed.cursor.database_revision == 1
    assert committed.cursor.current_candidate_id == candidate.candidate_id
    assert replay.disposition is store_v2.AuthenticatedReleaseSelectionDispositionV2.IDEMPOTENT
    assert replay.cursor == committed.cursor
    assert restarted.read_cursor() == committed.cursor
    assert committed.candidate_selected is False
    assert committed.revocation_authority is False
    assert committed.revocation_blocker_code == ("SIGNED_RELEASE_REVOCATION_CAPABILITY_REQUIRED")
    assert store.revocation_blocker_code == committed.revocation_blocker_code
    assert committed.release_authority is False
    assert committed.runtime_authority is False
    assert committed.settlement_authority is False
    assert committed.production_authority is False
    assert committed.monotonic_state_anchor_verified is False
    assert committed.same_uid_path_substitution_resistance_established is False
    assert committed.same_uid_path_substitution_blocker_code == (
        "DEDICATED_STORAGE_SUPERVISOR_REQUIRED"
    )
    assert store.same_uid_path_substitution_resistance_established is False
    assert store.identity.same_uid_path_substitution_resistance_established is False


def test_result_requires_private_store_construction_and_explicit_disposition(
    tmp_path: Path,
) -> None:
    store, authenticated, candidate = _new_store(tmp_path)
    committed = store.commit(authenticated)
    idempotent = store.commit(authenticated)
    gap, _gap_candidate, _pins = _authenticated_selection(
        cursor=committed.cursor,
        revision=3,
        parent_candidate_id=candidate.candidate_id,
        variant=4,
        evaluation_epoch=EVALUATION_EPOCH + 1,
    )
    rejected = store.commit(gap)

    with pytest.raises(TypeError, match="module-private store result"):
        store_v2.SpotV7AuthenticatedReleaseSelectionResultV2(
            disposition=store_v2.AuthenticatedReleaseSelectionDispositionV2.COMMITTED,
            code="CALLER_FORGED_COMMIT",
            selector_input_id=authenticated.selector_input_id,
            cursor=committed.cursor,
        )
    assert (
        "durable_authenticated_selection_recorded"
        not in store_v2.SpotV7AuthenticatedReleaseSelectionResultV2.__dict__
    )
    assert rejected.disposition is store_v2.AuthenticatedReleaseSelectionDispositionV2.REJECTED
    assert rejected.code == "RELEASE_REVISION_GAP"
    for result in (committed, idempotent, rejected):
        with pytest.raises(TypeError, match="explicit disposition handling"):
            bool(result)
        for slot in result.__slots__:
            with pytest.raises(TypeError, match="immutable"):
                delattr(result, slot)
        with pytest.raises(TypeError, match="cannot be copied"):
            copy.copy(result)
        with pytest.raises(TypeError, match="cannot be deep-copied"):
            copy.deepcopy(result)
        with pytest.raises(TypeError, match="cannot be serialized"):
            pickle.dumps(result)


def test_store_rejects_raw_nominal_objects_and_preserves_empty_state(tmp_path: Path) -> None:
    store, authenticated, _candidate = _new_store(tmp_path)
    initial = store.read_cursor()

    for raw in (True, {"verified": True}, authenticated._artifacts_for_durable_store_v2()):
        with pytest.raises(TypeError, match="exact authenticated"):
            store.commit(cast(Any, raw))

    assert store.read_cursor() == initial


def test_static_identity_drift_and_v1_database_reinterpretation_fail_closed(
    tmp_path: Path,
) -> None:
    store, authenticated, _candidate = _new_store(tmp_path)
    store.commit(authenticated)
    wrong_identity = replace(
        store.identity,
        external_trust_pin_identity=_position_bytes(251),
    )

    with pytest.raises(
        store_v2.SpotV7AuthenticatedReleaseSelectionStoreErrorV2,
        match="STORE_OPEN_FAILED.*identity drift",
    ):
        store_v2.SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2(
            store.path,
            identity=wrong_identity,
        )

    v1_path = (tmp_path / "legacy-v1.sqlite3").resolve()
    legacy = store_v1.SQLiteSpotV7GovernedReleaseSelectionStoreV1(v1_path)
    with pytest.raises(
        store_v2.SpotV7AuthenticatedReleaseSelectionStoreErrorV2,
        match="STORE_OPEN_FAILED.*application_id mismatch",
    ):
        store_v2.SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2(
            legacy.path,
            identity=store.identity,
        )


def test_hard_linked_database_file_rejects_before_read(tmp_path: Path) -> None:
    store, authenticated, _candidate = _new_store(tmp_path)
    store.commit(authenticated)
    alias = (tmp_path / "authenticated-selection-alias.sqlite3").resolve()
    os.link(store.path, alias)

    with pytest.raises(
        store_v2.SpotV7AuthenticatedReleaseSelectionStoreErrorV2,
        match="STORE_READ_FAILED.*exactly one hard link",
    ):
        store.read_cursor()

    alias.unlink()
    assert store.read_cursor().database_revision == 1


def test_valid_snapshot_replacement_keeps_external_monotonic_anchor_false(
    tmp_path: Path,
) -> None:
    store, genesis, genesis_candidate = _new_store(tmp_path)
    first = store.commit(genesis).cursor
    old_snapshot = (tmp_path / "old-valid-snapshot.sqlite3").resolve()
    shutil.copyfile(store.path, old_snapshot)
    os.chmod(old_snapshot, 0o600)

    forward, _candidate, _pins = _authenticated_selection(
        cursor=first,
        revision=2,
        parent_candidate_id=genesis_candidate.candidate_id,
        variant=1,
        evaluation_epoch=EVALUATION_EPOCH + 1,
    )
    assert store.commit(forward).cursor.database_revision == 2

    os.replace(old_snapshot, store.path)
    reopened = store_v2.SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2(
        store.path,
        identity=store.identity,
    )
    rolled_back = reopened.read_cursor()

    assert rolled_back.database_revision == 1
    assert reopened.monotonic_state_anchor_verified is False
    assert rolled_back.monotonic_state_anchor_verified is False
    assert reopened.monotonic_state_anchor_blocker_code == (
        "EXTERNAL_MONOTONIC_RELEASE_STATE_ANCHOR_REQUIRED"
    )


def test_authenticated_registry_drift_rejects_without_store_mutation(tmp_path: Path) -> None:
    store, _authenticated, _candidate = _new_store(tmp_path)
    drifted, _candidate, _pins = _authenticated_selection(
        cursor=store.read_cursor(),
        revision=1,
        parent_candidate_id=None,
        variant=0,
        evaluation_epoch=EVALUATION_EPOCH,
        registry_override=_registry(threshold=1),
    )

    with pytest.raises(
        store_v2.SpotV7AuthenticatedReleaseSelectionStoreErrorV2,
        match="AUTHENTICATED_SELECTION_INVALID.*REGISTRY_HASH_MISMATCH",
    ):
        store.commit(drifted)

    assert store.read_cursor().database_revision == 0


def test_authenticated_release_revision_rollback_rejects_as_noop(tmp_path: Path) -> None:
    store, genesis, current = _new_store(tmp_path)
    cursor = store.commit(genesis).cursor
    for revision, variant in ((2, 1), (3, 2)):
        forward, candidate, _pins = _authenticated_selection(
            cursor=cursor,
            revision=revision,
            parent_candidate_id=current.candidate_id,
            variant=variant,
            evaluation_epoch=EVALUATION_EPOCH + revision,
        )
        committed = store.commit(forward)
        assert committed.disposition is (
            store_v2.AuthenticatedReleaseSelectionDispositionV2.COMMITTED
        )
        cursor = committed.cursor
        current = candidate
    stable = cursor
    rollback, _candidate, _pins = _authenticated_selection(
        cursor=stable,
        revision=2,
        parent_candidate_id=current.candidate_id,
        variant=4,
        evaluation_epoch=EVALUATION_EPOCH + 4,
    )

    rejected = store.commit(rollback)

    assert rejected.disposition is store_v2.AuthenticatedReleaseSelectionDispositionV2.REJECTED
    assert rejected.code == "RELEASE_ROLLBACK_REJECTED"
    assert rejected.cursor == stable
    assert store.read_cursor() == stable


def test_schema_is_exact_and_all_stored_authority_flags_are_false(tmp_path: Path) -> None:
    store, authenticated, _candidate = _new_store(tmp_path)
    store.commit(authenticated)

    with sqlite3.connect(store.path) as connection:
        objects = connection.execute(
            "SELECT type, name FROM sqlite_master WHERE name NOT LIKE 'sqlite_%' ORDER BY type, name"
        ).fetchall()
        event = connection.execute(
            "SELECT durable_authenticated_selection_recorded, revocation_authority, "
            "release_authority, runtime_authority, settlement_authority, production_authority "
            "FROM spot_v7_authenticated_release_selection_events_v2"
        ).fetchone()
        meta = connection.execute(
            "SELECT release_authority, runtime_authority, settlement_authority, production_authority "
            "FROM spot_v7_authenticated_release_selection_meta_v2"
        ).fetchone()
        event_columns = {
            row[1]
            for row in connection.execute(
                "PRAGMA table_info(spot_v7_authenticated_release_selection_events_v2)"
            ).fetchall()
        }

    assert objects == [
        ("table", "spot_v7_authenticated_release_selection_events_v2"),
        ("table", "spot_v7_authenticated_release_selection_meta_v2"),
    ]
    assert event == (1, 0, 0, 0, 0, 0)
    assert meta == (0, 0, 0, 0)
    assert {
        "authentication_evidence_bytes",
        "candidate_bytes",
        "external_trust_pin_identity",
        "external_trust_pins_bytes",
        "quorum_report_bytes",
        "signature_envelopes_bytes",
        "signed_envelope_bytes",
        "signer_registry_bytes",
    } <= event_columns


@pytest.mark.parametrize(
    "column",
    (
        "candidate_bytes",
        "signed_envelope_bytes",
        "signer_registry_bytes",
        "signature_envelopes_bytes",
        "quorum_report_bytes",
        "external_trust_pins_bytes",
        "authentication_evidence_bytes",
    ),
)
def test_restart_rejects_every_persisted_artifact_mutation(
    tmp_path: Path,
    column: str,
) -> None:
    store, authenticated, _candidate = _new_store(tmp_path, name=f"{column}.sqlite3")
    store.commit(authenticated)
    with sqlite3.connect(store.path) as connection:
        connection.execute(
            f"UPDATE spot_v7_authenticated_release_selection_events_v2 "
            f"SET {column} = zeroblob(length({column}))"
        )

    with pytest.raises(
        store_v2.SpotV7AuthenticatedReleaseSelectionStoreErrorV2,
        match="STORE_OPEN_FAILED",
    ):
        store_v2.SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2(
            store.path,
            identity=store.identity,
        )


def test_restart_rejects_meta_and_schema_corruption(tmp_path: Path) -> None:
    meta_store, authenticated, _candidate = _new_store(tmp_path, name="meta.sqlite3")
    meta_store.commit(authenticated)
    with sqlite3.connect(meta_store.path) as connection:
        connection.execute(
            "UPDATE spot_v7_authenticated_release_selection_meta_v2 "
            "SET store_identity_sha256 = zeroblob(32)"
        )
    with pytest.raises(store_v2.SpotV7AuthenticatedReleaseSelectionStoreErrorV2):
        store_v2.SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2(
            meta_store.path,
            identity=meta_store.identity,
        )

    schema_store, _authenticated, _candidate = _new_store(tmp_path, name="schema.sqlite3")
    with sqlite3.connect(schema_store.path) as connection:
        connection.execute("CREATE TABLE injected(value INTEGER) STRICT")
    with pytest.raises(store_v2.SpotV7AuthenticatedReleaseSelectionStoreErrorV2):
        store_v2.SQLiteSpotV7AuthenticatedReleaseSelectionStoreV2(
            schema_store.path,
            identity=schema_store.identity,
        )


def test_two_concurrent_authenticated_forks_commit_exactly_one(tmp_path: Path) -> None:
    store, genesis, genesis_candidate = _new_store(tmp_path)
    selected = store.commit(genesis)
    stable = selected.cursor
    left, _left_candidate, _pins = _authenticated_selection(
        cursor=stable,
        revision=2,
        parent_candidate_id=genesis_candidate.candidate_id,
        variant=1,
        evaluation_epoch=EVALUATION_EPOCH + 1,
    )
    right, _right_candidate, _pins = _authenticated_selection(
        cursor=stable,
        revision=2,
        parent_candidate_id=genesis_candidate.candidate_id,
        variant=2,
        evaluation_epoch=EVALUATION_EPOCH + 1,
    )
    barrier = threading.Barrier(2)

    def commit_after_barrier(
        capability: _AuthenticatedSpotV7ReleaseSelectionV1,
    ) -> store_v2.SpotV7AuthenticatedReleaseSelectionResultV2:
        barrier.wait(timeout=5)
        return store.commit(capability)

    with ThreadPoolExecutor(max_workers=2) as executor:
        futures = [
            executor.submit(commit_after_barrier, capability) for capability in (left, right)
        ]
        results = [future.result(timeout=30) for future in futures]

    dispositions = [result.disposition for result in results]
    assert dispositions.count(store_v2.AuthenticatedReleaseSelectionDispositionV2.COMMITTED) == 1
    assert dispositions.count(store_v2.AuthenticatedReleaseSelectionDispositionV2.REJECTED) == 1
    rejected = next(
        result
        for result in results
        if result.disposition is store_v2.AuthenticatedReleaseSelectionDispositionV2.REJECTED
    )
    assert rejected.code in {
        "CURRENT_CANDIDATE_CAS_MISMATCH",
        "CURRENT_SELECTION_CAS_MISMATCH",
        "DATABASE_REVISION_CAS_MISMATCH",
    }
    assert store.read_cursor().database_revision == 2


def test_post_commit_fsync_failure_resolves_exact_event(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store, authenticated, _candidate = _new_store(tmp_path)

    def fail_fsync(_path: Path) -> None:
        raise OSError("injected directory fsync failure")

    monkeypatch.setattr(store_v2, "_fsync_directory", fail_fsync)
    result = store.commit(authenticated)

    assert result.disposition is store_v2.AuthenticatedReleaseSelectionDispositionV2.COMMITTED
    assert result.code == "AUTHENTICATED_SELECT_COMMITTED_POST_COMMIT_RESOLVED"
    assert result.cursor.database_revision == 1


def test_post_commit_resolution_rejects_schema_extension(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store, authenticated, _candidate = _new_store(tmp_path)

    def extend_schema_then_fail(_path: Path) -> None:
        with sqlite3.connect(store.path) as connection:
            connection.execute("CREATE TABLE injected_extension(value INTEGER)")
        raise OSError("injected directory fsync failure after schema extension")

    monkeypatch.setattr(store_v2, "_fsync_directory", extend_schema_then_fail)

    with pytest.raises(
        store_v2.SpotV7AuthenticatedReleaseSelectionDurabilityUncertainV2
    ) as captured:
        store.commit(authenticated)

    assert captured.value.selector_input_id == authenticated.selector_input_id
    assert captured.value.release_authority is False
    assert captured.value.production_authority is False


def test_unresolved_post_commit_outcome_raises_typed_uncertainty(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store, authenticated, _candidate = _new_store(tmp_path)
    original = store_v2._validate_complete_history
    calls = 0

    def fail_resolution(
        connection: sqlite3.Connection,
        identity: store_v2.SpotV7AuthenticatedReleaseSelectionStoreIdentityV2,
    ) -> store_v2.SpotV7AuthenticatedReleaseSelectionCursorV2:
        nonlocal calls
        calls += 1
        result = original(connection, identity)
        if calls == 2:
            raise ValueError("injected post-commit resolution failure")
        return result

    def fail_fsync(_path: Path) -> None:
        raise OSError("injected directory fsync failure")

    monkeypatch.setattr(store_v2, "_validate_complete_history", fail_resolution)
    monkeypatch.setattr(store_v2, "_fsync_directory", fail_fsync)
    with pytest.raises(
        store_v2.SpotV7AuthenticatedReleaseSelectionDurabilityUncertainV2
    ) as captured:
        store.commit(authenticated)

    assert captured.value.selector_input_id == authenticated.selector_input_id
    assert captured.value.release_authority is False
    assert captured.value.revocation_authority is False
    assert captured.value.production_authority is False
