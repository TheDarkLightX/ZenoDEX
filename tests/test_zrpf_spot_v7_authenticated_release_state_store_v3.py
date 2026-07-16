from __future__ import annotations

import copy
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

from src.integration._zrpf_spot_v7_release_revocation_envelope_v1 import (
    SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
    spot_v7_release_revocation_envelope_payload_hash_v1,
)
from src.integration.zeno_ledger_signature import build_bls_signed_artifact_envelope_v0
from src.integration.zrpf_spot_v7_authenticated_release_revocation_v1 import (
    SpotV7ReleaseRevocationExternalTrustPinsV1,
    _AuthenticatedSpotV7ReleaseRevocationV1,
    authenticate_spot_v7_release_revocation_v1,
    build_spot_v7_release_revocation_envelope_v1,
)
from src.integration.zrpf_spot_v7_authenticated_release_selection_v1 import (
    _AuthenticatedSpotV7ReleaseSelectionV1,
)
from tests import test_zrpf_spot_v7_authenticated_release_selection_store_v2 as v2_fx
from tests.integration import test_zrpf_spot_v7_authenticated_release_revocation_v1 as revoke_fx
from tests.test_zrpf_spot_v7_authenticated_release_selection_store_v2 import (
    EVALUATION_EPOCH,
    REVOCATION_REGISTRY_ROOT,
    _authenticated_selection,
)
from tests.test_zrpf_spot_v7_governed_release_selection_store_v1 import (
    _position_bytes,
    _revocation_bytes,
    _selector_bytes,
)
from tools import zrpf_spot_v7_authenticated_release_selection_store_v2 as store_v2
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools import zrpf_spot_v7_governed_release_selection_store_v1 as store_v1
from tools import zrpf_spot_v7_governed_release_selector_input_v1 as selector_v1

REVOCATION_EPOCH = EVALUATION_EPOCH + 10


def _v2_genesis_cursor() -> store_v2.SpotV7AuthenticatedReleaseSelectionCursorV2:
    return store_v2.SpotV7AuthenticatedReleaseSelectionCursorV2(
        database_revision=0,
        state_root=_position_bytes(20),
        last_evaluation_epoch=None,
        current_candidate_id=None,
        current_candidate_sha256=None,
        current_release_revision=None,
        current_selector_input_id=None,
    )


def _v1_selected_cursor(
    capability: _AuthenticatedSpotV7ReleaseSelectionV1,
) -> store_v1.SpotV7ReleaseSelectionCursorV1:
    return store_v1.SpotV7ReleaseSelectionCursorV1(
        database_revision=1,
        state_root=_position_bytes(21),
        last_evaluation_epoch=capability.evaluation_epoch,
        current_candidate_id=capability.selected_candidate_id,
        current_candidate_sha256=capability.selected_candidate_sha256,
        current_release_revision=capability.release_revision,
        current_select_input_id=capability.selector_input_id,
        current_scope_id=_position_bytes(22),
        current_revoked=False,
        current_revocation_record_id=None,
    )


def _revocation_material(
    selection: _AuthenticatedSpotV7ReleaseSelectionV1,
    candidate_bytes: bytes,
    *,
    nonce_index: int = 241,
) -> tuple[
    _AuthenticatedSpotV7ReleaseRevocationV1,
    SpotV7ReleaseRevocationExternalTrustPinsV1,
]:
    candidate = store_v3.check_exact_spot_v7_release_candidate_manifest_v1(
        candidate_bytes,
        expected_candidate_id=selection.selected_candidate_id,
    )
    cursor = _v1_selected_cursor(selection)
    record_bytes, record_id = _revocation_bytes(
        candidate=candidate,
        revocation_registry_root=REVOCATION_REGISTRY_ROOT,
        effective_epoch=REVOCATION_EPOCH,
        record_revision=revoke_fx.RECORD_REVISION,
        nonce_index=nonce_index,
    )
    selector_bytes, selector_id = _selector_bytes(
        operation=selector_v1.SelectorOperationV1.REVOKE,
        candidate=candidate,
        cursor=cursor,
        evaluation_epoch=REVOCATION_EPOCH,
        nonce_index=nonce_index + 1,
        revocation_registry_root=REVOCATION_REGISTRY_ROOT,
        revocation_record_id=record_id,
    )
    registry = revoke_fx._registry()
    pins = revoke_fx._pins(
        candidate,
        cursor,
        record_bytes,
        record_id,
        registry=registry,
        trusted_evaluation_epoch=REVOCATION_EPOCH,
    )
    envelope = build_spot_v7_release_revocation_envelope_v1(
        revocation_selector_input_bytes=selector_bytes,
        expected_revocation_selector_input_id=selector_id,
        current_candidate_bytes=candidate.canonical_bytes,
        revocation_record_bytes=record_bytes,
        expected_revocation_record_id=record_id,
        external_trust_pins=pins,
        trusted_signer_registry=registry,
    )
    payload_hash = spot_v7_release_revocation_envelope_payload_hash_v1(envelope)
    signatures = tuple(
        build_bls_signed_artifact_envelope_v0(
            payload_kind=SPOT_V7_RELEASE_REVOCATION_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id=f"release-revocation-signer-{index}",
            key_id=f"release-revocation-key-{index}",
            private_key_hex=private_key,
        )
        for index, private_key in enumerate((revoke_fx.PRIVATE_KEY_0, revoke_fx.PRIVATE_KEY_1))
    )
    return (
        authenticate_spot_v7_release_revocation_v1(
            envelope,
            revocation_selector_input_bytes=selector_bytes,
            expected_revocation_selector_input_id=selector_id,
            current_candidate_bytes=candidate.canonical_bytes,
            revocation_record_bytes=record_bytes,
            expected_revocation_record_id=record_id,
            external_trust_pins=pins,
            trusted_signer_registry=registry,
            signature_envelopes=signatures,
        ),
        pins,
    )


def _identity(
    selection_pins: Any,
    revocation_pins: SpotV7ReleaseRevocationExternalTrustPinsV1,
) -> store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3:
    return store_v3.SpotV7AuthenticatedReleaseStateStoreIdentityV3(
        application_id=selection_pins.application_id,
        chain_id=selection_pins.chain_id,
        domain_id=selection_pins.domain_id,
        release_profile=selection_pins.release_profile,
        selection_signer_registry_id=selection_pins.signer_registry_id,
        selection_signer_registry_hash=selection_pins.expected_signer_registry_hash,
        selection_signer_registry_revision=selection_pins.signer_registry_revision,
        selection_signer_registry_activation_epoch=(
            selection_pins.signer_registry_activation_epoch
        ),
        selection_signer_registry_revocation_epoch=(
            selection_pins.signer_registry_revocation_epoch
        ),
        selection_quorum_threshold=selection_pins.expected_quorum_threshold,
        selection_derived_static_trust_pin_identity=(
            store_v3.derive_selection_static_trust_pin_identity_v3(selection_pins)
        ),
        revocation_signer_registry_id=revocation_pins.signer_registry_id,
        revocation_signer_registry_hash=revocation_pins.expected_signer_registry_hash,
        revocation_signer_registry_revision=revocation_pins.signer_registry_revision,
        revocation_signer_registry_activation_epoch=(
            revocation_pins.signer_registry_activation_epoch
        ),
        revocation_signer_registry_revocation_epoch=(
            revocation_pins.signer_registry_revocation_epoch
        ),
        revocation_quorum_threshold=revocation_pins.expected_quorum_threshold,
        revocation_derived_static_trust_pin_identity=(
            store_v3.derive_revocation_static_trust_pin_identity_v3(revocation_pins)
        ),
        rollback_policy_root=selection_pins.rollback_policy_root,
        revocation_policy_root=selection_pins.revocation_policy_root,
        revocation_registry_root=selection_pins.revocation_registry_root,
    )


def _new_store(
    tmp_path: Path,
    *,
    name: str = "authenticated-release-state-v3.sqlite3",
    selection_epoch: int = EVALUATION_EPOCH,
) -> tuple[
    store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3,
    _AuthenticatedSpotV7ReleaseSelectionV1,
    _AuthenticatedSpotV7ReleaseRevocationV1,
    bytes,
]:
    os.chmod(tmp_path, 0o700)
    selection, candidate, selection_pins = _authenticated_selection(
        cursor=_v2_genesis_cursor(),
        revision=1,
        parent_candidate_id=None,
        variant=0,
        evaluation_epoch=selection_epoch,
    )
    revocation, revocation_pins = _revocation_material(
        selection,
        candidate.canonical_bytes,
    )
    identity = _identity(selection_pins, revocation_pins)
    store = store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
        (tmp_path / name).resolve(),
        identity=identity,
    )
    return store, selection, revocation, candidate.canonical_bytes


def _v2_cursor_from_v3(
    cursor: store_v3.SpotV7AuthenticatedReleaseStateCursorV3,
) -> store_v2.SpotV7AuthenticatedReleaseSelectionCursorV2:
    return store_v2.SpotV7AuthenticatedReleaseSelectionCursorV2(
        database_revision=cursor.database_revision,
        state_root=cursor.state_root,
        last_evaluation_epoch=cursor.last_evaluation_epoch,
        current_candidate_id=cursor.current_candidate_id,
        current_candidate_sha256=cursor.current_candidate_sha256,
        current_release_revision=cursor.current_release_revision,
        current_selector_input_id=cursor.current_select_input_id,
    )


def _successor_selection(
    cursor: store_v3.SpotV7AuthenticatedReleaseStateCursorV3,
    *,
    variant: int,
    revision: int = 2,
    evaluation_epoch: int | None = None,
) -> _AuthenticatedSpotV7ReleaseSelectionV1:
    capability, _candidate, _pins = _authenticated_selection(
        cursor=_v2_cursor_from_v3(cursor),
        revision=revision,
        parent_candidate_id=cursor.current_candidate_id,
        variant=variant,
        evaluation_epoch=(
            REVOCATION_EPOCH + variant if evaluation_epoch is None else evaluation_epoch
        ),
    )
    return capability


def test_v3_api_starts_authority_neutral() -> None:
    assert store_v3.STORE_SCHEMA_VERSION_V3 == 3
    assert (
        store_v3.SPOT_V7_AUTHENTICATED_RELEASE_STATE_MONOTONIC_ANCHOR_BLOCKER_V3
        == "EXTERNAL_MONOTONIC_RELEASE_STATE_ANCHOR_REQUIRED"
    )


def test_commit_status_requires_private_store_construction_and_has_no_positive_bool() -> None:
    cursor = store_v3.SpotV7AuthenticatedReleaseStateCursorV3(
        database_revision=0,
        state_root=_position_bytes(99),
        last_evaluation_epoch=None,
        current_candidate_id=None,
        current_candidate_sha256=None,
        current_release_revision=None,
        current_select_input_id=None,
        current_revoked=False,
        current_revocation_record_id=None,
    )
    with pytest.raises(TypeError, match="module-private store result"):
        store_v3.SpotV7AuthenticatedReleaseStateResultV3(
            disposition=store_v3.AuthenticatedReleaseStateDispositionV3.COMMITTED,
            code="CALLER_FORGED_COMMIT",
            event_kind=store_v3.ReleaseStateEventKindV3.SELECT,
            selector_input_id=_position_bytes(100),
            cursor=cursor,
        )
    assert (
        "durable_authenticated_release_state_recorded"
        not in store_v3.SpotV7AuthenticatedReleaseStateResultV3.__dict__
    )


def test_derived_static_pin_identity_ignores_event_cursor_and_binds_static_policy(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    selection, candidate, selection_pins = _authenticated_selection(
        cursor=_v2_genesis_cursor(),
        revision=1,
        parent_candidate_id=None,
        variant=0,
        evaluation_epoch=EVALUATION_EPOCH,
    )
    _revocation, revocation_pins = _revocation_material(
        selection,
        candidate.canonical_bytes,
    )
    select_identity = store_v3.derive_selection_static_trust_pin_identity_v3(selection_pins)
    revoke_identity = store_v3.derive_revocation_static_trust_pin_identity_v3(revocation_pins)

    changed_selection_event = replace(
        selection_pins,
        trusted_evaluation_epoch=selection_pins.trusted_evaluation_epoch + 1,
        expected_database_revision=selection_pins.expected_database_revision + 1,
        minimum_target_release_revision=selection_pins.minimum_target_release_revision + 1,
    )
    changed_revocation_event = replace(
        revocation_pins,
        trusted_evaluation_epoch=revocation_pins.trusted_evaluation_epoch + 1,
        expected_database_revision=revocation_pins.expected_database_revision + 1,
        expected_last_evaluation_epoch=revocation_pins.expected_last_evaluation_epoch + 1,
        current_revocation_record_id=revocation_pins.expected_revocation_record_id,
    )
    assert (
        store_v3.derive_selection_static_trust_pin_identity_v3(changed_selection_event)
        == select_identity
    )
    assert (
        store_v3.derive_revocation_static_trust_pin_identity_v3(changed_revocation_event)
        == revoke_identity
    )

    selection_static_changes = (
        replace(selection_pins, application_id="other-application"),
        replace(selection_pins, chain_id="other-chain"),
        replace(selection_pins, domain_id="other-domain"),
        replace(selection_pins, rollback_policy_root=_position_bytes(90)),
        replace(selection_pins, revocation_policy_root=_position_bytes(91)),
        replace(selection_pins, revocation_registry_root=_position_bytes(92)),
        replace(selection_pins, signer_registry_id="other-selection-registry"),
        replace(selection_pins, expected_signer_registry_hash="0x" + ("91" * 32)),
        replace(
            selection_pins,
            signer_registry_revision=selection_pins.signer_registry_revision + 1,
        ),
        replace(
            selection_pins,
            signer_registry_activation_epoch=(selection_pins.signer_registry_activation_epoch + 1),
        ),
        replace(
            selection_pins,
            signer_registry_revocation_epoch=(selection_pins.signer_registry_activation_epoch + 2),
        ),
        replace(
            selection_pins,
            expected_quorum_threshold=selection_pins.expected_quorum_threshold + 1,
        ),
    )
    revocation_static_changes = (
        replace(revocation_pins, application_id="other-application"),
        replace(revocation_pins, chain_id="other-chain"),
        replace(revocation_pins, domain_id="other-domain"),
        replace(revocation_pins, rollback_policy_root=_position_bytes(93)),
        replace(revocation_pins, revocation_policy_root=_position_bytes(94)),
        replace(revocation_pins, revocation_registry_root=_position_bytes(95)),
        replace(revocation_pins, signer_registry_id="other-revocation-registry"),
        replace(revocation_pins, expected_signer_registry_hash="0x" + ("96" * 32)),
        replace(
            revocation_pins,
            signer_registry_revision=revocation_pins.signer_registry_revision + 1,
        ),
        replace(
            revocation_pins,
            signer_registry_activation_epoch=(revocation_pins.signer_registry_activation_epoch + 1),
        ),
        replace(
            revocation_pins,
            signer_registry_revocation_epoch=(revocation_pins.signer_registry_activation_epoch + 2),
        ),
        replace(
            revocation_pins,
            expected_quorum_threshold=revocation_pins.expected_quorum_threshold + 1,
        ),
    )
    assert all(
        store_v3.derive_selection_static_trust_pin_identity_v3(changed) != select_identity
        for changed in selection_static_changes
    )
    assert all(
        store_v3.derive_revocation_static_trust_pin_identity_v3(changed) != revoke_identity
        for changed in revocation_static_changes
    )
    assert (
        store_v3.SPOT_V7_DERIVED_STATIC_TRUST_PIN_IDENTITY_ALGORITHM_V3
        == "sha256-domain-canonical-static-pins-v3"
    )
    identity = _identity(selection_pins, revocation_pins)
    assert (
        store_v3.SPOT_V7_SELECTION_DERIVED_STATIC_TRUST_PIN_DOMAIN_V3.encode("ascii")
        in identity.canonical_bytes
    )
    assert (
        store_v3.SPOT_V7_REVOCATION_DERIVED_STATIC_TRUST_PIN_DOMAIN_V3.encode("ascii")
        in identity.canonical_bytes
    )
    assert (
        store_v3.SPOT_V7_DERIVED_STATIC_TRUST_PIN_IDENTITY_ALGORITHM_V3.encode("ascii")
        in identity.canonical_bytes
    )

    monkeypatch.setattr(
        store_v3,
        "SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1",
        "zrpf_spot_v7_release_selection_mutated",
    )
    assert store_v3.derive_selection_static_trust_pin_identity_v3(selection_pins) != select_identity


def test_select_then_revoke_replays_and_reopens_authority_neutral(tmp_path: Path) -> None:
    store, selection, revocation, _candidate_bytes = _new_store(tmp_path)

    selected = store.commit_selection(selection)
    selected_replay = store.commit(selection)
    revoked = store.commit_revocation(revocation)
    revoked_replay = store.commit(revocation)
    reopened = store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
        store.path,
        identity=store.identity,
    )

    assert selected.disposition is store_v3.AuthenticatedReleaseStateDispositionV3.COMMITTED
    assert selected_replay.disposition is (
        store_v3.AuthenticatedReleaseStateDispositionV3.IDEMPOTENT
    )
    assert revoked.disposition is store_v3.AuthenticatedReleaseStateDispositionV3.COMMITTED
    assert revoked_replay.disposition is (
        store_v3.AuthenticatedReleaseStateDispositionV3.IDEMPOTENT
    )
    assert revoked.cursor.database_revision == 2
    assert revoked.cursor.current_candidate_id == selection.selected_candidate_id
    assert revoked.cursor.current_select_input_id == selection.selector_input_id
    assert revoked.cursor.current_revoked is True
    assert revoked.cursor.current_revocation_record_id == revocation.revocation_record_id
    assert reopened.read_cursor() == revoked.cursor
    for value in (store.identity, revoked.cursor, revoked, reopened):
        assert value.release_governed_trust_roots_authenticated is False
        assert value.external_monotonic_state_anchor_verified is False
        assert value.hostile_same_interpreter_resistance_established is False
        assert value.same_uid_path_substitution_resistance_established is False
        assert value.revocation_authority is False
        assert value.release_authority is False
        assert value.runtime_authority is False
        assert value.settlement_authority is False
        assert value.production_authority is False
        assert value.release_governed_trust_roots_blocker_code == (
            "EXTERNAL_RELEASE_TRUST_ROOT_GOVERNANCE_REQUIRED"
        )


def test_result_requires_explicit_disposition_and_rejects_mutation_or_serialization(
    tmp_path: Path,
) -> None:
    store, selection, _revocation, _candidate_bytes = _new_store(tmp_path)
    committed = store.commit(selection)
    idempotent = store.commit(selection)
    gap = _successor_selection(committed.cursor, variant=19, revision=3)
    rejected = store.commit(gap)

    assert rejected.disposition is store_v3.AuthenticatedReleaseStateDispositionV3.REJECTED
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


def test_current_release_snapshot_is_fresh_sealed_and_authority_neutral(
    tmp_path: Path,
) -> None:
    store, selection, revocation, candidate_bytes = _new_store(tmp_path)

    with pytest.raises(
        store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3,
        match="CURRENT_RELEASE_SNAPSHOT_FAILED.*current release is empty",
    ):
        store._current_release_snapshot_for_execution_binding_v1()

    selected = store.commit_selection(selection)
    snapshot = store._current_release_snapshot_for_execution_binding_v1()
    repeated = store._current_release_snapshot_for_execution_binding_v1()

    assert snapshot is not repeated
    assert snapshot.store_identity_sha256 == store.identity.identity_sha256
    assert snapshot.database_revision == selected.cursor.database_revision
    assert snapshot.last_evaluation_epoch == selected.cursor.last_evaluation_epoch
    assert snapshot.state_root == selected.cursor.state_root
    assert snapshot.current_candidate_id == selection.selected_candidate_id
    assert snapshot.current_candidate_sha256 == selection.selected_candidate_sha256
    assert snapshot.current_release_revision == selection.release_revision
    assert snapshot.current_select_input_id == selection.selector_input_id
    assert snapshot.current_revocation_record_id is None
    assert snapshot.current_candidate_bytes == candidate_bytes
    assert snapshot.currentness_at_settlement_verified is False
    assert snapshot.atomic_release_settlement_established is False
    assert snapshot.valid_snapshot_rollback_resistance_established is False
    assert snapshot.hostile_same_interpreter_resistance_established is False
    assert snapshot.external_monotonic_state_anchor_verified is False
    assert snapshot.release_authority is False
    assert snapshot.runtime_authority is False
    assert snapshot.settlement_authority is False
    assert snapshot.production_authority is False
    assert type(snapshot).__name__.startswith("_AuthorityNeutral")
    assert type(snapshot).__name__ not in store_v3.__all__

    with pytest.raises(TypeError, match="immutable"):
        snapshot.database_revision = 99  # type: ignore[misc]
    with pytest.raises(TypeError, match="cannot be copied"):
        copy.copy(snapshot)
    with pytest.raises(TypeError, match="cannot be deep-copied"):
        copy.deepcopy(snapshot)
    with pytest.raises(TypeError, match="cannot be serialized"):
        pickle.dumps(snapshot)

    store.commit_revocation(revocation)
    with pytest.raises(
        store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3,
        match="CURRENT_RELEASE_SNAPSHOT_FAILED.*current release is revoked",
    ):
        store._current_release_snapshot_for_execution_binding_v1()


def test_current_release_snapshot_revalidates_complete_history_each_call(
    tmp_path: Path,
) -> None:
    store, selection, _revocation, _candidate_bytes = _new_store(tmp_path)
    store.commit_selection(selection)
    store._current_release_snapshot_for_execution_binding_v1()

    with sqlite3.connect(store.path) as connection:
        connection.execute(
            """
            UPDATE spot_v7_authenticated_release_state_events_v3
            SET candidate_bytes = ?
            WHERE selector_input_id = ?
            """,
            (b"mutated", selection.selector_input_id),
        )

    with pytest.raises(
        store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3,
        match="CURRENT_RELEASE_SNAPSHOT_FAILED",
    ):
        store._current_release_snapshot_for_execution_binding_v1()


def test_nominal_objects_and_cross_kind_entrypoints_reject_without_mutation(
    tmp_path: Path,
) -> None:
    store, selection, revocation, _candidate_bytes = _new_store(tmp_path)
    initial = store.read_cursor()

    for raw in (True, {"verified": True}, selection._artifacts_for_durable_store_v2()):
        with pytest.raises(TypeError, match="exact authenticated"):
            store.commit(cast(Any, raw))
    with pytest.raises(TypeError, match="SELECT capability"):
        store.commit_selection(cast(Any, revocation))
    with pytest.raises(TypeError, match="REVOKE capability"):
        store.commit_revocation(cast(Any, selection))
    assert store.read_cursor() == initial


def test_terminal_revocation_rejects_conflicting_revoke_and_later_select(
    tmp_path: Path,
) -> None:
    store, selection, revocation, candidate_bytes = _new_store(tmp_path)
    selected = store.commit(selection).cursor
    conflicting_revocation, _pins = _revocation_material(
        selection,
        candidate_bytes,
        nonce_index=251,
    )
    revoked = store.commit(revocation).cursor
    later_select = _successor_selection(revoked, variant=1)

    conflicting = store.commit(conflicting_revocation)
    selected_after_revoke = store.commit(later_select)

    assert conflicting.disposition is store_v3.AuthenticatedReleaseStateDispositionV3.REJECTED
    assert conflicting.code == "CURRENT_RELEASE_ALREADY_REVOKED"
    assert selected_after_revoke.disposition is (
        store_v3.AuthenticatedReleaseStateDispositionV3.REJECTED
    )
    assert selected_after_revoke.code == "CURRENT_RELEASE_TERMINALLY_REVOKED"
    assert conflicting.cursor == revoked
    assert selected_after_revoke.cursor == revoked
    assert selected.database_revision == 1
    assert store.read_cursor() == revoked


def test_revocation_without_head_and_stale_or_gapped_selection_reject_as_noop(
    tmp_path: Path,
) -> None:
    store, selection, revocation, _candidate_bytes = _new_store(
        tmp_path,
        selection_epoch=EVALUATION_EPOCH + 5,
    )
    empty = store.read_cursor()
    no_head = store.commit(revocation)
    assert no_head.disposition is store_v3.AuthenticatedReleaseStateDispositionV3.REJECTED
    assert no_head.code == "REVOCATION_WITHOUT_CURRENT_HEAD"
    assert no_head.cursor == empty

    selected = store.commit(selection).cursor
    stale = _successor_selection(
        selected,
        variant=1,
        evaluation_epoch=EVALUATION_EPOCH + 4,
    )
    gap = _successor_selection(selected, variant=2, revision=3)
    stale_result = store.commit(stale)
    gap_result = store.commit(gap)
    assert stale_result.code == "EVALUATION_EPOCH_ROLLBACK_REJECTED"
    assert gap_result.code == "RELEASE_REVISION_GAP"
    assert stale_result.cursor == selected
    assert gap_result.cursor == selected


def test_release_rollback_and_old_candidate_revocation_reject(tmp_path: Path) -> None:
    store, selection, old_revocation, _candidate_bytes = _new_store(tmp_path)
    cursor = store.commit(selection).cursor
    second = _successor_selection(cursor, variant=1, revision=2)
    cursor = store.commit(second).cursor
    third = _successor_selection(cursor, variant=2, revision=3)
    cursor = store.commit(third).cursor
    rollback = _successor_selection(cursor, variant=4, revision=2)

    rollback_result = store.commit(rollback)
    old_revoke_result = store.commit(old_revocation)
    assert rollback_result.code == "RELEASE_ROLLBACK_REJECTED"
    assert old_revoke_result.code in {
        "EVALUATION_EPOCH_ROLLBACK_REJECTED",
        "DATABASE_REVISION_CAS_MISMATCH",
        "CURRENT_CANDIDATE_CAS_MISMATCH",
        "CURRENT_SELECTION_CAS_MISMATCH",
    }
    assert rollback_result.cursor == cursor
    assert old_revoke_result.cursor == cursor


def test_two_concurrent_identical_selects_append_one_event(tmp_path: Path) -> None:
    store, selection, _revocation, _candidate_bytes = _new_store(tmp_path)
    barrier = threading.Barrier(2)

    def commit() -> store_v3.SpotV7AuthenticatedReleaseStateResultV3:
        barrier.wait(timeout=5)
        return store.commit(selection)

    with ThreadPoolExecutor(max_workers=2) as executor:
        results = [
            future.result(timeout=45)
            for future in (executor.submit(commit), executor.submit(commit))
        ]

    dispositions = {result.disposition for result in results}
    assert dispositions == {
        store_v3.AuthenticatedReleaseStateDispositionV3.COMMITTED,
        store_v3.AuthenticatedReleaseStateDispositionV3.IDEMPOTENT,
    }
    assert store.read_cursor().database_revision == 1


def test_two_concurrent_successor_forks_commit_exactly_one(tmp_path: Path) -> None:
    store, selection, _revocation, _candidate_bytes = _new_store(tmp_path)
    selected = store.commit(selection).cursor
    left = _successor_selection(selected, variant=1)
    right = _successor_selection(selected, variant=2)
    barrier = threading.Barrier(2)

    def commit(capability: _AuthenticatedSpotV7ReleaseSelectionV1):
        barrier.wait(timeout=5)
        return store.commit(capability)

    with ThreadPoolExecutor(max_workers=2) as executor:
        results = [
            future.result(timeout=45)
            for future in (executor.submit(commit, left), executor.submit(commit, right))
        ]

    assert (
        sum(
            result.disposition is store_v3.AuthenticatedReleaseStateDispositionV3.COMMITTED
            for result in results
        )
        == 1
    )
    assert (
        sum(
            result.disposition is store_v3.AuthenticatedReleaseStateDispositionV3.REJECTED
            for result in results
        )
        == 1
    )
    assert store.read_cursor().database_revision == 2


@pytest.mark.parametrize(
    "column",
    (
        "candidate_bytes",
        "envelope_bytes",
        "signer_registry_bytes",
        "signature_envelopes_bytes",
        "quorum_report_bytes",
        "external_trust_pins_bytes",
        "authentication_evidence_bytes",
    ),
)
def test_reopen_rejects_every_persisted_projection_mutation(
    tmp_path: Path,
    column: str,
) -> None:
    store, selection, revocation, _candidate_bytes = _new_store(tmp_path)
    store.commit(selection)
    store.commit(revocation)
    with sqlite3.connect(store.path) as connection:
        connection.execute("PRAGMA ignore_check_constraints = ON")
        connection.execute(
            f"UPDATE spot_v7_authenticated_release_state_events_v3 "
            f"SET {column} = zeroblob(length({column})) WHERE event_kind = 'REVOKE'"
        )

    with pytest.raises(
        store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3,
        match="STORE_OPEN_FAILED",
    ):
        store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
            store.path,
            identity=store.identity,
        )


def test_schema_extension_and_authority_bit_mutation_reject(tmp_path: Path) -> None:
    schema_store, selection, _revocation, _candidate_bytes = _new_store(
        tmp_path,
        name="schema.sqlite3",
    )
    schema_store.commit(selection)
    with sqlite3.connect(schema_store.path) as connection:
        connection.execute("CREATE TABLE injected(value INTEGER) STRICT")
    with pytest.raises(store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3):
        schema_store.read_cursor()

    authority_store, selection, _revocation, _candidate_bytes = _new_store(
        tmp_path,
        name="authority.sqlite3",
    )
    authority_store.commit(selection)
    with sqlite3.connect(authority_store.path) as connection:
        connection.execute("PRAGMA ignore_check_constraints = ON")
        connection.execute(
            "UPDATE spot_v7_authenticated_release_state_events_v3 SET release_authority = 1"
        )
    with pytest.raises(store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3):
        authority_store.read_cursor()


def test_hardlink_and_v2_database_reinterpretation_reject(tmp_path: Path) -> None:
    store, selection, _revocation, _candidate_bytes = _new_store(tmp_path)
    store.commit(selection)
    alias = (tmp_path / "hardlink.sqlite3").resolve()
    os.link(store.path, alias)
    with pytest.raises(
        store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3,
        match="exactly one hard link",
    ):
        store.read_cursor()
    alias.unlink()

    v2_store, _authenticated, _candidate = v2_fx._new_store(
        tmp_path,
        name="selection-v2.sqlite3",
    )
    with pytest.raises(
        store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3,
        match="STORE_OPEN_FAILED.*application_id mismatch",
    ):
        store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
            v2_store.path,
            identity=store.identity,
        )


def test_identity_drift_private_modes_and_symlink_path_fail_closed(tmp_path: Path) -> None:
    store, selection, _revocation, _candidate_bytes = _new_store(tmp_path)
    store.commit(selection)
    wrong_identity = replace(
        store.identity,
        selection_derived_static_trust_pin_identity=_position_bytes(99),
    )
    with pytest.raises(
        store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3,
        match="identity drift",
    ):
        store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
            store.path,
            identity=wrong_identity,
        )

    os.chmod(store.path, 0o644)
    with pytest.raises(
        store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3,
        match="private and owned",
    ):
        store.read_cursor()
    os.chmod(store.path, 0o600)

    symlink = tmp_path / "state-link.sqlite3"
    symlink.symlink_to(store.path)
    with pytest.raises(ValueError, match="canonical and symlink-free"):
        store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
            symlink.absolute(),
            identity=store.identity,
        )

    public_parent = tmp_path / "public"
    public_parent.mkdir(mode=0o755)
    os.chmod(public_parent, 0o755)
    with pytest.raises(ValueError, match="parent must be private"):
        store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
            (public_parent / "state.sqlite3").resolve(),
            identity=store.identity,
        )


def test_valid_snapshot_rollback_keeps_monotonic_and_same_uid_claims_false(
    tmp_path: Path,
) -> None:
    store, selection, revocation, _candidate_bytes = _new_store(tmp_path)
    store.commit(selection)
    old_snapshot = (tmp_path / "old-valid.sqlite3").resolve()
    shutil.copyfile(store.path, old_snapshot)
    os.chmod(old_snapshot, 0o600)
    assert store.commit(revocation).cursor.database_revision == 2

    os.replace(old_snapshot, store.path)
    reopened = store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
        store.path,
        identity=store.identity,
    )
    rolled_back = reopened.read_cursor()

    assert rolled_back.database_revision == 1
    assert rolled_back.external_monotonic_state_anchor_verified is False
    assert rolled_back.same_uid_path_substitution_resistance_established is False
    assert reopened.monotonic_state_anchor_blocker_code == (
        "EXTERNAL_MONOTONIC_RELEASE_STATE_ANCHOR_REQUIRED"
    )


def test_post_commit_fsync_failure_revalidates_schema_and_exact_event(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store, selection, _revocation, _candidate_bytes = _new_store(tmp_path)

    def fail_fsync(_path: Path) -> None:
        raise OSError("injected directory fsync failure")

    monkeypatch.setattr(store_v3, "_fsync_directory", fail_fsync)
    result = store.commit(selection)
    assert result.disposition is store_v3.AuthenticatedReleaseStateDispositionV3.COMMITTED
    assert result.code.endswith("POST_COMMIT_RESOLVED")


def test_post_commit_resolution_rejects_schema_injection(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    store, selection, _revocation, _candidate_bytes = _new_store(tmp_path)

    def inject_then_fail(_path: Path) -> None:
        with sqlite3.connect(store.path) as connection:
            connection.execute("CREATE TABLE injected(value INTEGER) STRICT")
        raise OSError("injected directory fsync failure")

    monkeypatch.setattr(store_v3, "_fsync_directory", inject_then_fail)
    with pytest.raises(store_v3.SpotV7AuthenticatedReleaseStateDurabilityUncertainV3):
        store.commit(selection)


@pytest.mark.skipif(not hasattr(os, "fork"), reason="requires POSIX process crash semantics")
def test_subprocess_crash_before_and_after_commit_reopens_deterministically(
    tmp_path: Path,
) -> None:
    before_store, before_selection, _revocation, _candidate = _new_store(
        tmp_path,
        name="before-crash.sqlite3",
    )
    original_insert = store_v3._insert_event
    before_pid = os.fork()
    if before_pid == 0:

        def exit_after_insert(*args: Any, **kwargs: Any) -> None:
            original_insert(*args, **kwargs)
            os._exit(92)

        store_v3._insert_event = exit_after_insert
        before_store.commit(before_selection)
        os._exit(93)
    _wait_for_exit(before_pid, 92)
    before_reopened = store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
        before_store.path,
        identity=before_store.identity,
    )
    assert before_reopened.read_cursor().database_revision == 0

    after_store, after_selection, _revocation, _candidate = _new_store(
        tmp_path,
        name="after-crash.sqlite3",
    )
    after_pid = os.fork()
    if after_pid == 0:

        def exit_after_sqlite_commit(_path: Path) -> None:
            os._exit(94)

        store_v3._fsync_directory = exit_after_sqlite_commit  # type: ignore[assignment]
        after_store.commit(after_selection)
        os._exit(95)
    _wait_for_exit(after_pid, 94)
    after_reopened = store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
        after_store.path,
        identity=after_store.identity,
    )
    assert after_reopened.read_cursor().database_revision == 1


def _wait_for_exit(pid: int, expected_code: int) -> None:
    observed_pid, status = os.waitpid(pid, 0)
    assert observed_pid == pid
    assert os.WIFEXITED(status)
    assert os.WEXITSTATUS(status) == expected_code
