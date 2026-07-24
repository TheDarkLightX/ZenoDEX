from __future__ import annotations

import copy
import hashlib
import inspect
import os
import pickle
from collections.abc import Callable
from pathlib import Path
from typing import Any, cast

import pytest

from tests import test_zrpf_spot_v7_authenticated_release_selection_store_v2 as selection_fx
from tests import test_zrpf_spot_v7_authenticated_release_state_store_v3 as state_fx
from tests.test_zrpf_spot_v7_execution_authority_manifest_v1 import _fixture
from tools import zrpf_spot_v7_authenticated_release_state_store_v3 as store_v3
from tools import zrpf_spot_v7_current_release_execution_binding_v1 as binding
from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate


def _digest(label: str) -> bytes:
    return hashlib.sha256(label.encode("ascii")).digest()


def _snapshot(candidate_bytes: bytes) -> store_v3._AuthorityNeutralCurrentReleaseSnapshotV1:
    parsed = candidate.parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes)
    return store_v3._AuthorityNeutralCurrentReleaseSnapshotV1._from_verified(
        store_identity_sha256=_digest("store-identity"),
        database_revision=7,
        last_evaluation_epoch=101,
        state_root=_digest("release-state"),
        current_candidate_id=parsed.candidate_id,
        current_candidate_sha256=hashlib.sha256(candidate_bytes).digest(),
        current_release_revision=parsed.release_revision,
        current_select_input_id=_digest("select-input"),
        current_revocation_record_id=None,
        current_candidate_bytes=candidate_bytes,
        seal=store_v3._CURRENT_RELEASE_SNAPSHOT_SEAL_V1,
    )


def _first_release_fixture() -> tuple[bytes, bytes]:
    candidate_body, authority_body, _, _ = _fixture()
    lineage = cast(dict[str, Any], candidate_body["lineage"])
    lineage["parent_candidate_id"] = None
    lineage["proposed_activation_epoch"] = selection_fx.EVALUATION_EPOCH - 1
    lineage["proposed_expiration_epoch"] = selection_fx.EVALUATION_EPOCH + 100
    lineage["release_revision"] = 1
    authority_body["release_revision"] = 1
    manifest_bytes = authority.recompose_spot_v7_execution_authority_manifest_v1(authority_body)
    digest = hashlib.sha256(manifest_bytes).hexdigest()
    inventory = cast(list[dict[str, Any]], candidate_body["evidence_inventory"])
    row = next(item for item in inventory if item["role"] == "authority_manifest")
    row["artifact_sha256"] = digest
    row["bound_identity"] = digest
    row["size_bytes"] = len(manifest_bytes)
    cast(dict[str, Any], candidate_body["manifests"])["authority_manifest_sha256"] = digest
    candidate_bytes = candidate.recompose_spot_v7_release_candidate_manifest_v1(candidate_body)
    authority.check_exact_spot_v7_execution_authority_manifest_v1(
        exact_release_candidate_bytes=candidate_bytes,
        exact_authority_manifest_bytes=manifest_bytes,
    )
    return candidate_bytes, manifest_bytes


def _real_store_with_execution_candidate(
    tmp_path: Path,
    candidate_bytes: bytes,
) -> store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3:
    os.chmod(tmp_path, 0o700)
    parsed = candidate.parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes)
    cursor = state_fx._v2_genesis_cursor()
    selector_bytes, selector_id = selection_fx._selector_bytes(
        operation=selection_fx.selector_v1.SelectorOperationV1.SELECT,
        candidate=parsed,
        cursor=selection_fx._v1_cursor(cursor),
        evaluation_epoch=selection_fx.EVALUATION_EPOCH,
        nonce_index=300,
        revocation_registry_root=selection_fx.REVOCATION_REGISTRY_ROOT,
    )
    registry = selection_fx._registry()
    pins = selection_fx._pins(
        candidate=parsed,
        cursor=cursor,
        evaluation_epoch=selection_fx.EVALUATION_EPOCH,
        registry=registry,
    )
    envelope = selection_fx.build_spot_v7_release_selection_envelope_v1(
        selector_input_bytes=selector_bytes,
        expected_selector_input_id=selector_id,
        candidate_bytes=candidate_bytes,
        external_trust_pins=pins,
        trusted_signer_registry=registry,
    )
    payload_hash = selection_fx.spot_v7_release_selection_envelope_payload_hash_v1(envelope)
    signatures = tuple(
        selection_fx.build_bls_signed_artifact_envelope_v0(
            payload_kind=selection_fx.SPOT_V7_RELEASE_SELECTION_PAYLOAD_KIND_V1,
            payload_hash=payload_hash,
            signer_id=f"release-selection-signer-{index}",
            key_id=f"release-selection-key-{index}",
            private_key_hex=private_key,
        )
        for index, private_key in enumerate(
            (selection_fx.PRIVATE_KEY_0, selection_fx.PRIVATE_KEY_1)
        )
    )
    selected = selection_fx.authenticate_spot_v7_release_selection_v1(
        envelope,
        selector_input_bytes=selector_bytes,
        expected_selector_input_id=selector_id,
        candidate_bytes=candidate_bytes,
        external_trust_pins=pins,
        trusted_signer_registry=registry,
        signature_envelopes=signatures,
    )
    _, revocation_pins = state_fx._revocation_material(selected, candidate_bytes)
    store = store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3(
        (tmp_path / "current-release-execution-binding.sqlite3").resolve(),
        identity=state_fx._identity(pins, revocation_pins),
    )
    assert (
        store.commit_selection(selected).disposition
        is store_v3.AuthenticatedReleaseStateDispositionV3.COMMITTED
    )
    return store


def _store_with_snapshot(
    monkeypatch: pytest.MonkeyPatch,
    snapshot: store_v3._AuthorityNeutralCurrentReleaseSnapshotV1,
) -> store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3:
    monkeypatch.setattr(
        store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3,
        "_current_release_snapshot_for_execution_binding_v1",
        lambda _self: snapshot,
    )
    return object.__new__(store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3)


def test_locked_candidate_and_exact_execution_manifest_bind_authority_false(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, _, candidate_bytes, manifest_bytes = _fixture()
    snapshot = _snapshot(candidate_bytes)
    store = _store_with_snapshot(monkeypatch, snapshot)

    observed = binding.bind_current_release_to_execution_manifest_v1(
        store,
        exact_authority_manifest_bytes=manifest_bytes,
    )

    assert observed.store_identity_sha256 == snapshot.store_identity_sha256
    assert observed.database_revision == 7
    assert observed.last_evaluation_epoch == 101
    assert observed.release_state_root == snapshot.state_root
    assert observed.current_candidate_id == snapshot.current_candidate_id
    assert observed.current_candidate_sha256 == hashlib.sha256(candidate_bytes).digest()
    assert observed.current_release_revision == 7
    assert observed.current_select_input_id == snapshot.current_select_input_id
    assert observed.current_revocation_record_id is None
    assert observed.exact_candidate_bytes == candidate_bytes
    assert observed.exact_authority_manifest_bytes == manifest_bytes
    assert observed.execution_authority_manifest_sha256 == hashlib.sha256(manifest_bytes).digest()
    assert (
        observed.observation_root
        == hashlib.sha256(
            binding.CURRENT_RELEASE_EXECUTION_OBSERVATION_HASH_DOMAIN_V1
            + binding.encode_bytes(observed.canonical_observation_bytes)
        ).digest()
    )
    assert observed.currentness_at_settlement_established is False
    assert observed.atomic_release_and_settlement_commit_established is False
    assert observed.external_monotonic_rollback_resistance_established is False
    assert observed.hostile_same_interpreter_resistance_established is False
    assert observed.proof_receipt_authority is False
    assert observed.runtime_authority is False
    assert observed.release_authority is False
    assert observed.settlement_authority is False
    assert observed.production_authority is False


def test_real_authenticated_store_replay_binds_exact_execution_manifest(
    tmp_path: Path,
) -> None:
    candidate_bytes, manifest_bytes = _first_release_fixture()
    store = _real_store_with_execution_candidate(tmp_path, candidate_bytes)

    observed = binding.bind_current_release_to_execution_manifest_v1(
        store,
        exact_authority_manifest_bytes=manifest_bytes,
    )

    cursor = store.read_cursor()
    assert observed.database_revision == cursor.database_revision == 1
    assert observed.release_state_root == cursor.state_root
    assert observed.current_candidate_id == cursor.current_candidate_id
    assert observed.current_candidate_sha256 == cursor.current_candidate_sha256
    assert observed.current_release_revision == cursor.current_release_revision == 1
    assert observed.current_select_input_id == cursor.current_select_input_id
    assert observed.exact_candidate_bytes == candidate_bytes
    assert observed.release_authority is False
    assert observed.settlement_authority is False
    assert observed.production_authority is False


def test_exact_checker_runs_once_on_retained_candidate_bytes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, _, candidate_bytes, manifest_bytes = _fixture()
    store = _store_with_snapshot(monkeypatch, _snapshot(candidate_bytes))
    original = authority.check_exact_spot_v7_execution_authority_manifest_v1
    calls: list[tuple[bytes, bytes]] = []

    def counted(
        *,
        exact_release_candidate_bytes: bytes,
        exact_authority_manifest_bytes: bytes,
    ) -> authority.CheckedSpotV7ExecutionAuthorityManifestV1:
        calls.append((exact_release_candidate_bytes, exact_authority_manifest_bytes))
        return original(
            exact_release_candidate_bytes=exact_release_candidate_bytes,
            exact_authority_manifest_bytes=exact_authority_manifest_bytes,
        )

    monkeypatch.setattr(
        binding.authority,
        "check_exact_spot_v7_execution_authority_manifest_v1",
        counted,
    )
    binding.bind_current_release_to_execution_manifest_v1(
        store,
        exact_authority_manifest_bytes=manifest_bytes,
    )

    assert calls == [(candidate_bytes, manifest_bytes)]


@pytest.mark.parametrize(
    "mutate_snapshot",
    (
        lambda value: ("_current_candidate_id", _digest("wrong-candidate")),
        lambda value: ("_current_candidate_sha256", _digest("wrong-candidate-sha")),
        lambda value: ("_current_release_revision", value.current_release_revision + 1),
    ),
)
def test_locked_candidate_identity_substitution_rejects(
    monkeypatch: pytest.MonkeyPatch,
    mutate_snapshot: Callable[
        [store_v3._AuthorityNeutralCurrentReleaseSnapshotV1], tuple[str, object]
    ],
) -> None:
    _, _, candidate_bytes, manifest_bytes = _fixture()
    snapshot = _snapshot(candidate_bytes)
    field, substituted = mutate_snapshot(snapshot)
    object.__setattr__(snapshot, field, substituted)
    store = _store_with_snapshot(monkeypatch, snapshot)

    with pytest.raises(binding.SpotV7CurrentReleaseExecutionBindingRejectV1):
        binding.bind_current_release_to_execution_manifest_v1(
            store,
            exact_authority_manifest_bytes=manifest_bytes,
        )


def test_authority_manifest_substitution_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    _, _, candidate_bytes, manifest_bytes = _fixture()
    store = _store_with_snapshot(monkeypatch, _snapshot(candidate_bytes))
    substituted = bytearray(manifest_bytes)
    substituted[-2] ^= 1

    with pytest.raises(binding.SpotV7CurrentReleaseExecutionBindingRejectV1):
        binding.bind_current_release_to_execution_manifest_v1(
            store,
            exact_authority_manifest_bytes=bytes(substituted),
        )


def test_store_snapshot_failure_rejects(monkeypatch: pytest.MonkeyPatch) -> None:
    _, _, _, manifest_bytes = _fixture()

    def reject_snapshot(_self: object) -> None:
        raise store_v3.SpotV7AuthenticatedReleaseStateStoreErrorV3(
            "CURRENT_RELEASE_SNAPSHOT_FAILED",
            "current release is revoked",
        )

    monkeypatch.setattr(
        store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3,
        "_current_release_snapshot_for_execution_binding_v1",
        reject_snapshot,
    )
    store = object.__new__(store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3)

    with pytest.raises(binding.SpotV7CurrentReleaseExecutionBindingRejectV1) as captured:
        binding.bind_current_release_to_execution_manifest_v1(
            store,
            exact_authority_manifest_bytes=manifest_bytes,
        )
    assert captured.value.code == "CURRENT_RELEASE_SNAPSHOT_REJECTED"


def test_non_store_and_non_bytes_reject() -> None:
    with pytest.raises(TypeError):
        binding.bind_current_release_to_execution_manifest_v1(
            object(),  # type: ignore[arg-type]
            exact_authority_manifest_bytes=b"{}\n",
        )
    store = object.__new__(store_v3.SQLiteSpotV7AuthenticatedReleaseStateStoreV3)
    with pytest.raises(TypeError):
        binding.bind_current_release_to_execution_manifest_v1(
            store,
            exact_authority_manifest_bytes=cast(Any, bytearray(b"{}\n")),
        )


def test_output_is_immutable_noncopyable_and_nonserializable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, _, candidate_bytes, manifest_bytes = _fixture()
    observed = binding.bind_current_release_to_execution_manifest_v1(
        _store_with_snapshot(monkeypatch, _snapshot(candidate_bytes)),
        exact_authority_manifest_bytes=manifest_bytes,
    )

    with pytest.raises(TypeError):
        observed.database_revision = 8  # type: ignore[misc]
    with pytest.raises(TypeError):
        copy.copy(observed)
    with pytest.raises(TypeError):
        copy.deepcopy(observed)
    with pytest.raises(TypeError):
        pickle.dumps(observed)


def test_same_interpreter_field_mutation_invalidates_every_data_projection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, _, candidate_bytes, manifest_bytes = _fixture()
    observed = binding.bind_current_release_to_execution_manifest_v1(
        _store_with_snapshot(monkeypatch, _snapshot(candidate_bytes)),
        exact_authority_manifest_bytes=manifest_bytes,
    )
    object.__setattr__(observed, "_database_revision", 8)

    with pytest.raises(ValueError, match="observation was mutated"):
        _ = observed.database_revision
    with pytest.raises(ValueError, match="observation was mutated"):
        _ = observed.exact_candidate_bytes
    assert observed.release_authority is False
    assert observed.settlement_authority is False
    assert observed.production_authority is False


def test_nominal_checked_descriptor_is_not_an_input_surface() -> None:
    parameters = inspect.signature(binding.bind_current_release_to_execution_manifest_v1).parameters
    assert tuple(parameters) == ("store", "exact_authority_manifest_bytes")
    assert "checked_manifest" not in parameters


def test_same_interpreter_forge_cannot_promote_authority() -> None:
    candidate_bytes = b"forged-candidate"
    manifest_bytes = b"forged-manifest"
    forged = binding._AuthorityNeutralCurrentReleaseExecutionBindingV1._from_checked(
        store_identity_sha256=_digest("store"),
        database_revision=1,
        last_evaluation_epoch=1,
        release_state_root=_digest("state"),
        current_candidate_id=_digest("candidate"),
        current_candidate_sha256=hashlib.sha256(candidate_bytes).digest(),
        current_release_revision=1,
        current_select_input_id=_digest("select"),
        current_revocation_record_id=None,
        exact_candidate_bytes=candidate_bytes,
        exact_authority_manifest_bytes=manifest_bytes,
        execution_authority_manifest_sha256=hashlib.sha256(manifest_bytes).digest(),
        seal=binding._CURRENT_RELEASE_EXECUTION_BINDING_SEAL_V1,
    )

    assert forged.currentness_at_settlement_established is False
    assert forged.atomic_release_and_settlement_commit_established is False
    assert forged.external_monotonic_rollback_resistance_established is False
    assert forged.hostile_same_interpreter_resistance_established is False
    assert forged.proof_receipt_authority is False
    assert forged.runtime_authority is False
    assert forged.release_authority is False
    assert forged.settlement_authority is False
    assert forged.production_authority is False
