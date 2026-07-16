from __future__ import annotations

import copy
import hashlib
import json
import pickle
from pathlib import Path
from typing import Any, cast

import pytest

from src.integration import _zrpf_spot_v7_authenticated_proof_v1 as proof_v1
from src.integration import _zrpf_spot_v7_release_bound_proof_v1 as join_v1
from src.integration import _zrpf_spot_v7_release_state_engine_v7 as release_v7
from tests import test_zrpf_spot_v7_authenticated_release_selection_store_v2 as v2_fx
from tests import test_zrpf_spot_v7_execution_authority_manifest_v1 as authority_fx
from tests.integration import test_zrpf_spot_v7_authenticated_proof_v1 as proof_fx
from tests.test_zrpf_spot_v7_release_store_cutover_v1 import _cutover_selected_store
from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority_v1
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate_v1
from tools import zrpf_spot_v7_release_store_cutover_v1 as cutover_v1


class _JoinFixture:
    def __init__(self, monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
        self.proof = proof_fx._fixture()
        self.proof.application_id = join_v1._derive_release_scope_id_v1(
            b"zenodex.zrpf.application_id.v3",
            "zenodex",
        )
        self.proof.chain_or_domain_id = join_v1._derive_release_scope_id_v1(
            b"zenodex.zrpf.chain_or_domain_id.v3",
            "spot-domain-271828",
        )
        self.proof.response = proof_fx._response(self.proof)
        (
            self.candidate,
            self.execution_authority_manifest,
            self.proof_verifier_manifest,
        ) = _selected_candidate_material(self.proof)
        monkeypatch.setattr(
            v2_fx,
            "_candidate_with_static_policies",
            lambda **_kwargs: self.candidate,
        )
        (
            self.store,
            _selection,
            _revocation,
            self.destination,
            _watermark,
        ) = _cutover_selected_store(tmp_path)
        monkeypatch.setattr(
            proof_v1,
            "execute_pinned_verifier_once",
            lambda **_kwargs: self.proof.response,
        )
        verifier = proof_v1.PinnedSpotV7SemanticProofVerifierV1(
            executable=Path("/governed/spot-v7-proof-verifier"),
            authority_manifest_json=self.proof_verifier_manifest,
            authority_manifest_sha256=hashlib.sha256(self.proof_verifier_manifest).hexdigest(),
        )
        self.observation = verifier.verify(
            v7_receipt=self.proof.v7_receipt,
            guest_input=self.proof.guest_input,
            source_v6_receipt=self.proof.source_v6_receipt,
        )
        self.connection = cutover_v1.open_unified_release_store_v7_for_maintenance_v1(
            self.destination,
            identity=self.store.identity,
        )
        self.connection.execute("BEGIN IMMEDIATE")
        self.release = release_v7._current_release_for_atomic_join_locked_v7(
            self.connection,
            identity=self.store.identity,
        )

    def bind(self) -> join_v1._ReleaseBoundSpotV7SemanticProofV1:
        return join_v1._bind_release_locked_spot_v7_semantic_proof_v1(
            self.connection,
            identity=self.store.identity,
            release=self.release,
            observation=self.observation,
            exact_execution_authority_manifest_bytes=self.execution_authority_manifest,
            exact_proof_verifier_manifest_bytes=self.proof_verifier_manifest,
        )

    def close(self) -> None:
        if self.connection.in_transaction:
            self.connection.rollback()
        self.connection.close()


def _selected_candidate_material(
    proof: proof_fx._Fixture,
) -> tuple[
    candidate_v1.SpotV7ReleaseCandidateManifestV1,
    bytes,
    bytes,
]:
    candidate_body = authority_fx._candidate_body()
    lineage = cast(dict[str, Any], candidate_body["lineage"])
    lineage.update(
        {
            "minimum_rollback_revision": 1,
            "parent_candidate_id": None,
            "proposed_activation_epoch": 0,
            "proposed_expiration_epoch": None,
            "release_revision": 1,
        }
    )
    proof_verifier_manifest = proof_fx._authority_manifest(proof)
    verifier_digest = hashlib.sha256(proof_verifier_manifest).hexdigest()
    verifier_row = authority_fx._inventory_row(candidate_body, "verifier_manifest")
    verifier_row.update(
        {
            "artifact_sha256": verifier_digest,
            "bound_identity": verifier_digest,
            "size_bytes": len(proof_verifier_manifest),
        }
    )
    cast(dict[str, Any], candidate_body["manifests"])["verifier_manifest_sha256"] = verifier_digest
    authority_body = authority_fx._authority_body(candidate_body)
    cast(dict[str, Any], authority_body["artifacts"])["proof_verifier_executable_sha256"] = (
        proof.executable_sha256
    )
    execution_authority_manifest = authority_v1.recompose_spot_v7_execution_authority_manifest_v1(
        authority_body
    )
    authority_digest = hashlib.sha256(execution_authority_manifest).hexdigest()
    authority_row = authority_fx._inventory_row(candidate_body, "authority_manifest")
    authority_row.update(
        {
            "artifact_sha256": authority_digest,
            "bound_identity": authority_digest,
            "size_bytes": len(execution_authority_manifest),
        }
    )
    cast(dict[str, Any], candidate_body["manifests"])["authority_manifest_sha256"] = (
        authority_digest
    )
    candidate_bytes = candidate_v1.recompose_spot_v7_release_candidate_manifest_v1(candidate_body)
    candidate = candidate_v1.parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes)
    return candidate, execution_authority_manifest, proof_verifier_manifest


def test_release_bound_proof_binds_selected_manifests_and_exact_plan(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path)
    try:
        proof = fixture.bind()
        assert proof.release_candidate_id == fixture.release.current_candidate_id
        assert proof.release_candidate_sha256 == fixture.release.current_candidate_sha256
        assert proof.release_revision == 1
        assert proof.exact_plan_b_bytes == fixture.proof.plan
        assert proof.exact_plan_b_sha256 == hashlib.sha256(fixture.proof.plan).digest()
        assert proof.settlement_effect_plan_commitment == bytes.fromhex(
            fixture.proof.plan_commitment
        )
        assert (
            proof.proof_verifier_manifest_sha256
            == hashlib.sha256(fixture.proof_verifier_manifest).digest()
        )
        assert proof.proof_verifier_executable_sha256 == bytes.fromhex(
            fixture.proof.executable_sha256
        )
        assert proof.release_governed_verifier_identity_verified is True
        assert proof.proof_receipt_authority is True
        assert proof.external_monotonic_anchor_authenticated is False
        assert proof.finality_verified is False
        assert proof.hostile_same_interpreter_resistance_established is False
        assert proof.release_authority is False
        assert proof.settlement_authority is False
        assert proof.production_authority is False
        assert not hasattr(proof, "asset_effects_root")
        assert (
            join_v1._require_release_bound_proof_still_locked_v1(
                fixture.connection,
                identity=fixture.store.identity,
                proof=proof,
            )
            is proof
        )
        with pytest.raises(TypeError, match="verified private construction"):
            type(proof)()
        with pytest.raises(TypeError, match="immutable"):
            proof._release_revision = 2
        with pytest.raises(TypeError, match="cannot be copied"):
            copy.copy(proof)
        with pytest.raises(TypeError, match="cannot be deep-copied"):
            copy.deepcopy(proof)
        with pytest.raises(TypeError, match="cannot be serialized"):
            pickle.dumps(proof)
    finally:
        fixture.close()


def test_caller_selected_verifier_and_manifest_substitution_reject(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path)
    try:
        alternate_manifest_document = cast(
            dict[str, Any], json.loads(fixture.proof_verifier_manifest)
        )
        alternate_manifest_document["executable_sha256"] = hashlib.sha256(
            b"caller-selected-verifier"
        ).hexdigest()
        alternate_manifest = proof_v1.canonical_json_bytes(alternate_manifest_document)
        with pytest.raises(
            join_v1.SpotV7ReleaseBoundProofRejectV1,
            match="VERIFIER_MANIFEST_BINDING",
        ):
            join_v1._bind_release_locked_spot_v7_semantic_proof_v1(
                fixture.connection,
                identity=fixture.store.identity,
                release=fixture.release,
                observation=fixture.observation,
                exact_execution_authority_manifest_bytes=(fixture.execution_authority_manifest),
                exact_proof_verifier_manifest_bytes=alternate_manifest,
            )

        alternate_verifier = proof_v1.PinnedSpotV7SemanticProofVerifierV1(
            executable=Path("/caller/selected/spot-v7-proof-verifier"),
            authority_manifest_json=alternate_manifest,
            authority_manifest_sha256=hashlib.sha256(alternate_manifest).hexdigest(),
        )
        alternate_observation = alternate_verifier.verify(
            v7_receipt=fixture.proof.v7_receipt,
            guest_input=fixture.proof.guest_input,
            source_v6_receipt=fixture.proof.source_v6_receipt,
        )
        with pytest.raises(
            join_v1.SpotV7ReleaseBoundProofRejectV1,
            match="PROOF_OBSERVATION_BINDING",
        ):
            join_v1._bind_release_locked_spot_v7_semantic_proof_v1(
                fixture.connection,
                identity=fixture.store.identity,
                release=fixture.release,
                observation=alternate_observation,
                exact_execution_authority_manifest_bytes=(fixture.execution_authority_manifest),
                exact_proof_verifier_manifest_bytes=fixture.proof_verifier_manifest,
            )
    finally:
        fixture.close()


def test_stale_transaction_rejects_join_and_capability_reuse(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path)
    proof = fixture.bind()
    fixture.connection.rollback()
    with pytest.raises(release_v7.SpotV7ReleaseStateEngineRejectV7, match="TRANSACTION_ENDED"):
        fixture.bind()
    with pytest.raises(release_v7.SpotV7ReleaseStateEngineRejectV7, match="TRANSACTION_ENDED"):
        join_v1._require_release_bound_proof_still_locked_v1(
            fixture.connection,
            identity=fixture.store.identity,
            proof=proof,
        )
    fixture.connection.close()


def test_retained_plan_binding_drift_rejects_before_atomic_join(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path)
    try:
        proof = fixture.bind()
        object.__setattr__(proof, "_exact_plan_b_bytes", b"forged-plan")
        with pytest.raises(ValueError, match="retained binding drift"):
            join_v1._require_release_bound_proof_still_locked_v1(
                fixture.connection,
                identity=fixture.store.identity,
                proof=proof,
            )
    finally:
        fixture.close()


def test_candidate_authority_manifest_mismatch_rejects(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path)
    try:
        mutated = bytearray(fixture.execution_authority_manifest)
        mutated[-2] ^= 1
        with pytest.raises(
            join_v1.SpotV7ReleaseBoundProofRejectV1,
            match="EXECUTION_AUTHORITY_MANIFEST",
        ):
            join_v1._bind_release_locked_spot_v7_semantic_proof_v1(
                fixture.connection,
                identity=fixture.store.identity,
                release=fixture.release,
                observation=fixture.observation,
                exact_execution_authority_manifest_bytes=bytes(mutated),
                exact_proof_verifier_manifest_bytes=fixture.proof_verifier_manifest,
            )
    finally:
        fixture.close()


def test_forged_nominal_inputs_and_unbound_asset_root_cannot_cross_join(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path)
    try:
        for forged_release in (True, {"verified": True}, object()):
            with pytest.raises(TypeError, match="transaction-bound release"):
                join_v1._bind_release_locked_spot_v7_semantic_proof_v1(
                    fixture.connection,
                    identity=fixture.store.identity,
                    release=cast(
                        release_v7._TransactionBoundSpotV7CurrentReleaseV7,
                        forged_release,
                    ),
                    observation=fixture.observation,
                    exact_execution_authority_manifest_bytes=(fixture.execution_authority_manifest),
                    exact_proof_verifier_manifest_bytes=fixture.proof_verifier_manifest,
                )
        for forged_observation in (True, {"verified": True}, object()):
            with pytest.raises(TypeError, match="pinned proof observation"):
                join_v1._bind_release_locked_spot_v7_semantic_proof_v1(
                    fixture.connection,
                    identity=fixture.store.identity,
                    release=fixture.release,
                    observation=cast(
                        proof_v1._PinnedSpotV7SemanticProofObservationV1,
                        forged_observation,
                    ),
                    exact_execution_authority_manifest_bytes=(fixture.execution_authority_manifest),
                    exact_proof_verifier_manifest_bytes=fixture.proof_verifier_manifest,
                )
        with pytest.raises(TypeError, match="unexpected keyword"):
            cast(Any, join_v1._bind_release_locked_spot_v7_semantic_proof_v1)(
                fixture.connection,
                identity=fixture.store.identity,
                release=fixture.release,
                observation=fixture.observation,
                exact_execution_authority_manifest_bytes=(fixture.execution_authority_manifest),
                exact_proof_verifier_manifest_bytes=fixture.proof_verifier_manifest,
                asset_effects_root=bytes.fromhex("ab" * 32),
            )
    finally:
        fixture.close()
