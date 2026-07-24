from __future__ import annotations

import copy
import hashlib
import json
import pickle
from pathlib import Path
from typing import Any, cast

import pytest

from src.integration import _zrpf_spot_v7_release_bound_finality_v1 as join_v1
from src.integration import _zrpf_spot_v7_release_state_engine_v7 as release_v7
from src.integration import zrpf_spot_v7_checkpoint_finality_checker_adapter as finality_v1
from tests import test_zrpf_spot_v7_authenticated_release_selection_store_v2 as v2_fx
from tests import test_zrpf_spot_v7_execution_authority_manifest_v1 as authority_fx
from tests.integration import test_zrpf_spot_v7_checkpoint_finality_checker_adapter as finality_fx
from tests.test_zrpf_spot_v7_release_store_cutover_v1 import _cutover_selected_store
from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority_v1
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate_v1
from tools import zrpf_spot_v7_release_store_cutover_v1 as cutover_v1


class _FinalityJoinFixture:
    def __init__(
        self,
        monkeypatch: pytest.MonkeyPatch,
        tmp_path: Path,
        rust_checker: Path,
    ) -> None:
        self.policy = finality_fx._governed_policy()
        authenticated = finality_fx._authenticated_finality(self.policy)
        self.checker_manifest = finality_fx._manifest(rust_checker)
        self.cross_checked = finality_fx._checker(rust_checker).cross_check_authenticated(
            policy=self.policy,
            finality=authenticated,
        )
        (
            self.candidate,
            self.execution_authority_manifest,
        ) = _selected_candidate_material(
            policy=self.policy,
            checker_manifest=self.checker_manifest,
            checker_executable_sha256=hashlib.sha256(rust_checker.read_bytes()).hexdigest(),
        )
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
        self.connection = cutover_v1.open_unified_release_store_v7_for_maintenance_v1(
            self.destination,
            identity=self.store.identity,
        )
        self.connection.execute("BEGIN IMMEDIATE")
        self.release = release_v7._current_release_for_atomic_join_locked_v7(
            self.connection,
            identity=self.store.identity,
        )

    def bind(self) -> join_v1._ReleaseBoundSpotV7CheckpointFinalityV1:
        return join_v1._bind_release_locked_spot_v7_checkpoint_finality_v1(
            self.connection,
            identity=self.store.identity,
            release=self.release,
            finality=self.cross_checked,
            exact_execution_authority_manifest_bytes=(self.execution_authority_manifest),
        )

    def close(self) -> None:
        if self.connection.in_transaction:
            self.connection.rollback()
        self.connection.close()


def _selected_candidate_material(
    *,
    policy: object,
    checker_manifest: bytes,
    checker_executable_sha256: str,
) -> tuple[candidate_v1.SpotV7ReleaseCandidateManifestV1, bytes]:
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
    projection = policy._projection_for_governed_da_v2()  # type: ignore[attr-defined]
    provenance = policy._provenance_for_governed_da_v2()  # type: ignore[attr-defined]
    finality_policy_root = projection.checkpoint_finality_policy_root[2:]
    operational_policy_root = provenance.manifest_sha256
    policies = cast(dict[str, Any], candidate_body["policies"])
    policies["finality_policy_root"] = finality_policy_root
    policies["operational_policy_root"] = operational_policy_root
    authority_fx._inventory_row(candidate_body, "finality_policy")["bound_identity"] = (
        finality_policy_root
    )
    authority_fx._inventory_row(candidate_body, "operational_policy")["bound_identity"] = (
        operational_policy_root
    )

    authority_body = authority_fx._authority_body(candidate_body)
    artifacts = cast(dict[str, Any], authority_body["artifacts"])
    artifacts["checkpoint_finality_checker_executable_sha256"] = checker_executable_sha256
    artifacts["checkpoint_finality_checker_manifest_sha256"] = hashlib.sha256(
        checker_manifest
    ).hexdigest()
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
    return (
        candidate_v1.parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes),
        execution_authority_manifest,
    )


def test_release_bound_finality_binds_checker_policy_and_checkpoint(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    rust_checker: Path,
) -> None:
    fixture = _FinalityJoinFixture(monkeypatch, tmp_path, rust_checker)
    try:
        result = fixture.bind()
        projection = fixture.cross_checked._finality._projection
        assert result.release_candidate_id == fixture.release.current_candidate_id
        assert result.release_candidate_sha256 == fixture.release.current_candidate_sha256
        assert result.release_revision == 1
        assert result.epoch_id == projection.epoch_id
        assert result.proof_journal_hash == bytes.fromhex(projection.proof_journal_hash[2:])
        assert result.post_state_root == bytes.fromhex(projection.post_state_root[2:])
        assert result.certificate_root == bytes.fromhex(projection.certificate_root[2:])
        assert result.finality_policy_root == bytes.fromhex(projection.policy_root[2:])
        assert result.checker_manifest_sha256 == hashlib.sha256(fixture.checker_manifest).digest()
        assert result.release_governed_checker_identity_verified is True
        assert result.checkpoint_finality_authenticated is True
        assert result.external_monotonic_release_anchor_authenticated is False
        assert result.hostile_same_interpreter_resistance_established is False
        assert result.release_authority is False
        assert result.settlement_authority is False
        assert result.production_authority is False
        assert (
            join_v1._require_release_bound_finality_still_locked_v1(
                fixture.connection,
                identity=fixture.store.identity,
                finality=result,
            )
            is result
        )
        with pytest.raises(TypeError, match="verified private construction"):
            type(result)()
        with pytest.raises(TypeError, match="immutable"):
            result._epoch_id = 99
        with pytest.raises(TypeError, match="cannot be copied"):
            copy.copy(result)
        with pytest.raises(TypeError, match="cannot be deep-copied"):
            copy.deepcopy(result)
        with pytest.raises(TypeError, match="cannot be serialized"):
            pickle.dumps(result)
    finally:
        fixture.close()


def test_caller_selected_checker_rejects_release_binding(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    rust_checker: Path,
) -> None:
    fixture = _FinalityJoinFixture(monkeypatch, tmp_path, rust_checker)
    alternate = tmp_path / "alternate-checkpoint-finality-checker"
    alternate.write_bytes(rust_checker.read_bytes() + b"\x00")
    alternate.chmod(0o555)
    try:
        alternate_finality = finality_fx._checker(alternate).cross_check_authenticated(
            policy=fixture.policy,
            finality=finality_fx._authenticated_finality(fixture.policy),
        )
        with pytest.raises(
            join_v1.SpotV7ReleaseBoundFinalityRejectV1,
            match="CHECKER_MANIFEST_BINDING",
        ):
            join_v1._bind_release_locked_spot_v7_checkpoint_finality_v1(
                fixture.connection,
                identity=fixture.store.identity,
                release=fixture.release,
                finality=alternate_finality,
                exact_execution_authority_manifest_bytes=(fixture.execution_authority_manifest),
            )
    finally:
        fixture.close()


def test_authority_manifest_substitution_rejects(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    rust_checker: Path,
) -> None:
    fixture = _FinalityJoinFixture(monkeypatch, tmp_path, rust_checker)
    try:
        mutated_body = cast(
            dict[str, Any],
            json.loads(fixture.execution_authority_manifest),
        )
        cast(dict[str, Any], mutated_body["artifacts"])[
            "checkpoint_finality_checker_executable_sha256"
        ] = "cd" * 32
        mutated = authority_v1.recompose_spot_v7_execution_authority_manifest_v1(mutated_body)
        with pytest.raises(
            join_v1.SpotV7ReleaseBoundFinalityRejectV1,
            match="EXECUTION_AUTHORITY_MANIFEST",
        ):
            join_v1._bind_release_locked_spot_v7_checkpoint_finality_v1(
                fixture.connection,
                identity=fixture.store.identity,
                release=fixture.release,
                finality=fixture.cross_checked,
                exact_execution_authority_manifest_bytes=mutated,
            )
    finally:
        fixture.close()


def test_transaction_end_nominal_forgery_and_retained_tamper_reject(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    rust_checker: Path,
) -> None:
    fixture = _FinalityJoinFixture(monkeypatch, tmp_path, rust_checker)
    result = fixture.bind()
    with pytest.raises(TypeError, match="exact cross-checked finality"):
        join_v1._bind_release_locked_spot_v7_checkpoint_finality_v1(
            fixture.connection,
            identity=fixture.store.identity,
            release=fixture.release,
            finality=cast(
                finality_v1._CrossCheckedAuthenticatedCheckpointFinalityTransitionV1,
                {"verified": True},
            ),
            exact_execution_authority_manifest_bytes=(fixture.execution_authority_manifest),
        )
    object.__setattr__(result, "_checker_manifest_sha256", bytes.fromhex("aa" * 32))
    with pytest.raises(ValueError, match="binding drift"):
        join_v1._require_release_bound_finality_still_locked_v1(
            fixture.connection,
            identity=fixture.store.identity,
            finality=result,
        )
    fixture.connection.rollback()
    with pytest.raises(release_v7.SpotV7ReleaseStateEngineRejectV7):
        fixture.bind()
    fixture.connection.close()


@pytest.fixture(scope="session")
def rust_checker(tmp_path_factory: pytest.TempPathFactory) -> Path:
    target = tmp_path_factory.mktemp("release-bound-finality-rust-target")
    return finality_fx._build_rust_checker(target)
