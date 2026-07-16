"""CBC tests for transaction-locked release binding of Spot V7 DA."""

from __future__ import annotations

import copy
import hashlib
import pickle
from dataclasses import replace
from pathlib import Path
from typing import Any, cast

import pytest

from src.integration import _zrpf_spot_v7_release_bound_da_v1 as join_v1
from src.integration import _zrpf_spot_v7_release_state_engine_v7 as release_v7
from src.integration.zeno_ledger_v0 import canonical_json_bytes_v0
from src.integration.zrpf_sampled_retrievability_v1 import (
    build_sampled_response_ledger_inclusion_record_v1,
)
from src.integration.zrpf_spot_v7_finalized_da_response_inclusion import (
    bind_finalized_sampled_response_inclusion_v1,
)
from src.integration.zrpf_spot_v7_governed_da_prerequisite_v2 import (
    _bind_governed_spot_v7_da_prerequisite_v2,
)
from src.integration.zrpf_spot_v7_zeno_ledger_finality_adapter import (
    _AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    _AuthenticatedExactCheckpointFinalityTransitionV3,
)
from tests import test_zrpf_spot_v7_authenticated_release_selection_store_v2 as v2_fx
from tests import test_zrpf_spot_v7_execution_authority_manifest_v1 as authority_fx
from tests.integration import test_zrpf_spot_v7_finalized_da_response_inclusion as inclusion_fx
from tests.integration import test_zrpf_spot_v7_governed_da_prerequisite_v2 as da_fx
from tests.test_zrpf_spot_v7_release_store_cutover_v1 import _cutover_selected_store
from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority_v1
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate_v1
from tools import zrpf_spot_v7_release_store_cutover_v1 as cutover_v1


class _DaJoinFixture:
    def __init__(
        self,
        monkeypatch: pytest.MonkeyPatch,
        tmp_path: Path,
        *,
        wrong_release_da_policy: bool = False,
        wrong_release_operational_policy: bool = False,
    ) -> None:
        (
            self.policy,
            _beacon,
            self.sampled,
            governed_sample,
            self.full_blob,
        ) = da_fx._valid()
        self.governed_da = _bind_governed_spot_v7_da_prerequisite_v2(
            operational_policy=self.policy,
            exact_full_blob=self.full_blob,
            governed_sampled_response=governed_sample,
        )
        inclusion_height = self.sampled.checked_epoch + 1
        record = build_sampled_response_ledger_inclusion_record_v1(
            self.sampled.exact_evidence_bytes,
            zeno_ledger_chain_id=self.policy._projection.zeno_ledger_chain_id,
            inclusion_height=inclusion_height,
        )
        self.body = inclusion_fx._body(
            record,
            height=inclusion_height,
            chain_id=self.policy._projection.zeno_ledger_chain_id,
        )
        base_finality = inclusion_fx._finality(sampled=self.sampled, body=self.body)
        finality = _AuthenticatedExactCheckpointFinalityTransitionV3(
            replace(
                base_finality._projection,
                policy_root=self.policy._projection.checkpoint_finality_policy_root,
            ),
            exact_certificate_bytes=base_finality._exact_certificate_bytes,
            exact_finality_evidence_bytes=base_finality._exact_finality_evidence_bytes,
            seal=_AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
        )
        self.inclusion = bind_finalized_sampled_response_inclusion_v1(
            sampled_response=self.sampled,
            checkpoint_finality=finality,
            exact_body_bytes=canonical_json_bytes_v0(self.body),
        )
        self.candidate, self.execution_authority_manifest = _selected_candidate_material(
            policy=self.policy,
            wrong_da_policy=wrong_release_da_policy,
            wrong_operational_policy=wrong_release_operational_policy,
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

    def bind(self) -> join_v1._ReleaseBoundSpotV7DataAvailabilityV1:
        return join_v1._bind_release_locked_spot_v7_da_v1(
            self.connection,
            identity=self.store.identity,
            release=self.release,
            operational_policy=self.policy,
            governed_da=self.governed_da,
            finalized_inclusion=self.inclusion,
            exact_execution_authority_manifest_bytes=(self.execution_authority_manifest),
        )

    def close(self) -> None:
        if self.connection.in_transaction:
            self.connection.rollback()
        self.connection.close()


def _selected_candidate_material(
    *,
    policy: object,
    wrong_da_policy: bool,
    wrong_operational_policy: bool,
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
    release_da_policy_root = join_v1._derive_release_da_policy_root_v1(policy).hex()
    operational_policy_root = policy._provenance.manifest_sha256  # type: ignore[attr-defined]
    if wrong_da_policy:
        release_da_policy_root = hashlib.sha256(b"wrong-release-da-policy").hexdigest()
    if wrong_operational_policy:
        operational_policy_root = hashlib.sha256(b"wrong-operational-policy").hexdigest()
    policy_projection = policy._projection_for_governed_da_v2()  # type: ignore[attr-defined]
    roots = {
        "data_availability_policy": release_da_policy_root,
        "finality_policy": policy_projection.checkpoint_finality_policy_root[2:],
        "operational_policy": operational_policy_root,
    }
    policies = cast(dict[str, Any], candidate_body["policies"])
    for role, root in roots.items():
        policies[f"{role}_root"] = root
        authority_fx._inventory_row(candidate_body, role)["bound_identity"] = root

    authority_body = authority_fx._authority_body(candidate_body)
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


def test_release_bound_da_binds_exact_content_timing_policy_and_release(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture = _DaJoinFixture(monkeypatch, tmp_path)
    try:
        result = fixture.bind()
        da_projection = fixture.governed_da._projection_for_downstream_binding_v2()
        inclusion = fixture.inclusion._projection_for_da_store_v5()

        assert result.release_candidate_id == fixture.release.current_candidate_id
        assert result.release_candidate_sha256 == fixture.release.current_candidate_sha256
        assert result.release_revision == 1
        assert result.policy_root == join_v1._derive_release_da_policy_root_v1(fixture.policy)
        assert result.full_blob_certificate_root == bytes.fromhex(
            da_projection.base.certificate_root[2:]
        )
        assert result.data_root == bytes.fromhex(da_projection.base.data_root[2:])
        assert result.exact_blob_sha256 == bytes.fromhex(
            da_projection.base.exact_blob_sha256[2:]
        )
        assert result.sampled_evidence_sha256 == bytes.fromhex(
            da_projection.base.sampled_evidence_sha256
        )
        assert result.finalized_inclusion_epoch == inclusion.inclusion_height
        assert result.finalized_inclusion_body_root == bytes.fromhex(
            inclusion.finalized_body_root[2:]
        )
        assert result.finalized_inclusion_proof_root == bytes.fromhex(
            inclusion.inclusion_record_root[2:]
        )
        assert result.exact_certificate_bytes == fixture.full_blob._exact_certificate_bytes
        assert result.exact_sampled_evidence_bytes == fixture.sampled.exact_evidence_bytes
        assert result.exact_inclusion_body_bytes == canonical_json_bytes_v0(fixture.body)
        assert result.release_governed_da_policy_identity_verified is True
        assert result.governed_exact_full_blob_policy_satisfied is True
        assert result.finalized_sampled_evidence_digest_included_by_deadline is True
        assert result.response_timing_provenance_verified is True
        assert result.provider_response_generation_time_verified is False
        assert result.provider_independence_verified is False
        assert result.continuous_availability_verified is False
        assert result.public_future_availability_verified is False
        assert result.external_monotonic_release_anchor_authenticated is False
        assert result.hostile_same_interpreter_resistance_established is False
        assert result.release_authority is False
        assert result.settlement_authority is False
        assert result.production_authority is False
        assert (
            join_v1._require_release_bound_da_still_locked_v1(
                fixture.connection,
                identity=fixture.store.identity,
                data_availability=result,
            )
            is result
        )
    finally:
        fixture.close()


@pytest.mark.parametrize(
    ("wrong_da_policy", "wrong_operational_policy", "code"),
    (
        (True, False, "DA_POLICY_BINDING"),
        (False, True, "OPERATIONAL_POLICY_BINDING"),
    ),
)
def test_release_policy_substitution_rejects(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    wrong_da_policy: bool,
    wrong_operational_policy: bool,
    code: str,
) -> None:
    fixture = _DaJoinFixture(
        monkeypatch,
        tmp_path,
        wrong_release_da_policy=wrong_da_policy,
        wrong_release_operational_policy=wrong_operational_policy,
    )
    try:
        with pytest.raises(join_v1.SpotV7ReleaseBoundDaRejectV1, match=code):
            fixture.bind()
    finally:
        fixture.close()


def test_retained_blob_or_inclusion_drift_rejects(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture = _DaJoinFixture(monkeypatch, tmp_path)
    try:
        result = fixture.bind()
        original_blob = fixture.full_blob._exact_blob_bytes
        object.__setattr__(fixture.full_blob, "_exact_blob_bytes", b"forged-blob")
        with pytest.raises((ValueError, join_v1.SpotV7ReleaseBoundDaRejectV1)):
            join_v1._require_release_bound_da_still_locked_v1(
                fixture.connection,
                identity=fixture.store.identity,
                data_availability=result,
            )
        object.__setattr__(fixture.full_blob, "_exact_blob_bytes", original_blob)

        second = fixture.bind()
        object.__setattr__(fixture.inclusion, "_exact_body_bytes", b"{}")
        with pytest.raises((ValueError, join_v1.SpotV7ReleaseBoundDaRejectV1)):
            join_v1._require_release_bound_da_still_locked_v1(
                fixture.connection,
                identity=fixture.store.identity,
                data_availability=second,
            )
    finally:
        fixture.close()


def test_raw_nominal_values_and_transfer_attempts_reject(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture = _DaJoinFixture(monkeypatch, tmp_path)
    try:
        with pytest.raises(TypeError, match="exact governed DA V2"):
            join_v1._bind_release_locked_spot_v7_da_v1(
                fixture.connection,
                identity=fixture.store.identity,
                release=fixture.release,
                operational_policy=fixture.policy,
                governed_da={"verified": True},
                finalized_inclusion=fixture.inclusion,
                exact_execution_authority_manifest_bytes=(
                    fixture.execution_authority_manifest
                ),
            )
        with pytest.raises(TypeError, match="exact finalized inclusion"):
            join_v1._bind_release_locked_spot_v7_da_v1(
                fixture.connection,
                identity=fixture.store.identity,
                release=fixture.release,
                operational_policy=fixture.policy,
                governed_da=fixture.governed_da,
                finalized_inclusion={"finalized": True},
                exact_execution_authority_manifest_bytes=(
                    fixture.execution_authority_manifest
                ),
            )

        result = fixture.bind()
        with pytest.raises(TypeError, match="verified private construction"):
            type(result)()
        with pytest.raises(TypeError, match="immutable"):
            result._release_revision = 2
        with pytest.raises(TypeError, match="cannot be copied"):
            copy.copy(result)
        with pytest.raises(TypeError, match="cannot be deep-copied"):
            copy.deepcopy(result)
        with pytest.raises(TypeError, match="cannot be serialized"):
            pickle.dumps(result)
    finally:
        fixture.close()


def test_release_bound_da_cannot_escape_its_write_transaction(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    fixture = _DaJoinFixture(monkeypatch, tmp_path)
    try:
        result = fixture.bind()
        fixture.connection.rollback()
        with pytest.raises(ValueError, match="transaction"):
            join_v1._require_release_bound_da_still_locked_v1(
                fixture.connection,
                identity=fixture.store.identity,
                data_availability=result,
            )
    finally:
        fixture.close()
