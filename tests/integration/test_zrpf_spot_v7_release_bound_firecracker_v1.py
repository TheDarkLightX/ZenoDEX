from __future__ import annotations

import copy
import hashlib
import json
import pickle
import struct
from collections.abc import Callable
from pathlib import Path
from typing import Any, cast

import pytest

from src.integration import _zrpf_spot_v7_authenticated_proof_v1 as proof_adapter
from src.integration import _zrpf_spot_v7_release_bound_finality_v1 as finality_join
from src.integration import _zrpf_spot_v7_release_bound_firecracker_v1 as join_v1
from src.integration import _zrpf_spot_v7_release_bound_proof_v1 as proof_join
from src.integration import _zrpf_spot_v7_release_state_engine_v7 as release_v7
from tests import test_zrpf_spot_v7_authenticated_release_selection_store_v2 as v2_fx
from tests import test_zrpf_spot_v7_execution_authority_manifest_v1 as authority_fx
from tests.integration import test_zrpf_spot_v7_authenticated_proof_v1 as proof_fx
from tests.integration import (
    test_zrpf_spot_v7_checkpoint_finality_checker_adapter as finality_fx,
)
from tests.test_zrpf_spot_v7_firecracker_descriptor_staging import (
    _fixture as descriptor_fixture,
)
from tests.test_zrpf_spot_v7_firecracker_root_supervisor_candidate_policy_v1 import (
    _contract_document,
)
from tests.test_zrpf_spot_v7_release_store_cutover_v1 import _cutover_selected_store
from tools import zrpf_spot_v7_execution_authority_manifest_v1 as authority_v1
from tools import zrpf_spot_v7_firecracker_linux_runner as linux_runner
from tools import zrpf_spot_v7_firecracker_root_supervisor as supervisor_v1
from tools import zrpf_spot_v7_firecracker_root_supervisor_candidate_policy_v1 as policy_v1
from tools import zrpf_spot_v7_firecracker_runtime_manifest as runtime_v1
from tools import zrpf_spot_v7_firecracker_runtime_protocol as protocol_v1
from tools import zrpf_spot_v7_release_candidate_manifest_v1 as candidate_v1
from tools import zrpf_spot_v7_release_store_cutover_v1 as cutover_v1
from tools import zrpf_v3_firecracker_cgroup_v2 as cgroup_v1
from tools.zrpf_spot_v7_firecracker_authority_input import (
    SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1,
    build_authority_input_manifest_v1,
)


class _JoinFixture:
    def __init__(
        self,
        monkeypatch: pytest.MonkeyPatch,
        tmp_path: Path,
        rust_checker: Path,
    ) -> None:
        self.proof_data = proof_fx._fixture()
        self.proof_data.application_id = proof_join._derive_release_scope_id_v1(
            b"zenodex.zrpf.application_id.v3",
            "zenodex",
        )
        self.proof_data.chain_or_domain_id = proof_join._derive_release_scope_id_v1(
            b"zenodex.zrpf.chain_or_domain_id.v3",
            "spot-domain-271828",
        )
        self.proof_data.epoch_id = finality_fx.policy_test.POLICY_ACTIVATION_EPOCH
        self.proof_data.response = proof_fx._response(self.proof_data)
        self.operational_policy = finality_fx._governed_policy()
        self.authenticated_finality = _authenticated_finality(
            self.operational_policy,
            epoch_id=self.proof_data.epoch_id,
            proof_journal_hash=hashlib.sha256(self.proof_data.journal).digest(),
            post_state_root=bytes.fromhex(self.proof_data.post_state_root),
        )
        self.checker_manifest = finality_fx._manifest(rust_checker)
        self.cross_checked_finality = finality_fx._checker(
            rust_checker
        ).cross_check_authenticated(
            policy=self.operational_policy,
            finality=self.authenticated_finality,
        )
        self.proof_verifier_manifest = proof_fx._authority_manifest(self.proof_data)

        runtime_root = tmp_path / "runtime"
        runtime_root.mkdir(mode=0o700)
        descriptor = descriptor_fixture(runtime_root)
        base_runtime = runtime_v1.parse_exact_candidate_spot_v7_runtime_manifest_v1(
            descriptor.manifest,
            exact_machine_config_bytes=descriptor.config,
        )
        self.machine_config = descriptor.config
        self.runtime_manifest = runtime_v1.build_candidate_spot_v7_runtime_manifest_v1(
            exact_machine_config_bytes=self.machine_config,
            artifacts=base_runtime.artifacts,
            v7_image_id=struct.unpack("<8I", bytes.fromhex(self.proof_data.program_id)),
            v6_image_id=struct.unpack("<8I", bytes.fromhex(self.proof_data.source_program_id)),
        )
        self.runtime = runtime_v1.parse_exact_candidate_spot_v7_runtime_manifest_v1(
            self.runtime_manifest,
            exact_machine_config_bytes=self.machine_config,
        )
        self.runtime_artifact_manifest = _canonical(
            {
                "artifact_set_id": self.runtime.artifact_set_id.hex(),
                "schema": authority_v1.RUNTIME_ARTIFACT_MANIFEST_SCHEMA_V2,
            }
        )
        self.firecracker_profile = _canonical(
            {"schema": authority_v1.FIRECRACKER_REPLAY_PROFILE_SCHEMA_V1}
        )
        self.root_supervisor_contract = _canonical(
            _contract_document(
                runtime_manifest_sha256=hashlib.sha256(self.runtime_manifest).hexdigest(),
                firecracker_profile_sha256=hashlib.sha256(
                    self.firecracker_profile
                ).hexdigest(),
            )
        )
        self.root_supervisor_executable = b"governed-root-supervisor-static-elf-v1"
        self.settlement_intent = build_authority_input_manifest_v1(
            v7_image_id=self.runtime.v7_image_id,
            v6_image_id=self.runtime.v6_image_id,
            v7_receipt_bytes=self.proof_data.v7_receipt,
            guest_input_bytes=self.proof_data.guest_input,
            v6_receipt_bytes=self.proof_data.source_v6_receipt,
        )
        input_sha256 = next(
            row.sha256 for row in self.runtime.artifacts if row.role == "input"
        )
        self.request = protocol_v1.SpotV7FirecrackerRequestV1.validated(
            run_nonce_256=hashlib.sha256(b"release-bound-firecracker-run").digest(),
            runtime_manifest_sha256=hashlib.sha256(self.runtime_manifest).digest(),
            machine_config_sha256=hashlib.sha256(self.machine_config).digest(),
            input_drive_sha256=input_sha256,
            settlement_intent_sha256=hashlib.sha256(self.settlement_intent).digest(),
        ).encode()
        (
            self.candidate,
            self.execution_authority_manifest,
        ) = _selected_candidate_material(
            proof=self.proof_data,
            proof_verifier_manifest=self.proof_verifier_manifest,
            operational_policy=self.operational_policy,
            checker_manifest=self.checker_manifest,
            checker_executable_sha256=hashlib.sha256(rust_checker.read_bytes()).digest(),
            runtime=self.runtime,
            runtime_manifest=self.runtime_manifest,
            machine_config=self.machine_config,
            runtime_artifact_manifest=self.runtime_artifact_manifest,
            root_supervisor_contract=self.root_supervisor_contract,
            root_supervisor_executable=self.root_supervisor_executable,
            firecracker_profile=self.firecracker_profile,
        )
        monkeypatch.setattr(
            v2_fx,
            "_candidate_with_static_policies",
            lambda **_kwargs: self.candidate,
        )
        (
            self.store,
            _selection,
            self.revocation,
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

        monkeypatch.setattr(
            proof_adapter,
            "execute_pinned_verifier_once",
            lambda **_kwargs: self.proof_data.response,
        )
        verifier = proof_adapter.PinnedSpotV7SemanticProofVerifierV1(
            executable=Path("/governed/spot-v7-proof-verifier"),
            authority_manifest_json=self.proof_verifier_manifest,
            authority_manifest_sha256=hashlib.sha256(
                self.proof_verifier_manifest
            ).hexdigest(),
        )
        observation = verifier.verify(
            v7_receipt=self.proof_data.v7_receipt,
            guest_input=self.proof_data.guest_input,
            source_v6_receipt=self.proof_data.source_v6_receipt,
        )
        self.proof = proof_join._bind_release_locked_spot_v7_semantic_proof_v1(
            self.connection,
            identity=self.store.identity,
            release=self.release,
            observation=observation,
            exact_execution_authority_manifest_bytes=(self.execution_authority_manifest),
            exact_proof_verifier_manifest_bytes=self.proof_verifier_manifest,
        )
        self.finality = finality_join._bind_release_locked_spot_v7_checkpoint_finality_v1(
            self.connection,
            identity=self.store.identity,
            release=self.release,
            finality=self.cross_checked_finality,
            exact_execution_authority_manifest_bytes=(self.execution_authority_manifest),
        )
        self.execution = _candidate_bound_execution(
            candidate=self.candidate,
            runtime=self.runtime,
            request=self.request,
            payload=self.proof_data.verifier_output,
            root_supervisor_contract=self.root_supervisor_contract,
        )

    def bind(
        self,
        *,
        release: release_v7._TransactionBoundSpotV7CurrentReleaseV7 | None = None,
        execution: linux_runner.CandidateBoundSpotV7RootSupervisorRunV1 | None = None,
        proof: proof_join._ReleaseBoundSpotV7SemanticProofV1 | None = None,
        finality: finality_join._ReleaseBoundSpotV7CheckpointFinalityV1 | None = None,
        runtime_manifest: bytes | None = None,
        machine_config: bytes | None = None,
        runtime_artifact_manifest: bytes | None = None,
        root_supervisor_contract: bytes | None = None,
        root_supervisor_executable: bytes | None = None,
        firecracker_profile: bytes | None = None,
        request: bytes | None = None,
        settlement_intent: bytes | None = None,
    ) -> join_v1._ReleaseBoundSpotV7FirecrackerExecutionV1:
        return join_v1._bind_release_locked_spot_v7_firecracker_execution_v1(
            self.connection,
            identity=self.store.identity,
            release=release or self.release,
            execution=execution or self.execution,
            proof=proof or self.proof,
            finality=finality or self.finality,
            exact_execution_authority_manifest_bytes=(self.execution_authority_manifest),
            exact_runtime_manifest_bytes=runtime_manifest or self.runtime_manifest,
            exact_machine_config_bytes=machine_config or self.machine_config,
            exact_runtime_artifact_manifest_bytes=(
                runtime_artifact_manifest or self.runtime_artifact_manifest
            ),
            exact_root_supervisor_contract_bytes=(
                root_supervisor_contract or self.root_supervisor_contract
            ),
            exact_root_supervisor_executable_bytes=(
                root_supervisor_executable or self.root_supervisor_executable
            ),
            exact_firecracker_profile_bytes=(firecracker_profile or self.firecracker_profile),
            exact_authority_input_profile_bytes=(
                SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1
            ),
            exact_request_bytes=request or self.request,
            exact_settlement_intent_bytes=settlement_intent or self.settlement_intent,
        )

    def close(self) -> None:
        if self.connection.in_transaction:
            self.connection.rollback()
        self.connection.close()


def _selected_candidate_material(
    *,
    proof: proof_fx._Fixture,
    proof_verifier_manifest: bytes,
    operational_policy: object,
    checker_manifest: bytes,
    checker_executable_sha256: bytes,
    runtime: runtime_v1.CandidateSpotV7FirecrackerRuntimeManifestV1,
    runtime_manifest: bytes,
    machine_config: bytes,
    runtime_artifact_manifest: bytes,
    root_supervisor_contract: bytes,
    root_supervisor_executable: bytes,
    firecracker_profile: bytes,
) -> tuple[candidate_v1.SpotV7ReleaseCandidateManifestV1, bytes]:
    body = authority_fx._candidate_body()
    lineage = cast(dict[str, Any], body["lineage"])
    lineage.update(
        {
            "minimum_rollback_revision": 1,
            "parent_candidate_id": None,
            "proposed_activation_epoch": 0,
            "proposed_expiration_epoch": None,
            "release_revision": 1,
        }
    )
    verifier_digest = hashlib.sha256(proof_verifier_manifest).hexdigest()
    _bind_inventory_raw(body, "verifier_manifest", proof_verifier_manifest)
    authority_fx._inventory_row(body, "verifier_manifest")["bound_identity"] = verifier_digest
    cast(dict[str, Any], body["manifests"])["verifier_manifest_sha256"] = verifier_digest

    projection = operational_policy._projection_for_governed_da_v2()  # type: ignore[attr-defined]
    provenance = operational_policy._provenance_for_governed_da_v2()  # type: ignore[attr-defined]
    finality_policy_root = projection.checkpoint_finality_policy_root[2:]
    operational_policy_root = provenance.manifest_sha256
    cast(dict[str, Any], body["policies"]).update(
        {
            "finality_policy_root": finality_policy_root,
            "operational_policy_root": operational_policy_root,
        }
    )
    authority_fx._inventory_row(body, "finality_policy")["bound_identity"] = (
        finality_policy_root
    )
    authority_fx._inventory_row(body, "operational_policy")["bound_identity"] = (
        operational_policy_root
    )

    runtime_artifact_digest = hashlib.sha256(runtime_artifact_manifest).hexdigest()
    _bind_inventory_raw(body, "runtime_manifest", runtime_manifest)
    _bind_inventory_raw(body, "machine_config", machine_config)
    _bind_inventory_raw(body, "runtime_artifact_manifest", runtime_artifact_manifest)
    authority_fx._inventory_row(body, "runtime_artifact_manifest")["bound_identity"] = (
        runtime.artifact_set_id.hex()
    )
    _bind_inventory_raw(body, "root_supervisor_contract", root_supervisor_contract)
    _bind_inventory_raw(body, "root_supervisor_executable", root_supervisor_executable)
    _bind_inventory_raw(body, "firecracker_profile", firecracker_profile)
    _bind_inventory_raw(
        body,
        "authority_input_profile",
        SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1,
    )
    runtime_section = cast(dict[str, Any], body["runtime"])
    runtime_section.update(
        {
            "artifact_set_id": runtime.artifact_set_id.hex(),
            "authority_input_profile_sha256": hashlib.sha256(
                SPOT_V7_FIRECRACKER_AUTHORITY_INPUT_PROFILE_DESCRIPTOR_V1
            ).hexdigest(),
            "firecracker_profile_sha256": hashlib.sha256(
                firecracker_profile
            ).hexdigest(),
            "machine_config_sha256": hashlib.sha256(machine_config).hexdigest(),
            "root_supervisor_contract_sha256": hashlib.sha256(
                root_supervisor_contract
            ).hexdigest(),
            "root_supervisor_executable_sha256": hashlib.sha256(
                root_supervisor_executable
            ).hexdigest(),
            "runtime_manifest_sha256": hashlib.sha256(runtime_manifest).hexdigest(),
        }
    )

    authority_body = authority_fx._authority_body(body)
    artifacts = cast(dict[str, Any], authority_body["artifacts"])
    artifacts.update(
        {
            "checkpoint_finality_checker_executable_sha256": (
                checker_executable_sha256.hex()
            ),
            "checkpoint_finality_checker_manifest_sha256": hashlib.sha256(
                checker_manifest
            ).hexdigest(),
            "proof_verifier_executable_sha256": proof.executable_sha256,
            "proof_verifier_manifest_sha256": verifier_digest,
            "runtime_artifact_manifest_sha256": runtime_artifact_digest,
        }
    )
    authority_manifest = authority_v1.recompose_spot_v7_execution_authority_manifest_v1(
        authority_body
    )
    _bind_inventory_raw(body, "authority_manifest", authority_manifest)
    authority_digest = hashlib.sha256(authority_manifest).hexdigest()
    authority_fx._inventory_row(body, "authority_manifest")["bound_identity"] = (
        authority_digest
    )
    cast(dict[str, Any], body["manifests"])["authority_manifest_sha256"] = (
        authority_digest
    )
    candidate_bytes = candidate_v1.recompose_spot_v7_release_candidate_manifest_v1(body)
    return (
        candidate_v1.parse_exact_spot_v7_release_candidate_manifest_v1(candidate_bytes),
        authority_manifest,
    )


def _bind_inventory_raw(body: dict[str, Any], role: str, raw: bytes) -> None:
    digest = hashlib.sha256(raw).hexdigest()
    row = authority_fx._inventory_row(body, role)
    row.update(
        {
            "artifact_sha256": digest,
            "bound_identity": digest,
            "size_bytes": len(raw),
        }
    )


def _authenticated_finality(
    policy: object,
    *,
    epoch_id: int,
    proof_journal_hash: bytes,
    post_state_root: bytes,
) -> object:
    store_policy = policy._base_store_policy_for_finality_v3()  # type: ignore[attr-defined]
    sequence = store_policy.genesis_application_checkpoint_sequence + 1
    parent_hash = store_policy.genesis_application_checkpoint_hash
    checkpoint_hash = finality_fx._root("release-bound-firecracker-checkpoint")
    proof_hash = "0x" + proof_journal_hash.hex()
    state_root = "0x" + post_state_root.hex()
    evidence = b'{"schema":"release-bound-firecracker-finality-v1"}'
    evidence_root = "0x" + hashlib.sha256(evidence).hexdigest()
    policy_root = store_policy.checkpoint_finality_policy_root
    certificate_root = finality_fx._finality_certificate_root_v2(
        policy=store_policy,
        epoch_id=epoch_id,
        proof_journal_hash=proof_hash,
        post_state_root=state_root,
        sequence=sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
        evidence_root=evidence_root,
        policy_root=policy_root,
    )
    certificate = finality_fx._encode_checkpoint_finality_certificate_v2(
        policy=store_policy,
        epoch_id=epoch_id,
        proof_journal_hash=proof_hash,
        post_state_root=state_root,
        sequence=sequence,
        checkpoint_hash=checkpoint_hash,
        parent_hash=parent_hash,
        evidence_root=evidence_root,
        policy_root=policy_root,
        certificate_root=certificate_root,
    )
    projection = finality_fx._AuthenticatedCheckpointFinalityProjectionV3(
        application_id=store_policy.application_id,
        chain_or_domain_id=store_policy.chain_or_domain_id,
        epoch_id=epoch_id,
        proof_journal_hash=proof_hash,
        post_state_root=state_root,
        policy_root=policy_root,
        certificate_root=certificate_root,
        finality_evidence_root=evidence_root,
        prior_application_checkpoint_sequence=sequence - 1,
        prior_application_checkpoint_hash=parent_hash,
        next_application_checkpoint_sequence=sequence,
        next_application_checkpoint_hash=checkpoint_hash,
    )
    return finality_fx._AuthenticatedExactCheckpointFinalityTransitionV3(
        projection,
        exact_certificate_bytes=certificate,
        exact_finality_evidence_bytes=evidence,
        seal=finality_fx._AUTHENTICATED_CHECKPOINT_FINALITY_SEAL_V3,
    )


def _candidate_bound_execution(
    *,
    candidate: candidate_v1.SpotV7ReleaseCandidateManifestV1,
    runtime: runtime_v1.CandidateSpotV7FirecrackerRuntimeManifestV1,
    request: bytes,
    payload: bytes,
    root_supervisor_contract: bytes,
) -> linux_runner.CandidateBoundSpotV7RootSupervisorRunV1:
    prepared = policy_v1.prepare_candidate_bound_spot_v7_root_supervisor_policy_v1(
        exact_root_supervisor_contract_bytes=root_supervisor_contract,
        exact_release_candidate_bytes=candidate.canonical_bytes,
        expected_candidate_id=candidate.candidate_id,
    )
    cgroup_request = cgroup_v1.CgroupCreateRequestV1(
        cgroup_mount=prepared.cgroup_mount,
        parent_relative_path=prepared.cgroup_parent_relative_path,
        leaf_name="run00001",
        limits=prepared.cgroup_limits,
        mountinfo_path=prepared.mountinfo_path,
        proc_root=prepared.proc_root,
        trusted_uid=prepared.trusted_uid,
    )
    root_plan = supervisor_v1.SpotV7RootSupervisorPlanV1(
        cgroup_request=cgroup_request,
        network_namespace_root=prepared.network_namespace_root,
        network_namespace_name=cgroup_request.leaf_name,
        process_timeout_ns=prepared.process_timeout_ns,
        teardown_timeout_ns=prepared.teardown_timeout_ns,
    )
    candidate_plan = policy_v1.CandidateBoundSpotV7RootSupervisorPlanV1._from_validated(
        root_supervisor_plan=root_plan,
        candidate_id=candidate.candidate_id,
        evidence_inventory_root=candidate.evidence_inventory_root,
        candidate_manifest_sha256=hashlib.sha256(candidate.canonical_bytes).digest(),
        contract_sha256=prepared.contract_sha256,
        runtime_manifest_sha256=hashlib.sha256(runtime.canonical_bytes).digest(),
        artifact_set_id=runtime.artifact_set_id,
        machine_config_sha256=runtime.machine_config_sha256,
        authority_input_profile_sha256=runtime.authority_input_profile_sha256,
        firecracker_profile_sha256=prepared.firecracker_profile_sha256,
        netns_helper_sha256=bytes.fromhex(prepared.netns_helper_sha256),
        seal=policy_v1._CANDIDATE_BOUND_PLAN_CONSTRUCTION_SEAL_V1,
    )
    completed = supervisor_v1.CompletedSpotV7RootSupervisorRunV1(
        payload_bytes=payload,
        request_sha256=hashlib.sha256(request).digest(),
        cgroup_relative_path=root_plan.expected_cgroup_relative_path,
        network_namespace_path=root_plan.expected_network_namespace_path,
        prepare_observation_sha256=hashlib.sha256(b"prepare").digest(),
        launch_observation_sha256=hashlib.sha256(b"launch").digest(),
        finish_observation_sha256=hashlib.sha256(b"finish").digest(),
        seal=supervisor_v1._COMPLETED_SUPERVISOR_SEAL_V1,
    )
    return linux_runner.CandidateBoundSpotV7RootSupervisorRunV1._from_completed(
        completed_run=completed,
        candidate_bound_plan=candidate_plan,
        seal=linux_runner._CANDIDATE_BOUND_RESULT_SEAL_V1,
    )


def _canonical(value: object) -> bytes:
    return (
        json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True)
        + "\n"
    ).encode("ascii")


@pytest.fixture(scope="session")
def rust_checker(tmp_path_factory: pytest.TempPathFactory) -> Path:
    target = tmp_path_factory.mktemp("release-bound-firecracker-finality-rust")
    return finality_fx._build_rust_checker(target)


def test_release_bound_firecracker_joins_proof_checkpoint_and_runtime_without_db_write(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    rust_checker: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path, rust_checker)
    try:
        before_database = tuple(fixture.connection.iterdump())
        result = fixture.bind()
        assert tuple(fixture.connection.iterdump()) == before_database
        assert (
            fixture.connection.total_changes
            == fixture.release._transaction_expected_total_changes
        )
        assert result.release_candidate_id == fixture.release.current_candidate_id
        assert result.runtime_manifest_sha256 == hashlib.sha256(
            fixture.runtime_manifest
        ).digest()
        assert result.request_sha256 == hashlib.sha256(fixture.request).digest()
        assert result.proof_receipt_sha256 == hashlib.sha256(
            fixture.proof_data.v7_receipt
        ).digest()
        assert result.proof_guest_input_sha256 == hashlib.sha256(
            fixture.proof_data.guest_input
        ).digest()
        assert result.proof_source_v6_receipt_sha256 == hashlib.sha256(
            fixture.proof_data.source_v6_receipt
        ).digest()
        assert result.proof_journal_sha256 == hashlib.sha256(
            fixture.proof_data.journal
        ).digest()
        assert result.proof_plan_b_sha256 == hashlib.sha256(
            fixture.proof_data.plan
        ).digest()
        assert result.pre_state_root == bytes.fromhex(fixture.proof_data.pre_state_root)
        assert result.post_state_root == bytes.fromhex(fixture.proof_data.post_state_root)
        assert result.finality_epoch_id == fixture.proof_data.epoch_id
        assert result.next_checkpoint_sequence == result.prior_checkpoint_sequence + 1
        assert result.release_governed_runtime_identities_verified is True
        assert result.proof_runtime_payload_binding_verified is True
        assert result.checkpoint_post_state_binding_verified is True
        assert result.full_output_device_identity_retained is False
        assert result.root_supervisor_executable_execution_attested is False
        assert result.external_execution_attestation_authenticated is False
        assert result.hostile_same_interpreter_resistance_established is False
        assert result.sandbox_authority is False
        assert result.runtime_authority is False
        assert result.release_authority is False
        assert result.settlement_authority is False
        assert result.production_authority is False
        assert (
            join_v1._require_release_bound_firecracker_still_locked_v1(
                fixture.connection,
                identity=fixture.store.identity,
                execution=result,
            )
            is result
        )
        assert tuple(fixture.connection.iterdump()) == before_database
        assert (
            fixture.connection.total_changes
            == fixture.release._transaction_expected_total_changes
        )
        with pytest.raises(TypeError, match="verified construction"):
            type(result)()
        with pytest.raises(TypeError, match="immutable"):
            result._checked = object()  # type: ignore[assignment]
        with pytest.raises(TypeError, match="cannot be copied"):
            copy.copy(result)
        with pytest.raises(TypeError, match="cannot be deep-copied"):
            copy.deepcopy(result)
        with pytest.raises(TypeError, match="cannot be serialized"):
            pickle.dumps(result)
    finally:
        fixture.close()


def test_equivalent_but_distinct_release_projection_rejects(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    rust_checker: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path, rust_checker)
    try:
        second_projection = release_v7._current_release_for_atomic_join_locked_v7(
            fixture.connection,
            identity=fixture.store.identity,
        )
        assert second_projection.current_candidate_id == fixture.release.current_candidate_id
        assert second_projection is not fixture.release
        with pytest.raises(
            join_v1.SpotV7ReleaseBoundFirecrackerRejectV1,
            match="RELEASE_CAPABILITY_BINDING",
        ):
            fixture.bind(release=second_projection)
    finally:
        fixture.close()


@pytest.mark.parametrize(
    ("field", "replacement", "code"),
    (
        ("runtime_manifest", b"mutated-runtime-manifest", "RUNTIME_MANIFEST"),
        ("machine_config", b"{}\n", "RUNTIME_MANIFEST"),
        (
            "runtime_artifact_manifest",
            b'{"schema":"wrong"}\n',
            "RELEASE_ARTIFACT",
        ),
        (
            "root_supervisor_contract",
            b'{"schema":"wrong"}\n',
            "RELEASE_ARTIFACT",
        ),
        ("root_supervisor_executable", b"substituted-executable", "RELEASE_ARTIFACT"),
        ("firecracker_profile", b'{"schema":"wrong"}\n', "RELEASE_ARTIFACT"),
        ("request", b"wrong-request", "REQUEST"),
        ("settlement_intent", b"wrong-intent", "SETTLEMENT_INTENT"),
    ),
)
def test_runtime_and_artifact_substitutions_reject(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    rust_checker: Path,
    field: str,
    replacement: bytes,
    code: str,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path, rust_checker)
    try:
        with pytest.raises(
            (join_v1.SpotV7ReleaseBoundFirecrackerRejectV1, TypeError),
            match=code,
        ):
            dynamic_bind = cast(Callable[..., object], fixture.bind)
            dynamic_bind(**{field: replacement})
    finally:
        fixture.close()


def test_mismatched_proof_output_and_checkpoint_roots_reject(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    rust_checker: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path, rust_checker)
    try:
        alternate = proof_fx._fixture()
        alternate.plan = b"alternate-canonical-plan-b-v1"
        alternate.verifier_output, alternate.journal = proof_fx._verifier_payload(
            alternate
        )
        assert alternate.verifier_output != fixture.proof_data.verifier_output
        alternate_execution = _candidate_bound_execution(
            candidate=fixture.candidate,
            runtime=fixture.runtime,
            request=fixture.request,
            payload=alternate.verifier_output,
            root_supervisor_contract=fixture.root_supervisor_contract,
        )
        with pytest.raises(
            join_v1.SpotV7ReleaseBoundFirecrackerRejectV1,
            match="PROOF_OUTPUT_BINDING",
        ):
            fixture.bind(execution=alternate_execution)

        wrong_authenticated = _authenticated_finality(
            fixture.operational_policy,
            epoch_id=fixture.proof_data.epoch_id,
            proof_journal_hash=hashlib.sha256(b"wrong-journal").digest(),
            post_state_root=bytes.fromhex(fixture.proof_data.post_state_root),
        )
        wrong_cross_checked = finality_fx._checker(
            rust_checker
        ).cross_check_authenticated(
            policy=fixture.operational_policy,
            finality=wrong_authenticated,
        )
        wrong_finality = finality_join._bind_release_locked_spot_v7_checkpoint_finality_v1(
            fixture.connection,
            identity=fixture.store.identity,
            release=fixture.release,
            finality=wrong_cross_checked,
            exact_execution_authority_manifest_bytes=(
                fixture.execution_authority_manifest
            ),
        )
        with pytest.raises(
            join_v1.SpotV7ReleaseBoundFirecrackerRejectV1,
            match="CHECKPOINT_PROOF_BINDING",
        ):
            fixture.bind(finality=wrong_finality)
    finally:
        fixture.close()


def test_retained_bytes_and_release_transaction_generation_reject(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    rust_checker: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path, rust_checker)
    result = fixture.bind()
    object.__setattr__(
        result._inputs,
        "exact_request_bytes",
        bytes([result._inputs.exact_request_bytes[0] ^ 1])
        + result._inputs.exact_request_bytes[1:],
    )
    with pytest.raises(join_v1.SpotV7ReleaseBoundFirecrackerRejectV1):
        join_v1._require_release_bound_firecracker_still_locked_v1(
            fixture.connection,
            identity=fixture.store.identity,
            execution=result,
        )
    fixture.connection.rollback()
    fixture.connection.execute("BEGIN IMMEDIATE")
    with pytest.raises(
        release_v7.SpotV7ReleaseStateEngineRejectV7,
        match="RELEASE_TRANSACTION_GENERATION_ENDED",
    ):
        join_v1._require_release_bound_firecracker_still_locked_v1(
            fixture.connection,
            identity=fixture.store.identity,
            execution=result,
        )
    fixture.connection.rollback()
    fixture.connection.close()


def test_revoked_release_cannot_create_or_reuse_firecracker_join(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    rust_checker: Path,
) -> None:
    fixture = _JoinFixture(monkeypatch, tmp_path, rust_checker)
    result = fixture.bind()
    fixture.connection.rollback()
    revocation_connection = cutover_v1.open_unified_release_store_v7_for_maintenance_v1(
        fixture.destination,
        identity=fixture.store.identity,
    )
    try:
        revocation_connection.execute("BEGIN IMMEDIATE")
        release_v7._apply_authenticated_release_event_locked_v7(
            revocation_connection,
            identity=fixture.store.identity,
            capability=fixture.revocation,
        )
        revocation_connection.commit()
    finally:
        revocation_connection.close()
    fixture.connection.execute("BEGIN IMMEDIATE")
    with pytest.raises(
        release_v7.SpotV7ReleaseStateEngineRejectV7,
        match="CURRENT_RELEASE_UNAVAILABLE",
    ):
        release_v7._current_release_for_atomic_join_locked_v7(
            fixture.connection,
            identity=fixture.store.identity,
        )
    with pytest.raises(release_v7.SpotV7ReleaseStateEngineRejectV7):
        join_v1._require_release_bound_firecracker_still_locked_v1(
            fixture.connection,
            identity=fixture.store.identity,
            execution=result,
        )
    fixture.connection.rollback()
    fixture.connection.close()
