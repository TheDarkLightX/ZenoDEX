from __future__ import annotations

import copy
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from tools import check_recursive_stark_cbc_spec as checker

REPO = Path(__file__).resolve().parents[1]
REBUILD_PATH_EXPERIMENT = (
    REPO / "docs/research/RECURSIVE_STARK_REBUILD_PATH_EXPERIMENT_20260709.json"
)
CURRENT_V2_EVIDENCE = REPO / "docs/research/RECURSIVE_STARK_V2_CURRENT_EVIDENCE_20260710.json"
TWO_LEAF_EXPERIMENT = REPO / "docs/research/RECURSIVE_STARK_V2_TWO_LEAF_EXPERIMENT_20260710.json"
TWO_LEAF_SOURCE_PINNED_EVIDENCE = (
    REPO / "docs/research/RECURSIVE_STARK_V2_TWO_LEAF_SOURCE_PINNED_EVIDENCE_20260710.json"
)
SAME_PROFILE_TWO_SPOT_EVIDENCE = (
    REPO / "docs/research/RECURSIVE_STARK_V2_SAME_PROFILE_TWO_SPOT_EVIDENCE_20260710.json"
)
CURRENT_V2_REFERENCE = REPO / "config/proof_profiles/risc0_recursive_v2_rebuild_reference.json"
RECURSIVE_REBUILD_REFERENCES = (
    "config/proof_profiles/risc0_recursive_rebuild_reference.json",
    "config/proof_profiles/risc0_recursive_v2_rebuild_reference.json",
)


def _matrix() -> dict[str, Any]:
    matrix, errors = checker.load_matrix(checker.DEFAULT_MATRIX)
    assert errors == []
    assert isinstance(matrix, dict)
    return matrix


def _repo_copy_for_matrix(tmp_path: Path, matrix: dict[str, Any]) -> Path:
    root = tmp_path / "repo"
    paths = {item["owner_surface"] for item in matrix["typed_statements"]}
    for obligation in matrix["obligations"]:
        paths.update(ref["path"] for ref in obligation["code_refs"])
        paths.update(ref["path"] for ref in obligation["test_refs"])
    for relative in sorted(paths):
        destination = root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(REPO / relative, destination)
    for reference_path in RECURSIVE_REBUILD_REFERENCES:
        reference = json.loads((REPO / reference_path).read_bytes())
        reference_paths = [reference_path]
        reference_paths.extend(row["path"] for row in reference["source_compile"]["files"])
        for relative in reference_paths:
            destination = root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            if not destination.exists():
                shutil.copyfile(REPO / relative, destination)
    return root


def _obligation_report(report: dict[str, Any], obligation_id: str) -> dict[str, Any]:
    for item in report["obligations"]["items"]:
        if item["id"] == obligation_id:
            return item
    raise AssertionError(f"missing obligation report for {obligation_id}")


def _statement_report(report: dict[str, Any], statement_id: str) -> dict[str, Any]:
    for item in report["typed_statements"]["items"]:
        if item["id"] == statement_id:
            return item
    raise AssertionError(f"missing typed statement report for {statement_id}")


def test_default_recursive_stark_cbc_matrix_accepts_and_preserves_non_claims() -> None:
    matrix = _matrix()
    report = checker.validate_matrix(matrix)

    assert report["ok"] is True
    assert report["facts"]["missing_required_statements"] == []
    assert report["facts"]["missing_required_obligations"] == []
    assert report["facts"]["typed_statement_count"] == 9
    assert report["facts"]["obligation_count"] == 25
    assert report["facts"]["implemented_obligation_count"] == 20
    assert report["facts"]["pending_obligation_count"] == 5
    assert report["matrix_sha256"] == (
        "sha256:d476dae71a1806c4bdbd3b5a3d6b9d1c9f05e583a5e7d7e8636113fce7b42c84"
    )
    assert report["promotion_boundary"]["facts"]["public_claim_allowed"] is False
    assert report["promotion_boundary"]["facts"]["production_ready"] is False
    assert (
        report["promotion_boundary"]["facts"]["claim_status"]
        == "v1_v2_current_image_local_recursive_proofs_and_temporary_v3_structural_tree_verified"
    )
    assert (
        "no_canonical_recursive_outer_envelope"
        in matrix["promotion_boundary"]["non_claims"]
    )
    assert (
        "no_v3_semantic_receipt_authenticated_tree"
        in matrix["promotion_boundary"]["non_claims"]
    )
    assert (
        "no_release_backed_v3_receipt_authenticated_tree"
        in matrix["promotion_boundary"]["non_claims"]
    )
    assert "no_complete_v3_semantic_composition" in matrix["promotion_boundary"]["non_claims"]
    assert "no_generic_v4_runtime_identity_authority" in (
        matrix["promotion_boundary"]["non_claims"]
    )
    assert "no_zrpf_16x4_profile" in matrix["promotion_boundary"]["non_claims"]
    assert (
        "no_durable_atomic_recursive_admission_with_value_moving_effects"
        in matrix["promotion_boundary"]["non_claims"]
    )
    assert (
        "no_recursive_admission_state_root_as_economic_state_root"
        in matrix["promotion_boundary"]["non_claims"]
    )
    perps_source_finality = next(
        item for item in matrix["obligations"] if item["id"] == "RS-CBC-010"
    )
    assert perps_source_finality["code_refs"] == []
    assert perps_source_finality["test_refs"] == []
    outer_envelope = next(
        item for item in matrix["obligations"] if item["id"] == "RS-CBC-021"
    )
    assert outer_envelope["status"] == "pending"
    assert outer_envelope["code_refs"] == []
    assert outer_envelope["test_refs"] == []
    assert outer_envelope["external_commands"] == []
    adapter_receipt = next(
        item for item in matrix["obligations"] if item["id"] == "RS-CBC-022"
    )
    assert adapter_receipt["status"] == "implemented_partial"
    assert adapter_receipt["code_refs"]
    assert adapter_receipt["test_refs"]
    assert adapter_receipt["external_commands"]
    semantic_runtime_identity = next(
        item for item in matrix["obligations"] if item["id"] == "RS-CBC-024"
    )
    assert semantic_runtime_identity["status"] == "implemented_partial"
    assert semantic_runtime_identity["code_refs"]
    assert semantic_runtime_identity["test_refs"]
    assert semantic_runtime_identity["external_commands"]
    durable_admission = next(
        item for item in matrix["obligations"] if item["id"] == "RS-CBC-025"
    )
    assert durable_admission["status"] == "implemented_partial"
    assert durable_admission["code_refs"]
    assert durable_admission["test_refs"]
    assert durable_admission["external_commands"]
    assert "outer_verified_receipt_profile" in next(
        item
        for item in matrix["typed_statements"]
        if item["id"] == "zrpf_semantic_epoch_receipt_v2"
    )["required_fields"]
    assert any(
        "v1.94.1-rust-x86_64-unknown-linux-gnu" in command
        for command in semantic_runtime_identity["external_commands"]
    )
    for obligation_id in ("RS-CBC-023",):
        obligation = next(
            item for item in matrix["obligations"] if item["id"] == obligation_id
        )
        assert obligation["status"] == "pending"
        assert obligation["code_refs"] == []
        assert obligation["test_refs"] == []
        assert obligation["external_commands"] == []


def test_recursive_stark_cbc_matrix_requires_canonical_outer_envelope_nonclaim() -> None:
    matrix = _matrix()
    matrix["promotion_boundary"]["non_claims"].remove(
        "no_canonical_recursive_outer_envelope"
    )

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        report["promotion_boundary"]["facts"]["missing_required_non_claims"]
        == ["no_canonical_recursive_outer_envelope"]
    )
    assert (
        "promotion_boundary.non_claims missing required values"
        in report["promotion_boundary"]["errors"]
    )


def test_current_v2_public_evidence_matches_reference_and_preserves_nonclaims() -> None:
    evidence_bytes = CURRENT_V2_EVIDENCE.read_bytes()
    evidence = json.loads(evidence_bytes)
    reference_bytes = CURRENT_V2_REFERENCE.read_bytes()
    reference = json.loads(reference_bytes)
    canonical_reference = json.dumps(
        reference,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")

    assert evidence["schema"] == "zenodex/recursive_stark_v2_current_evidence/v1"
    assert hashlib.sha256(evidence_bytes).hexdigest() == (
        "6063b2def168c59d0f187a46e8384979441f4bad8ef1a795f2163c86a7849ea1"
    )
    assert evidence["committed_v2_rebuild_reference"] == {
        "path": "config/proof_profiles/risc0_recursive_v2_rebuild_reference.json",
        "schema": reference["schema"],
        "file_sha256": hashlib.sha256(reference_bytes).hexdigest(),
        "canonical_json_sha256": hashlib.sha256(canonical_reference).hexdigest(),
    }
    assert evidence["regenerated_build_artifacts"]["program"] == reference["program"]
    proof_evidence = evidence["pinned_receipts_verified_without_regeneration"]
    proof_reference = reference["proof_pair"]
    host_pair_verifier = dict(evidence["regenerated_build_artifacts"]["host_pair_verifier"])
    assert host_pair_verifier.pop("committed_reference_field") == "proof_pair.static_verifier"
    assert host_pair_verifier == proof_reference["static_verifier"]
    two_leaf_verifier = dict(
        evidence["regenerated_build_artifacts"]["two_leaf_host_pair_verifier"]
    )
    assert two_leaf_verifier.pop("committed_reference_field") == (
        "proof_pair.two_leaf_static_verifier"
    )
    assert two_leaf_verifier == proof_reference["two_leaf_static_verifier"]
    for field in (
        "inner",
        "root",
        "pair_verifier_output",
        "missing_assumption_output",
        "receipt_artifact_contract",
        "receipt_security",
    ):
        assert proof_evidence[field] == proof_reference[field]
    assert proof_evidence["receipts_regenerated_in_clean_run"] is False
    assert proof_evidence["proof_regeneration_determinism"] is False
    assert evidence["claims"] == reference["claims"]

    controls = evidence["clean_build_inputs_and_controls"]
    reference_policy = reference["build_policy"]
    assert (
        controls["toolchain_lock"]["canonical_json_sha256"]
        == (reference_policy["toolchain_lock_canonical_sha256"])
    )
    assert controls["effective_cargo_configs"] == [
        {
            "scope": row["location"],
            **{key: value for key, value in row.items() if key != "location"},
        }
        for row in reference_policy["effective_cargo_configs"]
    ]
    assert controls["nested_cargo_policy"] == reference_policy["nested_cargo_policy"]
    assert controls["offline_config_sha256"] == reference_policy["offline_config_sha256"]
    assert controls["source_closure"]["root_sha256"] == (reference["source_compile"]["root_sha256"])
    assert (
        controls["registry_source_closure"]["root_sha256"]
        == (reference["source_compile"]["registry_source_closure"]["root_sha256"])
    )

    required_false_facts = {
        "proof_regeneration_determinism",
        "builder_identity_authenticated",
        "full_toolchain_execution_authenticated",
        "proxy_interpreter_authenticated",
        "runtime_rootfs_authenticated",
        "whole_build_network_isolation",
        "source_archive_provenance_authenticated",
        "cross_environment_reproducibility",
        "public_claim_allowed",
        "production_ready",
        "settlement_authorization",
    }
    assert set(evidence["clean_rebuild_report"]["false_facts"]) == required_false_facts
    required_current_nonclaims = {
        "the clean rebuild regenerated the program, raw ELF, image ID, and both host pair verifiers",
        "the clean rebuild verified the pinned receipts without regenerating them",
        "proof regeneration determinism is not established",
        "builder identity, full toolchain execution, proxy interpreter, runtime rootfs, whole-build network isolation, and source-archive provenance are not authenticated",
        "this evidence does not establish cross-environment reproducibility, public replay, reproducible release, settlement authority, ledger admission, privacy, or production readiness",
    }
    assert set(proof_reference["nonclaims"]) <= set(evidence["nonclaims"])
    assert required_current_nonclaims <= set(evidence["nonclaims"])

    negative = evidence["negative_evidence"]
    assert negative["bundle_committed"] is False
    assert negative["public_replay"] is False
    assert negative["manifest"]["sha256"] == (
        "4a5315436583b07ff649233e7f7a006318e95f7bc756cecbb995c203694e9694"
    )
    assert negative["manifest_digest_sidecar"]["sha256"] == (
        "8db91ed53d021ac4c09c5f0642342a80608a24d22b156ba3cbdfaf7169a4e685"
    )
    assert {row["id"] for row in negative["fail_closed_cases"]} == {
        "swapped-levels",
        "wrong-risc0-image-id",
        "authenticated-journal-mutation",
        "noncanonical-outer-json",
    }
    assert all(row["exit_code"] == 1 for row in negative["fail_closed_cases"])

    def iter_strings(value: Any) -> list[str]:
        if isinstance(value, str):
            return [value]
        if isinstance(value, dict):
            return [item for child in value.values() for item in iter_strings(child)]
        if isinstance(value, list):
            return [item for child in value for item in iter_strings(child)]
        return []

    public_strings = iter_strings(evidence)
    assert all(not value.startswith("/") for value in public_strings)
    public_text = "\n".join(public_strings).lower()
    for forbidden in (
        "/home/",
        "/media/",
    ):
        assert forbidden not in public_text


def test_two_leaf_experiment_manifest_is_exact_and_claim_limited() -> None:
    manifest_bytes = TWO_LEAF_EXPERIMENT.read_bytes()
    manifest = json.loads(manifest_bytes)
    reference = json.loads(CURRENT_V2_REFERENCE.read_bytes())

    assert hashlib.sha256(manifest_bytes).hexdigest() == (
        "c225841cff999b30d0b076845a76b6c0a1ee95127a62504dc2d7c0f49280b73d"
    )
    assert manifest["schema"] == "zenodex/recursive_stark_v2_two_leaf_experiment/v1"
    assert manifest["status"] == "experimental_current_image_two_leaf_pair_verified"
    assert manifest["aggregate_v2"]["image_id"] == reference["program"]["image_id"]
    assert manifest["aggregate_v2"]["sdk_version"] == reference["sdk_version"]

    claims = manifest["claims"]
    assert claims["experimental_current_image_two_leaf_fixed_height_receipt_integrity"] is True
    assert claims["exact_leaf_artifact_sha256_recorded"] is True
    assert claims["host_verifier_recomputes_exact_leaf_claim_and_journal_roots"] is True
    for claim in (
        "arbitrary_depth_recursion",
        "cross_environment_reproducibility",
        "data_availability_verified",
        "durable_atomic_admission",
        "general_multi_leaf_profile_promoted",
        "governed_statement_authority",
        "independent_proof_implementation",
        "nonempty_receipt_partition_merge_cryptographically_exercised",
        "privacy",
        "production_ready",
        "public_claim_allowed",
        "release_authority",
        "same_profile_verifier_set_cryptographically_exercised",
        "settlement_authorization",
        "v1_outer_envelope_canonicality_verified",
    ):
        assert claims[claim] is False

    leaves = manifest["leaf_claims"]
    assert [(leaf["role"], leaf["profile"], leaf["lane_id"]) for leaf in leaves] == [
        ("spot", "recursive_spot_leaf_v1", "spot-root-child-0001"),
        ("zusd", "recursive_zusd_leaf_v1", "zusd-root-child-0001"),
    ]
    assert len({leaf["image_id"] for leaf in leaves}) == 2
    assert all(len(leaf["receipt_sha256"]) == 64 for leaf in leaves)

    proof_pair = manifest["proof_pair"]
    inner = proof_pair["inner"]
    root = proof_pair["root"]
    assert (
        inner["immediate_child_count"],
        inner["flat_leaf_count"],
        inner["tree_height"],
        inner["subtree_node_count"],
    ) == (2, 2, 1, 3)
    assert (
        root["immediate_child_count"],
        root["flat_leaf_count"],
        root["tree_height"],
        root["subtree_node_count"],
    ) == (1, 2, 2, 4)
    assert manifest["prover"]["source_to_binary_build_authenticated"] is False
    verifier = manifest["independent_host_verifier"]
    assert verifier["implementation_independent_from_guest"] is False
    assert verifier["transcript"]["status"] == "recursive_v2_two_leaf_pair_verified"
    assert verifier["control"] == {
        "expected_error": "authenticated journal surface mismatch",
        "exit_code": 1,
        "input_pair": "pinned one-leaf v2 pair",
        "stderr_sha256": "c51c6a83b4e6c87e00785de0f0fc73fb3f4cfe64571f396b1f9e707e44c7f17b",
        "stdout_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    }

    public_text = json.dumps(manifest, sort_keys=True)
    for forbidden in (
        "/home/",
        "/media/",
        "private_project_marker",
    ):
        assert forbidden not in public_text


def test_two_leaf_source_pinned_evidence_is_exact_and_claim_limited() -> None:
    evidence_bytes = TWO_LEAF_SOURCE_PINNED_EVIDENCE.read_bytes()
    evidence = json.loads(evidence_bytes)
    reference_bytes = CURRENT_V2_REFERENCE.read_bytes()
    reference = json.loads(reference_bytes)
    canonical_reference = json.dumps(
        reference,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")

    assert hashlib.sha256(evidence_bytes).hexdigest() == (
        "9a98b947f76a599109f5238861d010fd3dbb8a8299ef6e3f03685b3cac51ad74"
    )
    assert evidence["schema"] == ("zenodex/recursive_stark_v2_two_leaf_source_pinned_evidence/v1")
    assert evidence["status"] == (
        "same_host_source_frozen_two_leaf_receipts_regenerated_and_verified"
    )
    assert evidence["aggregate_v2"]["image_id"] == reference["program"]["image_id"]
    assert evidence["aggregate_v2"]["program_sha256"] == (reference["program"]["program_sha256"])

    build = evidence["source_frozen_build"]
    assert build["reference"] == {
        "path": "config/proof_profiles/risc0_recursive_v2_rebuild_reference.json",
        "file_sha256": hashlib.sha256(reference_bytes).hexdigest(),
        "canonical_json_sha256": hashlib.sha256(canonical_reference).hexdigest(),
    }
    assert build["source_closure"]["file_count"] == (reference["source_compile"]["file_count"])
    assert build["source_closure"]["root_sha256"] == (reference["source_compile"]["root_sha256"])
    assert build["build_pipeline_constrained"] is True
    assert build["source_to_binary_cryptographic_attestation"] is False
    assert build["cross_environment_reproducibility"] is False

    pair = evidence["regenerated_proof_pair"]
    inner = pair["inner"]
    root = pair["root"]
    assert (
        inner["immediate_child_count"],
        inner["flat_leaf_count"],
        inner["tree_height"],
        inner["subtree_node_count"],
    ) == (2, 2, 1, 3)
    assert (
        root["immediate_child_count"],
        root["flat_leaf_count"],
        root["tree_height"],
        root["subtree_node_count"],
    ) == (1, 2, 2, 4)

    historical_bytes = TWO_LEAF_EXPERIMENT.read_bytes()
    historical = json.loads(historical_bytes)
    comparison = evidence["cross_run_comparison"]
    assert comparison["historical_experiment_manifest_sha256"] == (
        hashlib.sha256(historical_bytes).hexdigest()
    )
    assert (
        comparison["historical_inner_receipt_sha256"]
        == (historical["proof_pair"]["inner"]["receipt_sha256"])
    )
    assert (
        comparison["historical_root_receipt_sha256"]
        == (historical["proof_pair"]["root"]["receipt_sha256"])
    )
    assert inner["journal_sha256"] == historical["proof_pair"]["inner"]["journal_sha256"]
    assert root["journal_sha256"] == historical["proof_pair"]["root"]["journal_sha256"]
    assert inner["receipt_sha256"] != comparison["historical_inner_receipt_sha256"]
    assert root["receipt_sha256"] != comparison["historical_root_receipt_sha256"]
    assert comparison["receipt_bytes_reproduced"] is False
    assert comparison["proof_regeneration_determinism"] is False

    claims = evidence["claims"]
    for claim in (
        "bounded_host_fanout_constructor_source_pinned",
        "current_image_two_leaf_receipts_regenerated",
        "current_image_two_leaf_fixed_height_receipt_integrity",
        "exact_leaf_and_node_binding_verified",
        "same_host_source_frozen_build",
    ):
        assert claims[claim] is True
    for claim in (
        "arbitrary_depth_recursion",
        "cross_environment_reproducibility",
        "data_availability_verified",
        "durable_atomic_admission",
        "general_multi_leaf_profile_promoted",
        "governed_statement_authority",
        "nonempty_receipt_partition_merge_cryptographically_exercised",
        "privacy",
        "production_ready",
        "public_claim_allowed",
        "public_replay_available",
        "release_authority",
        "same_profile_verifier_set_cryptographically_exercised",
        "settlement_authorization",
        "throughput_claim_allowed",
        "v1_outer_envelope_canonicality_verified",
    ):
        assert claims[claim] is False

    verifier = evidence["verification"]["specialized_host_verifier"]
    assert verifier["repository_source_pinned"] is True
    assert verifier["independent_proof_implementation"] is False
    source_row = next(
        row
        for row in reference["source_compile"]["files"]
        if row["path"] == verifier["source_path"]
    )
    assert verifier["source_sha256"] == source_row["sha256"]
    assert verifier["binary_sha256"] == (
        reference["proof_pair"]["two_leaf_static_verifier"]["sha256"]
    )
    assert verifier["binary_size_bytes"] == (
        reference["proof_pair"]["two_leaf_static_verifier"]["size_bytes"]
    )
    assert verifier["status"] == "recursive_v2_two_leaf_pair_verified"
    assert evidence["verification"]["missing_child_assumption_control"]["status"] == (
        "missing_child_assumption_rejected"
    )

    public_text = json.dumps(evidence, sort_keys=True)
    for forbidden in (
        "/home/",
        "/media/",
        "private_project_marker",
    ):
        assert forbidden not in public_text


def test_same_profile_two_spot_evidence_is_exact_and_claim_limited() -> None:
    evidence_bytes = SAME_PROFILE_TWO_SPOT_EVIDENCE.read_bytes()
    evidence = json.loads(evidence_bytes)
    baseline_bytes = TWO_LEAF_SOURCE_PINNED_EVIDENCE.read_bytes()
    reference_bytes = CURRENT_V2_REFERENCE.read_bytes()

    assert hashlib.sha256(evidence_bytes).hexdigest() == (
        "18141ffae7279b1a717edb41674b4fae101a489e2d7870b920c45c8d6810512a"
    )
    assert evidence["schema"] == (
        "zenodex/recursive_stark_v2_same_profile_two_spot_evidence/v1"
    )
    assert evidence["status"] == (
        "same_host_source_frozen_same_profile_two_spot_receipts_generated_and_verified"
    )
    assert evidence["trust_roots"]["recursive_v2_rebuild_reference"]["file_sha256"] == (
        hashlib.sha256(reference_bytes).hexdigest()
    )
    assert evidence["trust_roots"]["source_pinned_two_leaf_baseline"]["file_sha256"] == (
        hashlib.sha256(baseline_bytes).hexdigest()
    )
    identity = evidence["same_profile_identity"]
    assert identity["child_count"] == 2
    assert identity["unique_verifier_id_count"] == 1
    assert identity["distinct_statement_hash_count"] == 2
    assert identity["distinct_source_id_count"] == 2
    assert evidence["claims"]["same_profile_verifier_set_cryptographically_exercised"] is True
    assert evidence["claims"]["new_receipt_seal_mutation_rejected"] is True
    for claim in (
        "arbitrary_depth_recursion",
        "general_multi_leaf_profile_promoted",
        "nonempty_receipt_partition_merge_cryptographically_exercised",
        "privacy",
        "production_ready",
        "public_claim_allowed",
        "public_replay_available",
        "release_authority",
        "settlement_authorization",
        "throughput_claim_allowed",
    ):
        assert evidence["claims"][claim] is False

    public_text = json.dumps(evidence, sort_keys=True)
    for forbidden in ("/home/", "/media/", "private_project_marker"):
        assert forbidden not in public_text


def test_post_repair_verified_status_requires_fresh_proof_obligation_implemented() -> None:
    matrix = _matrix()
    for obligation in matrix["obligations"]:
        if obligation["id"] == "RS-CBC-014":
            obligation["status"] = "pending"
            break

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "post-repair local-proof-verified status requires RS-CBC-014 implemented"
        in report["errors"]
    )


def test_post_repair_verified_status_rejects_stale_proof_absence_nonclaim() -> None:
    matrix = _matrix()
    matrix["promotion_boundary"]["non_claims"].append(
        "no_current_image_recursive_proof_after_composition_repair"
    )

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "promotion_boundary.non_claims retains stale current-image proof absence"
        in report["promotion_boundary"]["errors"]
    )


def test_structural_tree_verified_status_rejects_stale_tree_absence_nonclaim() -> None:
    matrix = _matrix()
    matrix["promotion_boundary"]["non_claims"].append(
        "no_v3_receipt_authenticated_tree"
    )

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "promotion_boundary.non_claims retains stale V3 structural-tree absence"
        in report["promotion_boundary"]["errors"]
    )


@pytest.mark.parametrize("obligation_id", ["RS-CBC-016", "RS-CBC-022"])
def test_structural_tree_verified_status_requires_implemented_tree_obligations(
    obligation_id: str,
) -> None:
    matrix = _matrix()
    obligation = next(
        item for item in matrix["obligations"] if item["id"] == obligation_id
    )
    obligation["status"] = "pending"
    obligation["code_refs"] = []
    obligation["test_refs"] = []
    obligation["external_commands"] = []

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "temporary V3 structural-tree-verified status requires "
        f"{obligation_id} implemented or implemented_partial"
    ) in report["errors"]


@pytest.mark.parametrize(
    "relative",
    [
        "zk/state_proof_risc0/shared/src/recursive.rs",
        "zk/recursive_stark_v2_risc0/shared/src/lib.rs",
    ],
)
def test_post_repair_verified_status_rejects_source_closure_mutation(
    tmp_path: Path,
    relative: str,
) -> None:
    matrix = _matrix()
    root = _repo_copy_for_matrix(tmp_path, matrix)
    path = root / relative
    path.write_bytes(path.read_bytes() + b"\n// guest-linked mutation\n")

    report = checker.validate_matrix(matrix, repo_root=root)

    assert report["ok"] is False
    assert any(
        error.startswith("promoted V1 source closure rejected:")
        or error.startswith("promoted V2 source closure rejected:")
        for error in report["errors"]
    )


def test_post_repair_verified_status_rejects_extra_compile_source(tmp_path: Path) -> None:
    matrix = _matrix()
    root = _repo_copy_for_matrix(tmp_path, matrix)
    extra = root / "zk/recursive_stark_v2_risc0/shared/src/unpinned.rs"
    extra.write_text("pub const UNPINNED: bool = true;\n", encoding="ascii")

    report = checker.validate_matrix(matrix, repo_root=root)

    assert report["ok"] is False
    assert any(
        error.startswith("promoted V2 source closure rejected: SOURCE_FILE_EXTRA:")
        for error in report["errors"]
    )


def test_recursive_stark_cbc_matrix_rejects_stale_pre_repair_claim_status() -> None:
    matrix = _matrix()
    matrix["promotion_boundary"]["claim_status"] = (
        "patched_toolchain_local_artifact_pinned_recursive_proof_verified"
    )

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "promotion_boundary.claim_status is not an accepted reviewed status"
        in report["promotion_boundary"]["errors"]
    )


def test_recursive_stark_cbc_matrix_rejects_stale_adapter_only_claim_status() -> None:
    matrix = _matrix()
    matrix["promotion_boundary"]["claim_status"] = (
        "v1_v2_current_image_local_recursive_proofs_and_temporary_v3_adapter_receipt_verified"
    )

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "promotion_boundary.claim_status is not an accepted reviewed status"
        in report["promotion_boundary"]["errors"]
    )


def test_rebuild_path_experiment_preserves_counterexample_and_nonclaims() -> None:
    experiment = json.loads(REBUILD_PATH_EXPERIMENT.read_bytes())
    rows = {row["id"]: row for row in experiment["experiments"]}
    fixed = rows["fixed_dependency_path_nested_cargo_offline"]
    relocated = rows["relocated_cargo_home_nested_cargo_offline"]

    assert experiment["scope"] == "local_same_host_research_evidence"
    assert all(value is False for value in experiment["claims"].values())
    assert fixed["nested_cargo_offline"] is True
    assert fixed["compiler_visible_dependency_path_changed"] is False
    assert fixed["outcome"] == "exact_reference_match"
    assert fixed["proof_verification"]["ok"] is True
    assert relocated["nested_cargo_offline"] is True
    assert relocated["compiler_visible_dependency_path_changed"] is True
    assert relocated["outcome"] == "guest_image_identity_drift"
    assert relocated["proof_verification"] == {
        "error": "risc0_image_id mismatch",
        "ok": False,
        "transcript_sha256": ("a407b7ea58badabb159710b0a7702bd13cd3d6a84433e1d1ff980827bd8c1af1"),
    }

    fixed_programs = {row["name"]: row for row in fixed["programs"]}
    relocated_programs = {row["name"]: row for row in relocated["programs"]}
    assert fixed_programs.keys() == relocated_programs.keys()
    assert len(fixed_programs) == 6
    assert all(
        fixed_programs[name]["sha256"] != relocated_programs[name]["sha256"]
        and fixed_programs[name]["image_id"] != relocated_programs[name]["image_id"]
        for name in fixed_programs
    )


def test_recursive_stark_cbc_matrix_rejects_production_claim_boundary() -> None:
    matrix = _matrix()
    matrix["promotion_boundary"]["public_claim_allowed"] = True
    matrix["promotion_boundary"]["production_ready"] = True
    matrix["promotion_boundary"]["claim_status"] = "production_ready"

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert "promotion_boundary rejected" in report["errors"]
    assert (
        "promotion_boundary.public_claim_allowed must be false"
        in report["promotion_boundary"]["errors"]
    )
    assert (
        "promotion_boundary.production_ready must be false"
        in report["promotion_boundary"]["errors"]
    )
    assert (
        "promotion_boundary.claim_status is not an accepted reviewed status"
        in report["promotion_boundary"]["errors"]
    )


def test_recursive_stark_cbc_matrix_rejects_unknown_root_field() -> None:
    matrix = _matrix()
    matrix["unreviewed_extension"] = {}

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert "matrix has unknown fields: unreviewed_extension" in report["errors"]


def test_recursive_stark_cbc_matrix_rejects_unknown_promotion_field() -> None:
    matrix = _matrix()
    matrix["promotion_boundary"]["unreviewed_extension"] = False

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "promotion_boundary has unknown fields: unreviewed_extension"
        in report["promotion_boundary"]["errors"]
    )


def test_recursive_stark_cbc_matrix_rejects_unknown_statement_field() -> None:
    matrix = _matrix()
    statement = matrix["typed_statements"][0]
    statement["unreviewed_extension"] = "ignored-under-old-schema"

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    errors = _statement_report(report, statement["id"])["errors"]
    assert "typed_statements[0] has unknown fields: unreviewed_extension" in errors


def test_recursive_stark_cbc_matrix_rejects_unknown_obligation_field() -> None:
    matrix = _matrix()
    obligation = matrix["obligations"][0]
    obligation["unreviewed_extension"] = "ignored-under-old-schema"

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    errors = _obligation_report(report, obligation["id"])["errors"]
    assert "obligations[0] has unknown fields: unreviewed_extension" in errors


def test_recursive_stark_cbc_matrix_rejects_unknown_reference_field() -> None:
    matrix = _matrix()
    obligation = matrix["obligations"][0]
    obligation["code_refs"][0]["unreviewed_extension"] = "ignored-under-old-schema"

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    errors = _obligation_report(report, obligation["id"])["errors"]
    assert (
        "obligations[0].code_refs[0] has unknown fields: unreviewed_extension"
        in errors
    )


def test_recursive_stark_cbc_matrix_rejects_implemented_obligation_without_tests() -> None:
    matrix = _matrix()
    obligation = copy.deepcopy(matrix["obligations"][0])
    obligation["test_refs"] = []
    matrix["obligations"][0] = obligation

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    item = _obligation_report(report, "RS-CBC-001")
    assert "implemented obligation must include test_refs" in item["errors"]


def test_recursive_stark_cbc_matrix_rejects_missing_required_obligation() -> None:
    matrix = _matrix()
    matrix["obligations"] = [
        obligation for obligation in matrix["obligations"] if obligation["id"] != "RS-CBC-015"
    ]

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert "missing required obligations: RS-CBC-015" in report["obligations"]["errors"]


def test_recursive_stark_cbc_matrix_requires_v3_structural_statement() -> None:
    matrix = _matrix()
    matrix["typed_statements"] = [
        statement
        for statement in matrix["typed_statements"]
        if statement["id"] != "zrpf_node_v3_structural"
    ]

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "missing required typed statements: zrpf_node_v3_structural"
        in report["typed_statements"]["errors"]
    )


@pytest.mark.parametrize(
    "field",
    [
        "count_unit_id",
        "node_statement_hash",
        "commitments.provenance_root",
        "child_provenance_roots",
    ],
)
def test_v3_structural_statement_pins_new_abi_fields(field: str) -> None:
    matrix = _matrix()
    statement = next(
        item for item in matrix["typed_statements"] if item["id"] == "zrpf_node_v3_structural"
    )
    statement["required_fields"].remove(field)

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    errors = _statement_report(report, "zrpf_node_v3_structural")["errors"]
    assert f"typed statement missing pinned required fields: {field}" in errors


def test_v3_structural_statement_rejects_obsolete_unpinned_fields() -> None:
    matrix = _matrix()
    statement = next(
        item for item in matrix["typed_statements"] if item["id"] == "zrpf_node_v3_structural"
    )
    statement["required_fields"].append("statement_hash")

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    errors = _statement_report(report, "zrpf_node_v3_structural")["errors"]
    assert "typed statement has unpinned fields: statement_hash" in errors


def test_recursive_stark_cbc_matrix_requires_outer_envelope_obligation() -> None:
    matrix = _matrix()
    matrix["obligations"] = [
        obligation for obligation in matrix["obligations"] if obligation["id"] != "RS-CBC-021"
    ]

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert "missing required obligations: RS-CBC-021" in report["obligations"]["errors"]


@pytest.mark.parametrize(
    "obligation_id",
    ["RS-CBC-022", "RS-CBC-023", "RS-CBC-024", "RS-CBC-025"],
)
def test_recursive_stark_cbc_matrix_requires_v3_authority_obligations(
    obligation_id: str,
) -> None:
    matrix = _matrix()
    matrix["obligations"] = [
        obligation for obligation in matrix["obligations"] if obligation["id"] != obligation_id
    ]

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert f"missing required obligations: {obligation_id}" in report["obligations"]["errors"]


def test_semantic_v2_statuses_cannot_self_promote_without_fresh_receipt_evidence() -> None:
    matrix = _matrix()
    statement = next(
        item
        for item in matrix["typed_statements"]
        if item["id"] == "zrpf_semantic_epoch_receipt_v2"
    )
    obligation = next(
        item for item in matrix["obligations"] if item["id"] == "RS-CBC-024"
    )
    statement["status"] = "implemented"
    obligation["status"] = "implemented"

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "required typed statement status differs from pinned status"
        in _statement_report(report, "zrpf_semantic_epoch_receipt_v2")["errors"]
    )
    assert (
        "required obligation status differs from pinned status"
        in _obligation_report(report, "RS-CBC-024")["errors"]
    )


def test_durable_replay_admission_cannot_self_promote_to_full_implementation() -> None:
    matrix = _matrix()
    obligation = next(
        item for item in matrix["obligations"] if item["id"] == "RS-CBC-025"
    )
    obligation["status"] = "implemented"

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "required obligation status differs from pinned status"
        in _obligation_report(report, "RS-CBC-025")["errors"]
    )


def test_semantic_v2_fresh_receipt_nonclaim_is_required() -> None:
    matrix = _matrix()
    matrix["promotion_boundary"]["non_claims"].remove(
        "no_fresh_zrpf_semantic_v2_receipt_evidence"
    )

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "promotion_boundary.non_claims missing required values"
        in report["promotion_boundary"]["errors"]
    )


def test_outer_envelope_obligation_cannot_self_promote_with_unrelated_evidence() -> None:
    matrix = _matrix()
    obligation = next(item for item in matrix["obligations"] if item["id"] == "RS-CBC-021")
    obligation["status"] = "implemented_partial"
    obligation["code_refs"] = copy.deepcopy(matrix["obligations"][0]["code_refs"])
    obligation["test_refs"] = copy.deepcopy(matrix["obligations"][0]["test_refs"])
    obligation["external_commands"] = ["python3 -m pytest -q tests/test_placeholder.py"]

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    errors = _obligation_report(report, "RS-CBC-021")["errors"]
    assert (
        "required obligation remains pinned pending until checker policy is updated"
        in errors
    )
    assert "pinned pending obligation must not cite implementation evidence" in errors


@pytest.mark.parametrize("obligation_id", ["RS-CBC-023"])
def test_v3_pending_obligation_cannot_self_promote_with_structural_evidence(
    obligation_id: str,
) -> None:
    matrix = _matrix()
    obligation = next(item for item in matrix["obligations"] if item["id"] == obligation_id)
    obligation["status"] = "implemented_partial"
    obligation["code_refs"] = [
        {
            "path": "zk/zrpf_protocol/protocol/src/lib.rs",
            "symbol": "NodeJournalV3",
        }
    ]
    obligation["test_refs"] = [
        {
            "path": "zk/zrpf_protocol/protocol/tests/node_v3.rs",
            "symbol": "fully_saturated_eight_by_eight_tree_hits_the_declared_bounds",
        }
    ]

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    errors = _obligation_report(report, obligation_id)["errors"]
    assert "required obligation remains pinned pending until checker policy is updated" in errors
    assert "pinned pending obligation must not cite implementation evidence" in errors


@pytest.mark.parametrize("field", ["code_refs", "test_refs", "external_commands"])
def test_outer_envelope_pending_row_rejects_premature_evidence(field: str) -> None:
    matrix = _matrix()
    obligation = next(item for item in matrix["obligations"] if item["id"] == "RS-CBC-021")
    if field == "external_commands":
        obligation[field] = ["cargo test recursive_outer_envelope"]
    else:
        obligation[field] = copy.deepcopy(matrix["obligations"][0][field])

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "pinned pending obligation must not cite implementation evidence"
        in _obligation_report(report, "RS-CBC-021")["errors"]
    )


def test_recursive_stark_cbc_matrix_rejects_missing_ref_symbol() -> None:
    matrix = _matrix()
    obligation = copy.deepcopy(matrix["obligations"][0])
    obligation["code_refs"][0]["symbol"] = "definitely_missing_recursive_symbol"
    matrix["obligations"][0] = obligation

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    item = _obligation_report(report, "RS-CBC-001")
    assert (
        "ref symbol missing: zk/state_proof_risc0/methods/aggregate/src/main.rs::"
        "definitely_missing_recursive_symbol"
    ) in item["errors"]


def test_recursive_stark_cbc_matrix_rejects_unreviewed_claim_status() -> None:
    matrix = _matrix()
    matrix["promotion_boundary"]["claim_status"] = "experimental_local_smoke"

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert (
        "promotion_boundary.claim_status is not an accepted reviewed status"
        in report["promotion_boundary"]["errors"]
    )


@pytest.mark.parametrize(
    ("obligation_id", "field", "value", "expected_error"),
    [
        (
            "RS-CBC-018",
            "severity",
            "low",
            "required obligation severity is below its pinned minimum",
        ),
        (
            "RS-CBC-019",
            "defense_layer",
            "bounded_blast_radius",
            "required obligation defense_layer differs from its pinned layer",
        ),
        (
            "RS-CBC-020",
            "defense_layer",
            "guarded_transition",
            "required obligation defense_layer differs from its pinned layer",
        ),
        (
            "RS-CBC-021",
            "defense_layer",
            "guarded_transition",
            "required obligation defense_layer differs from its pinned layer",
        ),
        (
            "RS-CBC-022",
            "defense_layer",
            "unrepresentable",
            "required obligation defense_layer differs from its pinned layer",
        ),
        (
            "RS-CBC-023",
            "defense_layer",
            "guarded_transition",
            "required obligation defense_layer differs from its pinned layer",
        ),
        (
            "RS-CBC-024",
            "defense_layer",
            "guarded_transition",
            "required obligation defense_layer differs from its pinned layer",
        ),
        (
            "RS-CBC-025",
            "defense_layer",
            "guarded_transition",
            "required obligation defense_layer differs from its pinned layer",
        ),
    ],
)
def test_required_obligation_policy_rejects_downgrade_or_layer_drift(
    obligation_id: str,
    field: str,
    value: str,
    expected_error: str,
) -> None:
    matrix = _matrix()
    obligation = next(item for item in matrix["obligations"] if item["id"] == obligation_id)
    obligation[field] = value

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    assert expected_error in _obligation_report(report, obligation_id)["errors"]


@pytest.mark.parametrize(
    "unsafe_path",
    [
        "/etc/passwd",
        "../zk/state_proof_risc0/shared/src/recursive.rs",
        "zk\\state_proof_risc0\\shared\\src\\recursive.rs",
        "zk/state_proof_risc0/../state_proof_risc0/shared/src/recursive.rs",
        "zk/state_proof_risc0//shared/src/recursive.rs",
        "zk/state_proof_risc0/shared/src/recursive.rs\x00suffix",
        "zk/state_proof_risc0/shared/src/r\u00e9cursive.rs",
    ],
)
def test_recursive_stark_cbc_matrix_rejects_unsafe_reference_paths(
    unsafe_path: str,
) -> None:
    matrix = _matrix()
    matrix["obligations"][0]["code_refs"][0]["path"] = unsafe_path

    report = checker.validate_matrix(matrix)

    assert report["ok"] is False
    item = _obligation_report(report, "RS-CBC-001")
    assert any("ref path rejected" in error for error in item["errors"])


def test_recursive_stark_cbc_matrix_rejects_symlink_reference(tmp_path: Path) -> None:
    matrix = _matrix()
    root = _repo_copy_for_matrix(tmp_path, matrix)
    relative = matrix["obligations"][0]["code_refs"][0]["path"]
    path = root / relative
    target = tmp_path / "outside.rs"
    target.write_text("outside", encoding="utf-8")
    path.unlink()
    path.symlink_to(target)

    report = checker.validate_matrix(matrix, repo_root=root)

    assert report["ok"] is False
    item = _obligation_report(report, "RS-CBC-001")
    assert any("symbolic link" in error for error in item["errors"])


def test_recursive_stark_cbc_matrix_rejects_non_regular_reference(
    tmp_path: Path,
) -> None:
    matrix = _matrix()
    root = _repo_copy_for_matrix(tmp_path, matrix)
    relative = matrix["obligations"][0]["code_refs"][0]["path"]
    path = root / relative
    path.unlink()
    path.mkdir()

    report = checker.validate_matrix(matrix, repo_root=root)

    assert report["ok"] is False
    item = _obligation_report(report, "RS-CBC-001")
    assert any("not a regular file" in error for error in item["errors"])


def test_recursive_stark_cbc_matrix_rejects_oversized_reference(
    tmp_path: Path,
) -> None:
    matrix = _matrix()
    root = _repo_copy_for_matrix(tmp_path, matrix)
    relative = matrix["obligations"][0]["code_refs"][0]["path"]
    (root / relative).write_bytes(b"x" * (checker.MAX_REFERENCED_FILE_BYTES + 1))

    report = checker.validate_matrix(matrix, repo_root=root)

    assert report["ok"] is False
    item = _obligation_report(report, "RS-CBC-001")
    assert any("exceeds size limit" in error for error in item["errors"])


def test_matrix_loader_rejects_duplicate_keys(tmp_path: Path) -> None:
    path = tmp_path / "matrix.json"
    path.write_text('{"schema":"first","schema":"second"}', encoding="utf-8")

    matrix, errors = checker.load_matrix(path)

    assert matrix is None
    assert errors == ["matrix rejected: duplicate JSON key: schema"]


@pytest.mark.parametrize("nonfinite", ["NaN", "Infinity", "-Infinity"])
def test_matrix_loader_rejects_nonfinite_values(tmp_path: Path, nonfinite: str) -> None:
    path = tmp_path / "matrix.json"
    path.write_text(f'{{"value":{nonfinite}}}', encoding="utf-8")

    matrix, errors = checker.load_matrix(path)

    assert matrix is None
    assert errors == [f"matrix rejected: non-finite JSON value is forbidden: {nonfinite}"]


def test_matrix_loader_rejects_symlink_nonregular_and_oversized_files(
    tmp_path: Path,
) -> None:
    regular = tmp_path / "regular.json"
    regular.write_text("{}", encoding="utf-8")
    symlink = tmp_path / "symlink.json"
    symlink.symlink_to(regular)
    directory = tmp_path / "directory.json"
    directory.mkdir()
    oversized = tmp_path / "oversized.json"
    oversized.write_bytes(b" " * (checker.MAX_MATRIX_BYTES + 1))

    for path in (symlink, directory, oversized):
        matrix, errors = checker.load_matrix(path)
        assert matrix is None
        assert errors and errors[0].startswith("matrix rejected:")


def test_canonical_matrix_digest_changes_with_semantic_input() -> None:
    matrix = _matrix()
    accepted = checker.validate_matrix(matrix)
    matrix["promotion_boundary"]["claim_status"] = "unreviewed"

    rejected = checker.validate_matrix(matrix)

    assert accepted["matrix_sha256"].startswith("sha256:")
    assert rejected["matrix_sha256"].startswith("sha256:")
    assert accepted["matrix_sha256"] != rejected["matrix_sha256"]


def test_cli_checks_default_recursive_stark_cbc_matrix() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_recursive_stark_cbc_spec.py", "--pretty"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0
    assert proc.stderr == ""
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["schema"] == "zenodex/recursive_stark_cbc_matrix_report/v1"
