"""Adversarial evidence for the O006 V2 exact-subject closure certificate."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
from typing import cast

import pytest

from src.core.m6_safe_mount_types_v1 import (
    M6_RESEARCH_DISABLED_COMMANDS_V1,
    GlobalCommandKindV1,
)
from tools.build_m6_o006_command_lane_completion_v2 import (
    JSON_OUTPUT,
    REPO_ROOT,
    _read_git_blob,
    build_artifact_v2,
    load_stage_a_snapshot_v2,
)
from tools.check_m6_o006_command_lane_completion_v2 import (
    check_m6_o006_command_lane_completion_v2,
)
from tools.m6_o006_command_lane_completion_v2 import (
    ARTIFACT_PATH_V2,
    BASE_COMMIT_V2,
    BASE_TREE_V2,
    EXPECTED_DECISION_ROOT_V2,
    EXPECTED_REGISTRY_ROOT_V2,
    O005_ARTIFACT_COMMIT_V2,
    O005_ARTIFACT_PATH_V2,
    O005_EVIDENCE_SUBJECT_COMMIT_V2,
    O005_EVIDENCE_SUBJECT_TREE_V2,
    O006_REQUIRED_EVIDENCE_V2,
    STAGE_A_SOURCE_PATHS_V2,
    CommandLaneCompletionRejectV2,
    _capability_projection,
    _cross_language_evidence,
    _domain_root,
    _validate_command_registry,
    _validate_o005,
    build_command_lane_completion_artifact_v2,
    canonical_json_bytes_v2,
    validate_command_lane_completion_artifact_v2,
)


def _run_git(root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    environment = {
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "HOME": "/dev/null",
        "LC_ALL": "C",
        "PATH": os.defpath,
    }
    return subprocess.run(
        ["git", "-c", "core.hooksPath=/dev/null", "-C", str(root), *args],
        check=True,
        capture_output=True,
        env=environment,
        text=True,
        timeout=20,
    )


def _copy_stage_a_sources(clone: Path) -> None:
    for relative in STAGE_A_SOURCE_PATHS_V2:
        source = REPO_ROOT / relative
        target = clone / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)


def _isolated_stage_a_clone(tmp_path: Path) -> Path:
    clone = tmp_path / "repo"
    subprocess.run(
        ["git", "clone", "--quiet", "--shared", "--no-checkout", str(REPO_ROOT), str(clone)],
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    _run_git(clone, "checkout", "--quiet", "--detach", BASE_COMMIT_V2)
    _copy_stage_a_sources(clone)
    _run_git(clone, "add", "--", *STAGE_A_SOURCE_PATHS_V2)
    _run_git(
        clone,
        "-c",
        "user.name=O006 Test",
        "-c",
        "user.email=o006@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "O006 V2 synthetic Stage A",
    )
    return clone


def _commit_stage_b(clone: Path) -> bytes:
    raw = build_artifact_v2(clone)
    output = clone / JSON_OUTPUT
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(raw)
    _run_git(clone, "add", "--", ARTIFACT_PATH_V2)
    _run_git(
        clone,
        "-c",
        "user.name=O006 Test",
        "-c",
        "user.email=o006@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "O006 V2 synthetic Stage B",
    )
    return raw


def _commit(clone: Path, message: str, *paths: str) -> None:
    _run_git(clone, "add", "--", *paths)
    _run_git(
        clone,
        "-c",
        "user.name=O006 Test",
        "-c",
        "user.email=o006@example.invalid",
        "commit",
        "--quiet",
        "-m",
        message,
    )


def _semantic_inputs(snapshot) -> tuple[dict[str, object], set[str], set[str]]:
    sources = dict(snapshot.source_bytes)
    registry = json.loads(sources["docs/research/ZENODEX_M6_COMMAND_LANE_REGISTRY_V1.json"])
    manifest = json.loads(sources["docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"])
    _projection, lane_ids, route_ids = _capability_projection(manifest)
    return registry, lane_ids, route_ids


def _assert_zero_authority(report: dict[str, object]) -> None:
    for field in (
        "migration_authority",
        "production_authority",
        "release_authority",
        "settlement_authority",
        "value_movement_authority",
        "verifier_authority",
    ):
        assert report[field] == "NONE"
    assert report["vm_gates_closed"] == []


def _finding_code(report: dict[str, object]) -> str:
    finding = report["finding"]
    assert type(finding) is dict
    code = cast(dict[str, object], finding).get("code")
    assert type(code) is str
    return code


def test_bdd_given_exact_stage_a_when_built_then_current_subject_and_zero_authority_are_explicit(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)

    raw = build_command_lane_completion_artifact_v2(snapshot)
    artifact = json.loads(raw)

    assert artifact["evidence_subject"] == {
        "base_commit": BASE_COMMIT_V2,
        "base_tree": BASE_TREE_V2,
        "stage_a_commit": snapshot.stage_a_commit,
        "stage_a_tree": snapshot.stage_a_tree,
    }
    assert artifact["current_subject"]["commit"] == snapshot.stage_a_commit
    assert artifact["current_subject"]["tree"] == snapshot.stage_a_tree
    assert artifact["command_map"]["decision_root"] == EXPECTED_DECISION_ROOT_V2
    assert artifact["command_map"]["registry_root"] == EXPECTED_REGISTRY_ROOT_V2
    assert artifact["o006_completion"]["required_evidence"] == list(O006_REQUIRED_EVIDENCE_V2)
    assert artifact["dependency"]["artifact_commit"] == O005_ARTIFACT_COMMIT_V2
    assert artifact["dependency"]["subject_commit"] == O005_EVIDENCE_SUBJECT_COMMIT_V2
    assert artifact["dependency"]["subject_tree"] == O005_EVIDENCE_SUBJECT_TREE_V2
    obligation_rows = artifact["current_subject_ledger_rows"]
    assert [row["obligation_id"] for row in obligation_rows[:2]] == ["O-005", "O-006"]
    assert obligation_rows[1]["subject_commit"] == snapshot.stage_a_commit
    assert obligation_rows[1]["subject_tree"] == snapshot.stage_a_tree
    vm_row = obligation_rows[2]
    assert vm_row["ledger"] == "VALUE_MOVEMENT"
    assert vm_row["registered_gate_ids"] == [f"VM-{index:02d}" for index in range(1, 13)]
    assert vm_row["closed_gate_ids"] == []
    assert vm_row["closed_gate_count"] == 0
    assert vm_row["value_movement_claim_allowed"] is False
    assert artifact["claim_ceiling"]["value_movement_gates"] == []
    for field in (
        "migration_authority",
        "production_authority",
        "release_authority",
        "settlement_authority",
        "value_movement_authority",
        "verifier_authority",
    ):
        assert artifact["claim_ceiling"][field] == "NONE"


def test_property_given_closed_command_vocabulary_then_each_command_is_mapped_once(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    artifact = json.loads(build_artifact_v2(clone))

    mapping = artifact["command_map"]
    assert mapping["command_count"] == len(GlobalCommandKindV1)
    assert mapping["mapping_count"] == len(GlobalCommandKindV1)
    assert mapping["registered_commands_mapped_exactly_once"] is True
    assert mapping["canonical_command_order"] is True
    assert mapping["research_disabled_command_count"] == len(M6_RESEARCH_DISABLED_COMMANDS_V1)
    assert mapping["active_new_mapping_count"] == 0
    assert mapping["scope"] == "M6_SAFE_MOUNT_33_ONLY"
    assert mapping["python_rust_command_domain_parity"] is True
    assert mapping["runtime_disabled_guard_parity"] is True
    assert mapping["map_root_binds_capability_manifest"] is True
    assert len(mapping["rows"]) == len(GlobalCommandKindV1)


@pytest.mark.parametrize("mutation", ("omit", "duplicate", "reorder"))
def test_ripr_given_command_cardinality_or_order_mutant_then_direct_semantic_gate_rejects(
    tmp_path: Path,
    mutation: str,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    registry, lane_ids, route_ids = _semantic_inputs(snapshot)
    decisions = registry["decisions"]
    assert type(decisions) is list
    if mutation == "omit":
        decisions.pop()
    elif mutation == "duplicate":
        decisions[-1] = deepcopy(decisions[0])
    else:
        decisions[0], decisions[1] = decisions[1], decisions[0]

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        _validate_command_registry(registry, snapshot.stage_a_commit, lane_ids, route_ids)

    assert raised.value.code == "COMMAND_EXACT_ONCE"


def test_mutation_given_declared_target_substitution_and_paired_root_updates_then_reviewed_root_rejects(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    registry, lane_ids, route_ids = _semantic_inputs(snapshot)
    decisions = registry["decisions"]
    assert type(decisions) is list
    first = decisions[0]
    assert type(first) is dict
    first["target_id"] = "ZUSD_MONETARY"
    decision_payload = {
        "decisions": decisions,
        "schema": "zenodex/m6-command-lane-registry/v1",
    }
    registry["decision_root"] = _domain_root(
        b"zenodex/m6-command-lane-decision-root/v1", decision_payload
    )
    unsigned = {key: value for key, value in registry.items() if key != "registry_root"}
    registry["registry_root"] = _domain_root(b"zenodex/m6-command-lane-registry-root/v1", unsigned)

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        _validate_command_registry(registry, snapshot.stage_a_commit, lane_ids, route_ids)

    assert raised.value.code == "COMMAND_DECISION_ROOT"


def test_mutation_given_undeclared_target_then_manifest_projection_rejects(tmp_path: Path) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    registry, lane_ids, route_ids = _semantic_inputs(snapshot)
    decisions = registry["decisions"]
    assert type(decisions) is list and type(decisions[0]) is dict
    decisions[0]["target_id"] = "UNDECLARED_LANE"

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        _validate_command_registry(registry, snapshot.stage_a_commit, lane_ids, route_ids)

    assert raised.value.code == "UNDECLARED_TARGET"


def test_mutation_given_capability_lane_substitution_then_command_target_binding_rejects(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    sources = dict(snapshot.source_bytes)
    registry = json.loads(sources["docs/research/ZENODEX_M6_COMMAND_LANE_REGISTRY_V1.json"])
    manifest = json.loads(sources["docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"])
    lane = next(row for row in manifest["lanes"] if row["lane_id"] == "SPOT_LIQUIDITY")
    lane["lane_id"] = "SUBSTITUTED_SPOT_LIQUIDITY"
    _projection, lane_ids, route_ids = _capability_projection(manifest)

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        _validate_command_registry(registry, snapshot.stage_a_commit, lane_ids, route_ids)

    assert raised.value.code == "UNDECLARED_TARGET"


def test_mutation_given_active_new_direct_semantic_mutant_then_rejects_with_named_code(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    registry, lane_ids, route_ids = _semantic_inputs(snapshot)
    decisions = registry["decisions"]
    assert type(decisions) is list
    disabled = {command.value for command in M6_RESEARCH_DISABLED_COMMANDS_V1}
    row = next(row for row in decisions if row["command"] in disabled)
    row["status"] = "ACTIVE_NEW"

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        _validate_command_registry(registry, snapshot.stage_a_commit, lane_ids, route_ids)

    assert raised.value.code == "ACTIVE_NEW_MAPPING"


def test_mutation_given_duplicate_command_when_building_then_rejects(tmp_path: Path) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    registry_path = "docs/research/ZENODEX_M6_COMMAND_LANE_REGISTRY_V1.json"
    source_bytes = dict(snapshot.source_bytes)
    registry = json.loads(source_bytes[registry_path])
    registry["decisions"].append(registry["decisions"][0])
    mutant = canonical_json_bytes_v2(registry)
    replaced = tuple(
        (path, mutant if path == registry_path else raw) for path, raw in snapshot.source_bytes
    )

    with pytest.raises(CommandLaneCompletionRejectV2):
        build_command_lane_completion_artifact_v2(replace(snapshot, source_bytes=replaced))


def test_mutation_given_disabled_command_active_new_when_building_then_rejects(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    registry_path = "docs/research/ZENODEX_M6_COMMAND_LANE_REGISTRY_V1.json"
    source_bytes = dict(snapshot.source_bytes)
    registry = json.loads(source_bytes[registry_path])
    disabled = {command.value for command in M6_RESEARCH_DISABLED_COMMANDS_V1}
    row = next(row for row in registry["decisions"] if row["command"] in disabled)
    row["status"] = "ACTIVE_NEW"
    mutant = canonical_json_bytes_v2(registry)
    replaced = tuple(
        (path, mutant if path == registry_path else raw) for path, raw in snapshot.source_bytes
    )

    with pytest.raises(CommandLaneCompletionRejectV2):
        build_command_lane_completion_artifact_v2(replace(snapshot, source_bytes=replaced))


def test_mutation_given_o005_claim_ceiling_promotion_then_dependency_gate_rejects(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    o005 = json.loads(dict(snapshot.source_bytes)[O005_ARTIFACT_PATH_V2])
    o005["claim_ceiling"]["production_authority"] = "ACTIVE_NEW"

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        _validate_o005(o005)

    assert raised.value.code == "O005_AUTHORITY_DRIFT"


def test_mutation_given_o005_evidence_subject_drift_then_final_dependency_gate_rejects(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    o005 = json.loads(dict(snapshot.source_bytes)[O005_ARTIFACT_PATH_V2])
    o005["evidence_subject"]["commit"] = "99667c04980e60b6298e433e33bf3a4efc77e983"

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        _validate_o005(o005)

    assert raised.value.code == "O005_EVIDENCE_SUBJECT"


@pytest.mark.parametrize("source_kind", ("rust", "runtime_guard"))
def test_differential_given_cross_language_or_runtime_domain_drift_then_rejects(
    tmp_path: Path,
    source_kind: str,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    sources = dict(snapshot.source_bytes)
    if source_kind == "rust":
        path = "zk/recursive_stark_v2_risc0/shared/src/m6_core_v1.rs"
        sources[path] = sources[path].replace(
            b"    TauRejoin,\n", b"    TauRejoin,\n    ExtraCommand,\n"
        )
        expected_code = "RUST_COMMAND_DOMAIN"
    else:
        path = "src/core/m6_safe_mount_transition_v1.py"
        sources[path] = sources[path].replace(
            b"        GlobalCommandKindV1.ZRPF_PROVER_REWARD,\n", b""
        )
        expected_code = "RUNTIME_DISABLED_DOMAIN"

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        _cross_language_evidence(sources)

    assert raised.value.code == expected_code


def test_metamorphic_given_same_stage_a_snapshot_then_certificate_bytes_are_identical(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)

    first = build_command_lane_completion_artifact_v2(snapshot)
    second = build_command_lane_completion_artifact_v2(snapshot)

    assert first == second


@pytest.mark.parametrize(
    ("field", "replacement"),
    (("structural_scope_only", 1), ("status", "PROMOTED")),
)
def test_mutation_given_certificate_boolean_or_status_drift_then_exact_projection_rejects(
    tmp_path: Path,
    field: str,
    replacement: object,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    artifact = json.loads(build_command_lane_completion_artifact_v2(snapshot))
    artifact["o006_completion"][field] = replacement
    mutant = canonical_json_bytes_v2(artifact)

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        validate_command_lane_completion_artifact_v2(mutant, snapshot)

    assert raised.value.code == "ARTIFACT_BINDING_DRIFT"


def test_mutation_given_value_movement_gate_promotion_then_exact_projection_rejects(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    snapshot = load_stage_a_snapshot_v2(clone)
    artifact = json.loads(build_command_lane_completion_artifact_v2(snapshot))
    vm_row = artifact["current_subject_ledger_rows"][2]
    vm_row["closed_gate_ids"] = ["VM-01"]
    vm_row["closed_gate_count"] = 1

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        validate_command_lane_completion_artifact_v2(canonical_json_bytes_v2(artifact), snapshot)

    assert raised.value.code == "ARTIFACT_BINDING_DRIFT"


def test_given_real_stage_a_and_artifact_only_stage_b_then_public_checker_accepts(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    raw = _commit_stage_b(clone)

    report = check_m6_o006_command_lane_completion_v2(clone)

    assert report["ok"] is True
    assert report["historical_valid"] is True
    assert report["current_applicable"] is True
    assert report["artifact_sha256"]
    assert raw == (clone / ARTIFACT_PATH_V2).read_bytes()
    assert report["production_authority"] == "NONE"
    assert report["value_movement_authority"] == "NONE"
    assert report["vm_gates_closed"] == []


def test_given_documented_cli_entrypoints_then_builder_and_checker_execute(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    stage_a = _run_git(clone, "rev-parse", "HEAD").stdout.strip()
    environment = {"LC_ALL": "C", "PATH": os.defpath, "PYTHONHASHSEED": "0"}
    built = subprocess.run(
        [
            sys.executable,
            "tools/build_m6_o006_command_lane_completion_v2.py",
            "--root",
            ".",
            "--stage-a",
            stage_a,
        ],
        cwd=clone,
        check=False,
        capture_output=True,
        env=environment,
        text=True,
        timeout=30,
    )
    assert built.returncode == 0, built.stderr
    assert json.loads(built.stdout)["ok"] is True
    _commit(clone, "O006 V2 CLI Stage B", ARTIFACT_PATH_V2)

    checked = subprocess.run(
        [
            sys.executable,
            "tools/check_m6_o006_command_lane_completion_v2.py",
            "--root",
            ".",
        ],
        cwd=clone,
        check=False,
        capture_output=True,
        env=environment,
        text=True,
        timeout=30,
    )
    assert checked.returncode == 0, checked.stderr
    assert json.loads(checked.stdout)["ok"] is True


def test_given_promisor_repository_then_stage_a_loader_rejects_before_snapshot(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    _run_git(clone, "config", "remote.origin.promisor", "true")

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        load_stage_a_snapshot_v2(clone)

    assert raised.value.code == "GIT_PROMISOR_REPOSITORY"


def test_given_git_blob_over_read_ceiling_then_bounded_reader_rejects(tmp_path: Path) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    oversized = clone / "O006_OVERSIZED_BLOB"
    oversized.write_bytes(b"xx")
    blob = _run_git(clone, "hash-object", "-w", "O006_OVERSIZED_BLOB").stdout.strip()

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        _read_git_blob(clone, blob, 1, "O006_OVERSIZED_BLOB")

    assert raised.value.code == "GIT_BLOB_OUTPUT_LIMIT"


def test_given_stage_b_extra_delta_then_public_checker_rejects(tmp_path: Path) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    raw = build_artifact_v2(clone)
    output = clone / ARTIFACT_PATH_V2
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(raw)
    extra = clone / "O006_EXTRA"
    extra.write_text("extra\n", encoding="utf-8")
    _run_git(clone, "add", "--", ARTIFACT_PATH_V2, "O006_EXTRA")
    _run_git(
        clone,
        "-c",
        "user.name=O006 Test",
        "-c",
        "user.email=o006@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "invalid Stage B",
    )

    report = check_m6_o006_command_lane_completion_v2(clone)

    assert report["ok"] is False
    assert report["historical_valid"] is False
    assert report["current_applicable"] is False
    assert _finding_code(report) == "STAGE_B_DELTA"
    assert report["production_authority"] == "NONE"


def test_given_merge_stage_b_then_checker_rejects_multiple_parents(tmp_path: Path) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    stage_a = _run_git(clone, "rev-parse", "HEAD").stdout.strip()
    raw = build_artifact_v2(clone)
    output = clone / ARTIFACT_PATH_V2
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(raw)
    _run_git(clone, "add", "--", ARTIFACT_PATH_V2)
    artifact_tree = _run_git(clone, "write-tree").stdout.strip()
    stage_a_tree = _run_git(clone, "rev-parse", f"{stage_a}^{{tree}}").stdout.strip()
    side = _run_git(
        clone,
        "-c",
        "user.name=O006 Test",
        "-c",
        "user.email=o006@example.invalid",
        "commit-tree",
        stage_a_tree,
        "-p",
        stage_a,
        "-m",
        "side parent",
    ).stdout.strip()
    merge = _run_git(
        clone,
        "-c",
        "user.name=O006 Test",
        "-c",
        "user.email=o006@example.invalid",
        "commit-tree",
        artifact_tree,
        "-p",
        stage_a,
        "-p",
        side,
        "-m",
        "merge Stage B",
    ).stdout.strip()
    _run_git(clone, "checkout", "--quiet", "--detach", merge)

    report = check_m6_o006_command_lane_completion_v2(clone)

    assert report["ok"] is False
    assert report["historical_valid"] is False
    assert _finding_code(report) == "STAGE_A_PARENT"
    _assert_zero_authority(report)


def test_given_stage_a_extra_delta_then_builder_rejects_before_projection(tmp_path: Path) -> None:
    clone = tmp_path / "repo"
    subprocess.run(
        ["git", "clone", "--quiet", "--shared", "--no-checkout", str(REPO_ROOT), str(clone)],
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    _run_git(clone, "checkout", "--quiet", "--detach", BASE_COMMIT_V2)
    _copy_stage_a_sources(clone)
    extra = clone / "O006_STAGE_A_EXTRA"
    extra.write_text("extra\n", encoding="utf-8")
    _commit(clone, "invalid Stage A", *STAGE_A_SOURCE_PATHS_V2, "O006_STAGE_A_EXTRA")

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        load_stage_a_snapshot_v2(clone)

    assert raised.value.code == "STAGE_A_DELTA"


def test_given_intermediate_parent_then_builder_rejects_non_direct_stage_a(tmp_path: Path) -> None:
    clone = tmp_path / "repo"
    subprocess.run(
        ["git", "clone", "--quiet", "--shared", "--no-checkout", str(REPO_ROOT), str(clone)],
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    _run_git(clone, "checkout", "--quiet", "--detach", BASE_COMMIT_V2)
    intermediate = clone / "INTERMEDIATE"
    intermediate.write_text("intermediate\n", encoding="utf-8")
    _commit(clone, "intermediate", "INTERMEDIATE")
    _copy_stage_a_sources(clone)
    _commit(clone, "late Stage A", *STAGE_A_SOURCE_PATHS_V2)

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        load_stage_a_snapshot_v2(clone)

    assert raised.value.code == "BASE_NOT_DIRECT_PARENT"


def test_given_stage_a_symlink_source_then_regular_blob_gate_rejects(tmp_path: Path) -> None:
    clone = tmp_path / "repo"
    subprocess.run(
        ["git", "clone", "--quiet", "--shared", "--no-checkout", str(REPO_ROOT), str(clone)],
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    _run_git(clone, "checkout", "--quiet", "--detach", BASE_COMMIT_V2)
    _copy_stage_a_sources(clone)
    target = clone / STAGE_A_SOURCE_PATHS_V2[-1]
    target.unlink()
    target.symlink_to("../../../../tools/m6_o006_command_lane_completion_v2.py")
    _commit(clone, "symlink Stage A", *STAGE_A_SOURCE_PATHS_V2)

    with pytest.raises(CommandLaneCompletionRejectV2) as raised:
        load_stage_a_snapshot_v2(clone)

    assert raised.value.code == "SOURCE_GIT_ENTRY"


def test_given_harmless_descendant_then_certificate_remains_currently_applicable(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    _commit_stage_b(clone)
    harmless = clone / "O006_HARMLESS"
    harmless.write_text("unrelated\n", encoding="utf-8")
    _run_git(clone, "add", "--", "O006_HARMLESS")
    _run_git(
        clone,
        "-c",
        "user.name=O006 Test",
        "-c",
        "user.email=o006@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "harmless descendant",
    )

    report = check_m6_o006_command_lane_completion_v2(clone)

    assert report["ok"] is True
    assert report["historical_valid"] is True
    assert report["current_applicable"] is True


def test_given_dirty_artifact_then_history_is_valid_and_current_applicability_fails(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    raw = _commit_stage_b(clone)
    artifact = json.loads(raw)
    artifact["status"] = "DIRTY"
    (clone / ARTIFACT_PATH_V2).write_bytes(canonical_json_bytes_v2(artifact))

    report = check_m6_o006_command_lane_completion_v2(clone)

    assert report["ok"] is False
    assert report["historical_valid"] is True
    assert report["current_applicable"] is False
    assert _finding_code(report) == "CURRENT_ARTIFACT_WORKTREE_DRIFT"
    _assert_zero_authority(report)


def test_given_delete_and_readd_artifact_then_history_count_rejects(tmp_path: Path) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    raw = _commit_stage_b(clone)
    (clone / ARTIFACT_PATH_V2).unlink()
    _run_git(clone, "add", "--", ARTIFACT_PATH_V2)
    _run_git(
        clone,
        "-c",
        "user.name=O006 Test",
        "-c",
        "user.email=o006@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "delete artifact",
    )
    (clone / ARTIFACT_PATH_V2).write_bytes(raw)
    _commit(clone, "readd artifact", ARTIFACT_PATH_V2)

    report = check_m6_o006_command_lane_completion_v2(clone)

    assert report["ok"] is False
    assert report["historical_valid"] is False
    assert _finding_code(report) == "ARTIFACT_HISTORY_COUNT"
    _assert_zero_authority(report)


def test_given_noncanonical_committed_artifact_then_historical_projection_rejects(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    canonical = build_artifact_v2(clone)
    pretty = json.dumps(json.loads(canonical), indent=2, sort_keys=True).encode("utf-8")
    output = clone / ARTIFACT_PATH_V2
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(pretty)
    _commit(clone, "noncanonical Stage B", ARTIFACT_PATH_V2)

    report = check_m6_o006_command_lane_completion_v2(clone)

    assert report["ok"] is False
    assert report["historical_valid"] is False
    assert _finding_code(report) == "ARTIFACT_BINDING_DRIFT"
    _assert_zero_authority(report)


def test_given_relevant_source_descendant_drift_then_history_survives_but_current_fails(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    _commit_stage_b(clone)
    source = clone / STAGE_A_SOURCE_PATHS_V2[0]
    source.write_text(source.read_text(encoding="utf-8") + "\n# drift\n", encoding="utf-8")
    _run_git(clone, "add", "--", STAGE_A_SOURCE_PATHS_V2[0])
    _run_git(
        clone,
        "-c",
        "user.name=O006 Test",
        "-c",
        "user.email=o006@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "relevant drift",
    )

    report = check_m6_o006_command_lane_completion_v2(clone)

    assert report["ok"] is False
    assert report["historical_valid"] is True
    assert report["current_applicable"] is False
    assert _finding_code(report) == "CURRENT_SOURCE_DRIFT"


def test_given_dirty_stage_a_source_then_history_survives_but_current_worktree_fails(
    tmp_path: Path,
) -> None:
    clone = _isolated_stage_a_clone(tmp_path)
    _commit_stage_b(clone)
    source = clone / STAGE_A_SOURCE_PATHS_V2[0]
    source.write_text(source.read_text(encoding="utf-8") + "\n# dirty\n", encoding="utf-8")

    report = check_m6_o006_command_lane_completion_v2(clone)

    assert report["ok"] is False
    assert report["historical_valid"] is True
    assert report["current_applicable"] is False
    assert _finding_code(report) == "CURRENT_SOURCE_WORKTREE_DRIFT"
    _assert_zero_authority(report)
