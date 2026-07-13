from __future__ import annotations

import copy
import hashlib
import json
import subprocess
from pathlib import Path

import pytest

from tools import plan_zrpf_source_opened_spot_v6_identity_rebuild as planner

SOURCE_COMMIT = subprocess.check_output(
    ["git", "-C", str(planner.REPO_ROOT), "rev-parse", "HEAD"],
    text=True,
).strip()
RUN_ROOT = "/external/zrpf-v6-identity-rebuild-candidate"


def _image(stage_id: str) -> tuple[str, list[int]]:
    raw = hashlib.sha256(f"image:{stage_id}".encode()).digest()
    return raw.hex(), [
        int.from_bytes(raw[index : index + 4], "little")
        for index in range(0, 32, 4)
    ]


def _program(spec: planner.StageSpec) -> dict:
    image_id, words = _image(spec.stage_id)
    return {
        "artifact_file": spec.artifact_file,
        "program_binary_bytes": 1024 + spec.ordinal,
        "program_binary_sha256": hashlib.sha256(
            f"program:{spec.stage_id}".encode()
        ).hexdigest(),
        "image_id": image_id,
        "image_id_words": words,
    }


def _observations(plan: dict) -> dict:
    stages = []
    programs: list[dict[str, object]] = []
    for spec in planner.STAGES:
        program = _program(spec)
        source_tree_root = (
            plan["tracked_workspace_source_coverage"]["inventory_root_sha256"]
            if spec.stage_id == "source_spot"
            else None
        )
        child_pin = None
        if programs:
            child_pin = {
                "stage_id": planner.STAGES[spec.ordinal - 2].stage_id,
                "image_id": programs[-1]["image_id"],
                "program_binary_sha256": programs[-1]["program_binary_sha256"],
            }
        repins = [
            {
                "path": repin.path,
                "symbol": repin.symbol,
                "value_kind": repin.value_kind,
                "visibility": repin.visibility,
                "value": planner._repin_value(
                    repin.value_kind,
                    program,
                    source_tree_root,
                ),
            }
            for repin in spec.repins
        ]
        stages.append(
            {
                "stage_id": spec.stage_id,
                "ordinal": spec.ordinal,
                "source_snapshot_root_sha256": hashlib.sha256(
                    f"source:{spec.stage_id}".encode()
                ).hexdigest(),
                "source_tree_root_sha256": source_tree_root,
                "canonical_source_root": planner.CANONICAL_SOURCE_ROOT,
                "target_was_absent": True,
                "output_was_absent": True,
                "network_disabled": True,
                "cargo_locked": True,
                "cargo_offline": True,
                "build_jobs": planner.BUILD_JOBS,
                "build_cpus": planner.BUILD_CPUS,
                "build_memory_bytes": planner.BUILD_MEMORY_BYTES,
                "program": program,
                "companion_host_binary": (
                    {
                        "binary_file": "tau-state-proof-risc0-cli",
                        "binary_bytes": 8192,
                        "binary_sha256": hashlib.sha256(b"source-cli").hexdigest(),
                    }
                    if spec.stage_id == "source_spot"
                    else None
                ),
                "child_pin": child_pin,
                "repins": repins,
            }
        )
        programs.append(program)
    settlement = copy.deepcopy(programs[-1])
    final_root = hashlib.sha256(b"final-source").hexdigest()
    return {
        "schema": planner.OBSERVATION_SCHEMA,
        "plan_sha256": planner.canonical_sha256(plan),
        "source_commit": SOURCE_COMMIT,
        "toolchain": copy.deepcopy(planner.TOOLCHAIN),
        "stages": stages,
        "settlement_self_image_two_pass": {
            "host_only_policy_path": planner.STAGES[-1].repins[0].path,
            "host_only_policy_symbol": planner.STAGES[-1].repins[0].symbol,
            "settlement_guest_depends_on_host_only_policy": False,
            "second_pass_source_snapshot_root_sha256": hashlib.sha256(
                b"settlement-second-pass"
            ).hexdigest(),
            "second_pass_program": settlement,
        },
        "final_clean_rebuild": {
            "final_source_snapshot_root_sha256": final_root,
            "canonical_source_root": planner.CANONICAL_SOURCE_ROOT,
            "network_disabled": True,
            "cargo_locked": True,
            "cargo_offline": True,
            "fresh_target_per_stage": True,
            "fresh_output_per_stage": True,
            "programs": copy.deepcopy(programs),
        },
        "host_verifier": {
            "source_snapshot_root_sha256": final_root,
            "expected_settlement_image_id": settlement["image_id"],
            "binary_file": "source-opened-spot-settlement-verifier-v6",
            "binary_bytes": 4096,
            "binary_sha256": hashlib.sha256(b"host-verifier").hexdigest(),
            "canonical_source_root": planner.CANONICAL_SOURCE_ROOT,
            "target_was_absent": True,
            "cargo_locked": True,
            "cargo_offline": True,
            "network_disabled": True,
        },
    }


def _plan() -> dict:
    return planner.build_plan(SOURCE_COMMIT, RUN_ROOT)


def test_plan_is_deterministic_acyclic_and_uses_pinned_build_contract() -> None:
    first = _plan()
    second = _plan()

    assert first == second
    assert first["topology"] == {
        "nodes": list(planner.TOPOLOGY_NODES),
        "edges": [list(edge) for edge in planner.TOPOLOGY_EDGES],
        "acyclic": True,
        "downstream_policy_must_not_feed_upstream_program": True,
    }
    positions = {
        node: index for index, node in enumerate(first["topology"]["nodes"])
    }
    assert all(
        positions[source] < positions[destination]
        for source, destination in first["topology"]["edges"]
    )
    assert [row["stage_id"] for row in first["stages"]] == [
        "source_spot",
        "v1_adapter",
        "v6_leaf",
        "v6_l1",
        "v6_l2",
        "v6_settlement",
    ]
    for row in first["stages"]:
        command = row["command"]
        assert command[0] == planner.CANONICAL_CARGO
        assert "--locked" in command
        assert "--offline" in command
        assert f"{planner.CANONICAL_SOURCE_ROOT}/" in " ".join(command)
        assert command[command.index("--jobs") + 1] == "2"
        assert row["identity_command"][0] == planner.CANONICAL_R0VM
        assert row["identity_command"][-1] == "--id"
        assert row["host_target_directory"].startswith(f"{RUN_ROOT}/targets/")
        assert row["host_output_directory"].startswith(f"{RUN_ROOT}/outputs/")
        assert row["host_target_directory"] != row["host_output_directory"]
    assert first["resource_policy"]["outer_cargo_path"] == planner.CANONICAL_CARGO
    assert first["resource_policy"]["nested_cargo_path"] == planner.CANONICAL_CARGO
    assert first["resource_policy"]["network_disabled"] is True
    assert first["resource_policy"]["build_image"] == planner.BUILD_IMAGE
    assert first["resource_policy"]["r0vm_path"] == planner.CANONICAL_R0VM
    assert all(value is False for value in first["authority"].values())


def test_plan_preserves_historical_v1_anchor_and_requires_versioned_successor() -> None:
    plan = _plan()
    repin_paths = {
        repin["path"]
        for stage in plan["stages"]
        for repin in stage["repins_after_success"]
    }

    assert (
        "config/proof_profiles/zrpf_v1_retained_source_anchor_v1.json"
        not in repin_paths
    )
    assert (
        "config/proof_profiles/zrpf_v1_leaf_adapter_source_policy_v1.json"
        not in repin_paths
    )
    updates = set(plan["required_governance_updates_after_candidate"])
    assert (
        "create config/proof_profiles/zrpf_v1_current_source_anchor_v2.json"
        in updates
    )
    assert (
        "create config/proof_profiles/zrpf_v1_leaf_adapter_source_policy_v2.json"
        in updates
    )
    assert plan["protected_historical_artifacts"] == list(
        planner.PROTECTED_HISTORICAL_ARTIFACTS
    )


def test_tracked_workspace_source_audit_includes_parallel_shard_sources() -> None:
    coverage = _plan()["tracked_workspace_source_coverage"]

    assert coverage["all_tracked_workspace_files_included"] is True
    assert coverage["tracked_file_modes_included"] is True
    assert coverage["explicitly_excluded_tracked_files"] == []
    assert coverage["complete_build_input_closure_verified"] is False
    assert coverage["tracked_file_count"] > 0
    assert coverage["tracked_bytes"] > 0
    assert coverage["parallel_shard_epoch_v1_files"]
    assert all(
        path.startswith(
            "zk/zrpf_protocol/protocol/src/parallel_shard_epoch_v1/"
        )
        for path in coverage["parallel_shard_epoch_v1_files"]
    )


def test_complete_observations_emit_candidate_only_report() -> None:
    plan = _plan()
    report = planner.check_observations(plan, _observations(plan))

    assert report["status"] == "candidate_repin_chain_observations_validated"
    assert report["validated_facts"] == {
        "acyclic_topology_validated": True,
        "child_pins_match_predecessor_programs": True,
        "exact_program_binary_hashes_and_image_ids_recorded": True,
        "final_clean_rebuild_matches_all_primary_programs": True,
        "fresh_external_target_and_output_reported": True,
        "locked_offline_builds_reported": True,
        "network_disabled_builds_reported": True,
        "settlement_host_only_two_pass_match": True,
        "source_anchor_matches_tracked_workspace_inventory": True,
    }
    assert all(report["authority"][field] is False for field in planner.AUTHORITY_FLAGS)
    assert report["programs"][-1]["stage_id"] == "v6_settlement"
    assert report["source_spot_cli"]["binary_file"] == "tau-state-proof-risc0-cli"
    assert "host_run_root" not in report
    assert report["observations_sha256"] == planner.canonical_sha256(
        _observations(plan)
    )


def test_source_stage_repins_image_program_hash_and_source_tree_root() -> None:
    plan = _plan()
    observations = _observations(plan)
    source = observations["stages"][0]

    planner.check_observations(plan, observations)
    values = {row["symbol"]: row["value"] for row in source["repins"]}
    assert values["PINNED_SPOT_LEAF_IMAGE_ID_V1"] == source["program"][
        "image_id_words"
    ]
    assert values["PINNED_SPOT_LEAF_PROGRAM_SHA256_V1"] == list(
        bytes.fromhex(source["program"]["program_binary_sha256"])
    )
    assert values["PINNED_V1_LOCAL_SOURCE_TREE_ROOT"] == list(
        bytes.fromhex(source["source_tree_root_sha256"])
    )


def test_source_tree_root_must_equal_tracked_workspace_inventory() -> None:
    plan = _plan()
    observations = _observations(plan)
    observations["stages"][0]["source_tree_root_sha256"] = "f" * 64
    observations["stages"][0]["repins"][2]["value"] = [255] * 32

    with pytest.raises(planner.RebuildPlanError, match="source tree root mismatch"):
        planner.check_observations(plan, observations)


def test_child_pin_substitution_rejects() -> None:
    plan = _plan()
    observations = _observations(plan)
    observations["stages"][3]["child_pin"]["image_id"] = "0" * 64

    with pytest.raises(planner.RebuildPlanError, match="child image ID mismatch"):
        planner.check_observations(plan, observations)


def test_final_rebuild_detects_downstream_feedback_into_upstream_program() -> None:
    plan = _plan()
    observations = _observations(plan)
    observations["final_clean_rebuild"]["programs"][0][
        "program_binary_sha256"
    ] = "1" * 64

    with pytest.raises(
        planner.RebuildPlanError,
        match="final rebuild identity for source_spot mismatch",
    ):
        planner.check_observations(plan, observations)


def test_settlement_host_only_second_pass_must_be_byte_identical() -> None:
    plan = _plan()
    observations = _observations(plan)
    observations["settlement_self_image_two_pass"]["second_pass_program"][
        "program_binary_sha256"
    ] = "2" * 64

    with pytest.raises(
        planner.RebuildPlanError,
        match="settlement two-pass program identity mismatch",
    ):
        planner.check_observations(plan, observations)


def test_settlement_guest_dependency_on_host_self_pin_rejects() -> None:
    plan = _plan()
    observations = _observations(plan)
    observations["settlement_self_image_two_pass"][
        "settlement_guest_depends_on_host_only_policy"
    ] = True

    with pytest.raises(
        planner.RebuildPlanError,
        match="settlement guest host-only dependency mismatch",
    ):
        planner.check_observations(plan, observations)


def test_noncanonical_image_word_order_rejects() -> None:
    plan = _plan()
    observations = _observations(plan)
    observations["stages"][2]["program"]["image_id_words"].reverse()

    with pytest.raises(planner.RebuildPlanError, match="do not encode"):
        planner.check_observations(plan, observations)


def test_plan_mutation_rejects_before_observation_interpretation() -> None:
    plan = _plan()
    observations = _observations(plan)
    plan["resource_policy"]["cargo_offline"] = False

    with pytest.raises(planner.RebuildPlanError, match="deterministic plan"):
        planner.check_observations(plan, observations)


def test_loader_rejects_duplicate_keys_and_noncanonical_bytes(tmp_path: Path) -> None:
    duplicate = tmp_path / "duplicate.json"
    duplicate.write_text('{"schema":"a","schema":"b"}\n', encoding="utf-8")
    with pytest.raises(planner.RebuildPlanError, match="duplicate JSON key"):
        planner.load_canonical_json(duplicate, "fixture")

    noncanonical = tmp_path / "noncanonical.json"
    noncanonical.write_text(json.dumps({"schema": "a"}) + "\n", encoding="utf-8")
    with pytest.raises(planner.RebuildPlanError, match="canonical JSON"):
        planner.load_canonical_json(noncanonical, "fixture")


def test_git_inventory_parser_rejects_control_characters_in_paths() -> None:
    malformed = b"100644 blob " + b"0" * 40 + b"\tbad\npath\0"

    with pytest.raises(planner.RebuildPlanError, match="path is invalid"):
        planner._parse_ls_tree(malformed)


def test_cli_plan_refuses_run_root_inside_repository(tmp_path: Path) -> None:
    inside = planner.REPO_ROOT / "untracked-v6-run"
    assert not inside.exists()

    result = planner.main(
        [
            "plan",
            "--source-commit",
            SOURCE_COMMIT,
            "--run-root",
            str(inside),
        ]
    )

    assert result == 2
