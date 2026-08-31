"""Adversarial evidence for the O-007B V3 exact current-subject receipt."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any, Callable

import pytest

from tools.build_o007b_cross_language_sink_closure_v3 import (
    collect_inventory_evidence_v3,
)
from tools.check_o007b_cross_language_sink_closure_v3 import (
    check_o007b_cross_language_sink_closure_v3,
)
from tools.m6_cross_language_sinks.inventory import compare_projection_to_manifest
from tools.o007b_cross_language_sink_closure_v3 import (
    ARTIFACT_PATH_V3,
    BASE_COMMIT_V3,
    CURRENT_CHANGED_SOURCE_PATHS_V3,
    EXPECTED_INVENTORY_V3,
    MANIFEST_PATH_V3,
    O006_ARTIFACT_SHA256_V3,
    O006_CERTIFICATE_ROOT_V3,
    O007A_ARTIFACT_SHA256_V3,
    O007A_CERTIFICATE_ROOT_V3,
    O007A_STAGE_A_V3,
    O007A_STAGE_B_V3,
    PREDECESSOR_ARTIFACT_SHA256_V2,
    STAGE_A_SOURCE_PATHS_V3,
    V2_PRESERVED_PATHS,
    O007BClosureRejectV3,
    StageASnapshotV3,
    build_artifact_v3,
    canonical_json_bytes_v3,
    certificate_root_v3,
    validate_artifact_v3,
)

ROOT = Path(__file__).resolve().parents[1]


def _snapshot() -> StageASnapshotV3:
    return StageASnapshotV3(
        stage_a_commit="1" * 40,
        stage_a_tree="2" * 40,
        stage_a_source_pins=(),
        evidence_source_pins=(),
    )


def _dependency_reports() -> tuple[dict[str, object], dict[str, object]]:
    shared: dict[str, object] = {
        "current_applicable": True,
        "finding": None,
        "historical_valid": True,
        "migration_authority": "NONE",
        "ok": True,
        "production_authority": "NONE",
        "release_authority": "NONE",
        "settlement_authority": "NONE",
        "value_movement_authority": "NONE",
        "verifier_authority": "NONE",
        "vm_gates_closed": [],
    }
    o007a = {
        **shared,
        "artifact_sha256": O007A_ARTIFACT_SHA256_V3,
        "certificate_root": O007A_CERTIFICATE_ROOT_V3,
        "schema": "zenodex/o007a-deployed-sink-closure-check/v2",
        "stage_a_commit": O007A_STAGE_A_V3,
        "stage_b_commit": O007A_STAGE_B_V3,
        "vm01_status": "OPEN",
    }
    o006 = {
        **shared,
        "artifact_sha256": O006_ARTIFACT_SHA256_V3,
        "certificate_root": O006_CERTIFICATE_ROOT_V3,
        "schema": "zenodex/m6-o006-command-lane-completion-check/v2",
    }
    return o007a, o006


def _inventory() -> dict[str, object]:
    return {
        **EXPECTED_INVENTORY_V3,
        "command_lane_consistency": {"rust_lane_ids_v2": ["SPOT_LIQUIDITY"]},
        "generated_replay_ownership_complete": False,
        "language_operation_definitions": {
            "PYTHON": [],
            "RUST": [],
            "SHELL": [],
            "TAU": [],
        },
        "manifest_sha256": "3" * 64,
        "report_findings": [],
        "report_ok": True,
        "release_ready": False,
        "vm01_status": "OPEN",
    }


def _artifact_bytes() -> tuple[StageASnapshotV3, bytes]:
    snapshot = _snapshot()
    o007a, o006 = _dependency_reports()
    artifact = build_artifact_v3(
        snapshot,
        inventory=_inventory(),
        o007a_check=o007a,
        o006_check=o006,
    )
    return snapshot, canonical_json_bytes_v3(artifact)


def _recertified(raw: bytes, mutation: Callable[[dict[str, Any]], None]) -> bytes:
    artifact: dict[str, Any] = json.loads(raw)
    mutation(artifact)
    payload = {key: value for key, value in artifact.items() if key != "certificate_root"}
    artifact["certificate_root"] = certificate_root_v3(payload)
    return canonical_json_bytes_v3(artifact)


def test_bdd_exact_current_subject_closes_only_bounded_o007b_gap() -> None:
    _snapshot_value, raw = _artifact_bytes()
    artifact = json.loads(raw)

    assert artifact["implementation_subject"]["parent"] == BASE_COMMIT_V3
    assert artifact["obligation"]["gap_closed"] == "cross_language_sink_coverage_gap"
    assert artifact["obligation"]["residual_aggregate_gaps"] == [
        "user_story_closure",
        "recovery_and_administrative_reachability",
        "terminal_path_closure",
    ]
    assert artifact["predecessor_v2"]["artifact_sha256"] == PREDECESSOR_ARTIFACT_SHA256_V2
    assert artifact["reviewed_source_delta_from_v2"]["changed_source_row_count"] == 4
    assert artifact["reviewed_source_delta_from_v2"]["operation_delta_count"] == 0
    assert [row["path"] for row in artifact["reviewed_source_delta_from_v2"]["rows"]] == list(
        CURRENT_CHANGED_SOURCE_PATHS_V3
    )
    assert artifact["claim_ceiling"]["release_ready"] is False
    assert artifact["claim_ceiling"]["vm_01_status"] == "OPEN"
    assert artifact["claim_ceiling"]["value_movement_authority"] == "NONE"


@pytest.mark.parametrize(
    "mutation",
    [
        lambda artifact: artifact["claim_ceiling"].__setitem__(
            "value_movement_authority", "GRANTED"
        ),
        lambda artifact: artifact["claim_ceiling"].__setitem__("vm_01_status", "CLOSED"),
        lambda artifact: artifact["dependency_bindings"]["o_007a"].__setitem__(
            "certificate_root", "0" * 64
        ),
        lambda artifact: artifact["inventory_evidence"].__setitem__(
            "dynamic_import_declaration_count", 13
        ),
        lambda artifact: artifact["inventory_evidence"].__setitem__(
            "unresolved_dynamic_import_count", 0
        ),
        lambda artifact: artifact["inventory_evidence"].__setitem__(
            "projection_root", "0" * 64
        ),
        lambda artifact: artifact["predecessor_v2"].__setitem__(
            "artifact_sha256", "0" * 64
        ),
        lambda artifact: artifact["reviewed_source_delta_from_v2"].__setitem__(
            "operation_delta_count", 1
        ),
    ],
)
def test_recertified_authority_count_or_root_mutant_rejects(
    mutation: Callable[[dict[str, Any]], None],
) -> None:
    snapshot, raw = _artifact_bytes()

    with pytest.raises(O007BClosureRejectV3):
        validate_artifact_v3(_recertified(raw, mutation), snapshot)


def test_noncanonical_and_duplicate_artifact_json_reject() -> None:
    snapshot, raw = _artifact_bytes()
    noncanonical = (json.dumps(json.loads(raw), indent=2) + "\n").encode()

    with pytest.raises(O007BClosureRejectV3) as noncanonical_error:
        validate_artifact_v3(noncanonical, snapshot)
    assert noncanonical_error.value.code == "ARTIFACT_CANONICAL"

    duplicate = raw.replace(b'{"bounded_delta":', b'{"schema":"duplicate","bounded_delta":', 1)
    with pytest.raises(O007BClosureRejectV3) as duplicate_error:
        validate_artifact_v3(duplicate, snapshot)
    assert duplicate_error.value.code == "DUPLICATE_JSON_KEY"


def test_reviewed_manifest_rejects_changed_projection() -> None:
    manifest: dict[str, Any] = json.loads((ROOT / MANIFEST_PATH_V3).read_bytes())
    projection = copy.deepcopy(manifest["projection"])
    projection["operation_occurrence_counts"]["RUST"] += 1

    assert compare_projection_to_manifest(manifest["projection"], manifest) == ()
    assert compare_projection_to_manifest(projection, manifest) == (
        "cross-language projection does not match the reviewed manifest",
    )


def test_reviewed_manifest_matches_exact_current_projection_and_counts() -> None:
    evidence = collect_inventory_evidence_v3(ROOT)

    for key, expected in EXPECTED_INVENTORY_V3.items():
        assert evidence[key] == expected
    assert evidence["report_findings"] == []
    assert evidence["report_ok"] is True
    assert evidence["release_ready"] is False
    assert evidence["vm01_status"] == "OPEN"
    assert evidence["manifest_sha256"] == hashlib.sha256(
        (ROOT / MANIFEST_PATH_V3).read_bytes()
    ).hexdigest()


def test_repository_stage_topology_preserves_v2_and_is_current_when_present() -> None:
    if not (ROOT / ARTIFACT_PATH_V3).is_file():
        pytest.skip("artifact-only Stage B has not been created yet")

    report = check_o007b_cross_language_sink_closure_v3(ROOT)

    assert report["ok"] is True
    assert report["historical_valid"] is True
    assert report["current_applicable"] is True
    assert report["release_ready"] is False
    assert report["vm01_status"] == "OPEN"
    assert report["vm_gates_closed"] == []
    stage_a = str(report["stage_a_commit"])
    delta = subprocess.run(
        [
            "git",
            "diff-tree",
            "--no-commit-id",
            "--name-status",
            "--no-renames",
            "-r",
            stage_a,
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    assert delta == [f"A\t{path}" for path in STAGE_A_SOURCE_PATHS_V3]
    for path in V2_PRESERVED_PATHS:
        base_blob = subprocess.run(
            ["git", "rev-parse", f"{BASE_COMMIT_V3}:{path}"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout
        stage_blob = subprocess.run(
            ["git", "rev-parse", f"{stage_a}:{path}"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout
        assert stage_blob == base_blob


def test_current_checker_rejects_new_cross_language_writer(tmp_path: Path) -> None:
    if not (ROOT / ARTIFACT_PATH_V3).is_file():
        pytest.skip("artifact-only Stage B has not been created yet")
    clone = tmp_path / "repo"
    subprocess.run(
        ["git", "clone", "--quiet", "--shared", str(ROOT), str(clone)],
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
    )
    target = clone / "zk" / "global_settlement_abi_v2" / "src" / "lib.rs"
    target.write_text(
        target.read_text(encoding="utf-8")
        + "\nuse std::fs::rename as archive_v3_snapshot;\n"
        + '#[allow(dead_code)] fn o007b_v3_mutant() { let _ = archive_v3_snapshot("a", "b"); }\n',
        encoding="utf-8",
    )

    report = check_o007b_cross_language_sink_closure_v3(clone)

    assert report["ok"] is False
    assert report["historical_valid"] is True
    assert report["current_applicable"] is False
    finding = report["finding"]
    assert isinstance(finding, dict)
    assert finding["code"] == "INVENTORY_REPORT"
