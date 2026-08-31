"""Adversarial evidence for the bounded O-007A exact-subject receipt."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
from copy import deepcopy
from pathlib import Path

import pytest

from tools.build_o007a_deployed_sink_closure_v2 import build_artifact_v2
from tools.check_o007a_deployed_sink_closure_v2 import (
    check_o007a_deployed_sink_closure_v2,
)
from tools.o007a_deployed_sink_closure_v2 import (
    ARTIFACT_PATH_V2,
    BASE_COMMIT_V2,
    EVIDENCE_SOURCE_PATHS_V2,
    EXPECTED_CLOSURE_V2,
    LAUNCHER_SOURCE_PATHS_V2,
    O006_ARTIFACT_SHA256_V2,
    O006_CERTIFICATE_ROOT_V2,
    PLAN_COMMIT_V2,
    REJECTED_ARTIFACT_PATH_V1,
    REJECTED_DONOR_COMMIT_V2,
    REPAIR_DONOR_COMMIT_V2,
    SELECTED_DONOR_COMMIT_V2,
    SELECTED_PROFILE_ID_V2,
    STAGE_A_SOURCE_PATHS_V2,
    CurrentEvidenceV2,
    O007AClosureRejectV2,
    SourcePinV2,
    StageASnapshotV2,
    build_o007a_artifact_v2,
    canonical_json_bytes_v2,
    canonical_root_v2,
    validate_o007a_artifact_v2,
)

ROOT = Path(__file__).resolve().parents[1]


def _pin(path: str) -> SourcePinV2:
    raw = (ROOT / path).read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    mode = "100755" if os.access(ROOT / path, os.X_OK) else "100644"
    return SourcePinV2(
        path=path,
        git_blob_sha=digest[:40],
        git_mode=mode,
        sha256=digest,
        size_bytes=len(raw),
    )


def _snapshot() -> StageASnapshotV2:
    return StageASnapshotV2(
        stage_a_commit="1" * 40,
        stage_a_tree="2" * 40,
        stage_a_source_pins=tuple(_pin(path) for path in STAGE_A_SOURCE_PATHS_V2),
        evidence_source_pins=tuple(_pin(path) for path in EVIDENCE_SOURCE_PATHS_V2),
    )


def _evidence(snapshot: StageASnapshotV2) -> CurrentEvidenceV2:
    pins = {pin.path: pin for pin in snapshot.evidence_source_pins}
    return CurrentEvidenceV2(
        closure=dict(EXPECTED_CLOSURE_V2),
        launcher_sources=tuple(
            {"path": path, "sha256": pins[path].sha256} for path in LAUNCHER_SOURCE_PATHS_V2
        ),
    )


def _mutated(raw: bytes, change) -> bytes:
    artifact = json.loads(raw)
    change(artifact)
    body = {key: value for key, value in artifact.items() if key != "certificate_root"}
    artifact["certificate_root"] = canonical_root_v2(body)
    return canonical_json_bytes_v2(artifact)


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
        timeout=30,
    )


def _synthetic_stage_a(tmp_path: Path) -> Path:
    clone = tmp_path / "repo"
    subprocess.run(
        ["git", "clone", "--quiet", "--shared", "--no-checkout", str(ROOT), str(clone)],
        check=True,
        capture_output=True,
        text=True,
        timeout=30,
    )
    _run_git(clone, "checkout", "--quiet", "--detach", BASE_COMMIT_V2)
    for relative in STAGE_A_SOURCE_PATHS_V2:
        target = clone / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / relative, target)
    _run_git(clone, "add", "--", *STAGE_A_SOURCE_PATHS_V2)
    _run_git(
        clone,
        "-c",
        "user.name=O007A Test",
        "-c",
        "user.email=o007a@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "O007A synthetic Stage A",
    )
    return clone


def _commit_stage_b(clone: Path) -> bytes:
    raw = build_artifact_v2(clone)
    output = clone / ARTIFACT_PATH_V2
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(raw)
    _run_git(clone, "add", "--", ARTIFACT_PATH_V2)
    _run_git(
        clone,
        "-c",
        "user.name=O007A Test",
        "-c",
        "user.email=o007a@example.invalid",
        "commit",
        "--quiet",
        "-m",
        "O007A synthetic Stage B",
    )
    return raw


def test_bdd_given_exact_stage_a_then_receipt_closes_only_o007a_delta() -> None:
    snapshot = _snapshot()
    raw = build_o007a_artifact_v2(snapshot, _evidence(snapshot))
    artifact = json.loads(raw)

    assert artifact["implementation_subject"]["commit"] == snapshot.stage_a_commit
    assert artifact["implementation_subject"]["tree"] == snapshot.stage_a_tree
    assert artifact["obligation"] == {
        "contributes_to": ["VM-01"],
        "gap_closed": "deployed_launcher_sink_coverage_gap",
        "obligation_id": "O-007A",
        "status": "RESEARCH_ONLY_O007A_DEPLOYED_PROFILE_CLOSURE_COMPLETE_NO_VM_GATE",
    }
    assert artifact["claim_ceiling"]["vm_01_status"] == "OPEN"
    assert artifact["claim_ceiling"]["closed_value_movement_gates"] == 0
    assert set(artifact["claim_ceiling"].values()) >= {"NONE", "OPEN", 0}


def test_dependency_receipts_are_exact_and_zero_authority() -> None:
    snapshot = _snapshot()
    artifact = json.loads(build_o007a_artifact_v2(snapshot, _evidence(snapshot)))

    assert artifact["dependencies"]["active_plan"]["plan_commit"] == PLAN_COMMIT_V2
    o006 = artifact["dependencies"]["o_006"]
    assert o006["artifact_sha256"] == O006_ARTIFACT_SHA256_V2
    assert o006["certificate_root"] == O006_CERTIFICATE_ROOT_V2
    assert o006["vm_gates_closed"] == []
    assert artifact["claim_ceiling"]["value_movement_authority"] == "NONE"


def test_donor_selection_is_deterministic_and_rejects_old_receipt() -> None:
    snapshot = _snapshot()
    artifact = json.loads(build_o007a_artifact_v2(snapshot, _evidence(snapshot)))

    selection = artifact["donor_selection"]
    assert selection["selected"]["commit"] == SELECTED_DONOR_COMMIT_V2
    assert selection["rejected"]["commit"] == REJECTED_DONOR_COMMIT_V2
    assert selection["repair_donor"]["commit"] == REPAIR_DONOR_COMMIT_V2
    assert len(selection["selected"]["write_set"]) > len(selection["rejected"]["write_set"])
    assert selection["restage_relation"]["reviewed_delta_paths"] == [
        "tests/test_check_m6_value_sinks_v2.py",
        "tools/m6_value_sinks/operations.py",
    ]
    assert artifact["rejected_prior_receipt"]["path"] == REJECTED_ARTIFACT_PATH_V1
    assert artifact["rejected_prior_receipt"]["disposition"].startswith("REJECTED_STALE_O006")


def test_selected_profile_binds_exact_launcher_sources_and_static_ceiling() -> None:
    snapshot = _snapshot()
    artifact = json.loads(build_o007a_artifact_v2(snapshot, _evidence(snapshot)))

    profile = artifact["deployment_profile"]
    closure = artifact["deployment_closure"]
    assert profile["selected_profile"]["profile_id"] == SELECTED_PROFILE_ID_V2
    assert closure["launcher_source_count"] == len(LAUNCHER_SOURCE_PATHS_V2)
    assert [row["path"] for row in closure["launcher_sources"]] == list(LAUNCHER_SOURCE_PATHS_V2)
    assert closure["classified_identity_count"] == 162
    assert closure["observed_occurrence_count"] == 181
    assert closure["static_scanned_module_count"] == 463
    assert closure["declared_closure_gap_count"] == 26
    assert closure["unmediated_static_writer_count"] == 54
    assert closure["static_reachable_unscanned_module_count"] == 1
    assert closure["release_ready"] is False


def test_metamorphic_same_snapshot_produces_identical_canonical_bytes() -> None:
    snapshot = _snapshot()
    evidence = _evidence(snapshot)

    assert build_o007a_artifact_v2(snapshot, evidence) == build_o007a_artifact_v2(
        snapshot, evidence
    )


def test_mutation_given_launcher_source_root_drift_then_projection_rejects() -> None:
    snapshot = _snapshot()
    raw = build_o007a_artifact_v2(snapshot, _evidence(snapshot))
    mutant = _mutated(
        raw,
        lambda artifact: artifact["deployment_closure"].__setitem__(
            "launcher_sources_root", "0" * 64
        ),
    )

    with pytest.raises(O007AClosureRejectV2) as raised:
        validate_o007a_artifact_v2(mutant, snapshot)

    assert raised.value.code == "ARTIFACT_BINDING_DRIFT"


@pytest.mark.parametrize(
    "mutation",
    [
        lambda artifact: artifact["claim_ceiling"].__setitem__(
            "value_movement_authority", "GRANTED"
        ),
        lambda artifact: artifact["claim_ceiling"].__setitem__("vm_01_status", "CLOSED"),
        lambda artifact: artifact["dependencies"]["o_006"].__setitem__(
            "certificate_root", "0" * 64
        ),
        lambda artifact: artifact["donor_selection"]["selected"].__setitem__(
            "commit", REJECTED_DONOR_COMMIT_V2
        ),
    ],
)
def test_mutation_given_authority_dependency_or_donor_drift_then_rejects(mutation) -> None:
    snapshot = _snapshot()
    raw = build_o007a_artifact_v2(snapshot, _evidence(snapshot))

    with pytest.raises(O007AClosureRejectV2) as raised:
        validate_o007a_artifact_v2(_mutated(raw, mutation), snapshot)

    assert raised.value.code == "ARTIFACT_BINDING_DRIFT"


def test_mutation_given_census_root_drift_then_live_evidence_rejects() -> None:
    snapshot = _snapshot()
    closure = deepcopy(EXPECTED_CLOSURE_V2)
    closure["static_scanned_module_count"] = 462

    with pytest.raises(O007AClosureRejectV2) as raised:
        build_o007a_artifact_v2(
            snapshot,
            CurrentEvidenceV2(
                closure=closure, launcher_sources=_evidence(snapshot).launcher_sources
            ),
        )

    assert raised.value.code == "CLOSURE_EVIDENCE_DRIFT"


def test_noncanonical_or_duplicate_json_rejects() -> None:
    snapshot = _snapshot()
    raw = build_o007a_artifact_v2(snapshot, _evidence(snapshot))
    artifact = json.loads(raw)
    noncanonical = (json.dumps(artifact, indent=2) + "\n").encode()

    with pytest.raises(O007AClosureRejectV2) as noncanonical_error:
        validate_o007a_artifact_v2(noncanonical, snapshot)
    assert noncanonical_error.value.code == "ARTIFACT_NONCANONICAL"

    duplicate = raw.replace(b'{"bounded_delta":', b'{"schema":"duplicate","bounded_delta":', 1)
    with pytest.raises(O007AClosureRejectV2) as duplicate_error:
        validate_o007a_artifact_v2(duplicate, snapshot)
    assert duplicate_error.value.code == "DUPLICATE_JSON_KEY"


def test_given_synthetic_exact_stage_a_and_artifact_only_stage_b_checker_accepts(
    tmp_path: Path,
) -> None:
    clone = _synthetic_stage_a(tmp_path)
    raw = _commit_stage_b(clone)

    report = check_o007a_deployed_sink_closure_v2(clone)

    assert report["ok"] is True
    assert report["historical_valid"] is True
    assert report["current_applicable"] is True
    assert report["vm01_status"] == "OPEN"
    assert report["vm_gates_closed"] == []
    assert report["value_movement_authority"] == "NONE"
    assert raw == (clone / ARTIFACT_PATH_V2).read_bytes()


def test_repository_stage_b_is_current_when_present() -> None:
    if not (ROOT / ARTIFACT_PATH_V2).is_file():
        pytest.skip("artifact-only Stage B has not been created yet")

    report = check_o007a_deployed_sink_closure_v2(ROOT)

    assert report["ok"] is True
    assert report["historical_valid"] is True
    assert report["current_applicable"] is True
    assert report["vm01_status"] == "OPEN"
