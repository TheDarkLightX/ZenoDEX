"""Adversarial evidence for the bounded O-007B exact-subject receipt."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
from pathlib import Path

import pytest

from tools.check_o007b_cross_language_sink_closure_v2 import (
    check_o007b_cross_language_sink_closure_v2,
)
from tools.o007b_cross_language_sink_closure_v2 import (
    ARTIFACT_PATH_V2,
    BASE_COMMIT_V2,
    EVIDENCE_SOURCE_PATHS_V2,
    O006_ARTIFACT_SHA256_V2,
    O006_CERTIFICATE_ROOT_V2,
    O007A_ARTIFACT_SHA256_V2,
    O007A_CERTIFICATE_ROOT_V2,
    O007A_STAGE_A_V2,
    O007A_STAGE_B_V2,
    STAGE_A_SOURCE_PATHS_V2,
    O007BClosureRejectV2,
    SourcePinV2,
    StageASnapshotV2,
    build_artifact_v2,
    canonical_json_bytes_v2,
    certificate_root_v2,
    validate_artifact_v2,
)

ROOT = Path(__file__).resolve().parents[1]


def _pin(path: str) -> SourcePinV2:
    raw = (ROOT / path).read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    return SourcePinV2(
        path=path,
        git_blob_sha=digest[:40],
        git_mode="100755" if os.access(ROOT / path, os.X_OK) else "100644",
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
        "artifact_sha256": O007A_ARTIFACT_SHA256_V2,
        "certificate_root": O007A_CERTIFICATE_ROOT_V2,
        "schema": "zenodex/o007a-deployed-sink-closure-check/v2",
        "stage_a_commit": O007A_STAGE_A_V2,
        "stage_b_commit": O007A_STAGE_B_V2,
        "vm01_status": "OPEN",
    }
    o006 = {
        **shared,
        "artifact_sha256": O006_ARTIFACT_SHA256_V2,
        "certificate_root": O006_CERTIFICATE_ROOT_V2,
        "schema": "zenodex/m6-o006-command-lane-completion-check/v2",
    }
    return o007a, o006


def _inventory() -> dict[str, object]:
    return {
        "command_lane_consistency": {"rust_lane_ids_v2": ["SPOT_LIQUIDITY"]},
        "generated_replay_ownership_complete": False,
        "language_operation_definitions": {
            "PYTHON": [],
            "RUST": [],
            "SHELL": [],
            "TAU": [],
        },
        "report_ok": True,
        "release_ready": False,
        "unmediated_operation_count": 1,
        "unresolved_dynamic_import_count": 1,
        "vm01_status": "OPEN",
    }


def _artifact_bytes() -> tuple[StageASnapshotV2, bytes]:
    snapshot = _snapshot()
    o007a, o006 = _dependency_reports()
    artifact = build_artifact_v2(
        snapshot,
        inventory=_inventory(),
        o007a_check=o007a,
        o006_check=o006,
    )
    return snapshot, canonical_json_bytes_v2(artifact)


def _recertified(raw: bytes, mutation) -> bytes:
    artifact = json.loads(raw)
    mutation(artifact)
    payload = {key: value for key, value in artifact.items() if key != "certificate_root"}
    artifact["certificate_root"] = certificate_root_v2(payload)
    return canonical_json_bytes_v2(artifact)


def test_bdd_exact_subject_closes_only_bounded_o007b_gap() -> None:
    _snapshot_value, raw = _artifact_bytes()
    artifact = json.loads(raw)

    assert artifact["implementation_subject"]["parent"] == BASE_COMMIT_V2
    assert artifact["obligation"]["gap_closed"] == "cross_language_sink_coverage_gap"
    assert artifact["obligation"]["residual_aggregate_gaps"] == [
        "user_story_closure",
        "recovery_and_administrative_reachability",
        "terminal_path_closure",
    ]
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
            "unresolved_dynamic_import_count", 0
        ),
    ],
)
def test_recertified_authority_dependency_or_gap_mutant_rejects(mutation) -> None:
    snapshot, raw = _artifact_bytes()

    with pytest.raises(O007BClosureRejectV2):
        validate_artifact_v2(_recertified(raw, mutation), snapshot)


def test_noncanonical_and_duplicate_json_reject() -> None:
    snapshot, raw = _artifact_bytes()
    noncanonical = (json.dumps(json.loads(raw), indent=2) + "\n").encode()

    with pytest.raises(O007BClosureRejectV2) as noncanonical_error:
        validate_artifact_v2(noncanonical, snapshot)
    assert noncanonical_error.value.code == "ARTIFACT_CANONICAL"

    duplicate = raw.replace(b'{"bounded_delta":', b'{"schema":"duplicate","bounded_delta":', 1)
    with pytest.raises(O007BClosureRejectV2) as duplicate_error:
        validate_artifact_v2(duplicate, snapshot)
    assert duplicate_error.value.code == "DUPLICATE_JSON_KEY"


def test_repository_stage_b_is_current_when_present() -> None:
    if not (ROOT / ARTIFACT_PATH_V2).is_file():
        pytest.skip("artifact-only Stage B has not been created yet")

    report = check_o007b_cross_language_sink_closure_v2(ROOT)

    assert report["ok"] is True
    assert report["historical_valid"] is True
    assert report["current_applicable"] is True
    assert report["release_ready"] is False
    assert report["vm01_status"] == "OPEN"
    assert report["vm_gates_closed"] == []


def test_current_checker_rejects_cross_language_writer_mutation(tmp_path: Path) -> None:
    if not (ROOT / ARTIFACT_PATH_V2).is_file():
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
        + "\nuse std::fs::rename as archive_snapshot;\n"
        + '#[allow(dead_code)] fn o007b_mutant() { let _ = archive_snapshot("old", "new"); }\n',
        encoding="utf-8",
    )

    report = check_o007b_cross_language_sink_closure_v2(clone)

    assert report["ok"] is False
    assert report["historical_valid"] is True
    assert report["current_applicable"] is False
    assert report["finding"]["code"] in {"INVENTORY_CHECK", "ARTIFACT_CONTENT"}
