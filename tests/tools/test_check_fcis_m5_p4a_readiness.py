"""Tests for the FCIS M5-P4A readiness checker and associated tools."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

_REPO_ROOT = Path(__file__).resolve().parents[2]

_BASELINE_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_LEGACY_BASELINE_V1.json"
_DIFF_REPLAY_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_DIFFERENTIAL_REPLAY_V1.json"
_CALL_GRAPH_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_CALL_GRAPH_LEDGER_V1.json"
_XLANG_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_CROSS_LANGUAGE_MATRIX_V1.json"
_RECEIPT_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_READINESS_RECEIPT_V1.json"

_REQUIRED_COMMAND_KINDS = frozenset({
    "CREATE_POOL",
    "ADD_LIQUIDITY",
    "REMOVE_LIQUIDITY",
    "SWAP_EXACT_IN",
    "SWAP_EXACT_OUT",
    "ROUTE_EXACT_IN",
    "ROUTE_EXACT_OUT",
})


def _load(path: Path) -> dict:
    assert path.exists(), f"artifact missing: {path}"
    return json.loads(path.read_text())


def test_baseline_artifact_exists_and_has_correct_schema() -> None:
    artifact = _load(_BASELINE_PATH)
    assert artifact["schema"] == "zenodex/fcis-m5-p4a-legacy-baseline/v1"


def test_baseline_covers_all_seven_command_kinds() -> None:
    artifact = _load(_BASELINE_PATH)
    covered = set(artifact["command_kinds_covered"])
    assert covered == _REQUIRED_COMMAND_KINDS


def test_baseline_has_accepted_and_rejected_fixtures() -> None:
    artifact = _load(_BASELINE_PATH)
    fixtures = artifact["fixtures"]
    accepted = [f for f in fixtures if f["accepted"]]
    rejected = [f for f in fixtures if not f["accepted"]]
    assert len(accepted) > 0
    assert len(rejected) > 0


def test_baseline_has_generator_and_source_tree_hash() -> None:
    artifact = _load(_BASELINE_PATH)
    assert artifact["generator_hash"].startswith("0x")
    assert artifact["source_tree_hash"].startswith("0x")
    assert len(artifact["generator_hash"]) == 66
    assert len(artifact["source_tree_hash"]) == 66


def test_baseline_fixture_count_matches_actual() -> None:
    artifact = _load(_BASELINE_PATH)
    assert artifact["fixture_count"] == len(artifact["fixtures"])


def test_differential_replay_artifact_exists_and_has_correct_schema() -> None:
    artifact = _load(_DIFF_REPLAY_PATH)
    assert artifact["schema"] == "zenodex/fcis-m5-p4a-differential-replay/v1"


def test_differential_replay_fixture_count_matches_baseline() -> None:
    baseline = _load(_BASELINE_PATH)
    diff = _load(_DIFF_REPLAY_PATH)
    assert diff["fixture_count"] == baseline["fixture_count"]


def test_differential_replay_has_match_and_divergence_counts() -> None:
    artifact = _load(_DIFF_REPLAY_PATH)
    assert artifact["match_count"] + artifact["divergence_count"] == artifact["fixture_count"]
    assert artifact["divergence_count"] > 0
    assert "divergence_categories" in artifact


def test_call_graph_ledger_exists_and_has_correct_schema() -> None:
    artifact = _load(_CALL_GRAPH_PATH)
    assert artifact["schema"] == "zenodex/fcis-m5-p4a-call-graph-ledger/v1"


def test_call_graph_ledger_reports_79_violations() -> None:
    artifact = _load(_CALL_GRAPH_PATH)
    assert artifact["mount_readiness"]["total_violations"] == 79


def test_call_graph_ledger_reports_not_ready_for_mount() -> None:
    artifact = _load(_CALL_GRAPH_PATH)
    assert artifact["mount_readiness"]["ready_for_mount"] is False


def test_call_graph_ledger_has_blocker_paths() -> None:
    artifact = _load(_CALL_GRAPH_PATH)
    blocker_paths = artifact["mount_readiness"]["blocker_paths"]
    assert "src/core/dex.py" in blocker_paths
    assert "src/state/legacy_state_snapshots.py" in blocker_paths
    assert "src/core/settlement_strong_validator.py" in blocker_paths


def test_cross_language_matrix_exists_and_has_correct_schema() -> None:
    artifact = _load(_XLANG_PATH)
    assert artifact["schema"] == "zenodex/fcis-m5-p4a-cross-language-matrix/v1"


def test_cross_language_matrix_has_trusted_core_surfaces() -> None:
    artifact = _load(_XLANG_PATH)
    surfaces = artifact["surface_matrix"]
    assert len(surfaces) == 10
    surface_names = {s["surface"] for s in surfaces}
    assert "state_root" in surface_names
    assert "cpmm_settlement" in surface_names


def test_cross_language_matrix_has_fcis_specific_entries() -> None:
    artifact = _load(_XLANG_PATH)
    fcis_entries = artifact["fcis_specific_matrix"]
    assert len(fcis_entries) >= 6
    fcis_surfaces = {e["surface"] for e in fcis_entries}
    assert "fcis_step_evaluator" in fcis_surfaces
    assert "fcis_spot_shadow" in fcis_surfaces


def test_readiness_receipt_exists_and_has_correct_schema() -> None:
    receipt = _load(_RECEIPT_PATH)
    assert receipt["schema"] == "zenodex/fcis-m5-p4a-readiness-receipt/v1"


def test_readiness_receipt_verdict_is_blocked() -> None:
    receipt = _load(_RECEIPT_PATH)
    assert receipt["verdict"] == "BLOCKED"
    assert receipt["overall_ready"] is False


def test_readiness_receipt_reports_79_authority_violations() -> None:
    receipt = _load(_RECEIPT_PATH)
    assert receipt["authority_violations"] == 79


def test_readiness_receipt_packet_is_complete() -> None:
    receipt = _load(_RECEIPT_PATH)
    assert receipt["packet_complete"] is True
    assert receipt["check_violations"] == 0


def test_readiness_receipt_honest_blocked_outcome() -> None:
    receipt = _load(_RECEIPT_PATH)
    assert receipt["honest_blocked_outcome"] is True
    assert receipt["mount_ready"] is False


def test_readiness_receipt_all_artifacts_exist() -> None:
    receipt = _load(_RECEIPT_PATH)
    for ae in receipt["artifact_existence"]:
        assert ae["exists"] is True
        assert ae["size_bytes"] > 0
        assert ae["sha256"].startswith("0x")
