"""Adversarial tests for the FCIS M5-P4A evidence packet."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import cast

import pytest

from src.state.canonical import canonical_json_bytes
from tools.check_fcis_m5_p4a_readiness import (
    _OBSERVABLE_FIELDS,
    build_readiness_receipt_v1,
    classify_changed_paths_v1,
    load_canonical_json_v1,
    validate_baseline_v1,
    validate_cross_language_v1,
    validate_differential_v1,
    validate_mount_graph_v1,
)
from tools.run_fcis_m5_p4a_differential_replay import compare_observations_v1

_REPO_ROOT = Path(__file__).resolve().parents[2]
_BASELINE_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_LEGACY_BASELINE_V1.json"
_DIFFERENTIAL_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_DIFFERENTIAL_REPLAY_V1.json"
_MOUNT_GRAPH_PATH = _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_MOUNT_CALL_GRAPH_V1.json"
_CROSS_LANGUAGE_PATH = (
    _REPO_ROOT / "docs" / "research" / "FCIS_M5_P4A_CROSS_LANGUAGE_MATRIX_V1.json"
)


def _load(path: Path) -> dict[str, object]:
    return load_canonical_json_v1(path)


def _clone(value: dict[str, object]) -> dict[str, object]:
    cloned = json.loads(canonical_json_bytes(value))
    assert type(cloned) is dict
    return cast(dict[str, object], cloned)


def _rehash(value: dict[str, object]) -> dict[str, object]:
    value.pop("artifact_sha256", None)
    value["artifact_sha256"] = "0x" + hashlib.sha256(canonical_json_bytes(value)).hexdigest()
    return value


def _artifacts() -> tuple[
    dict[str, object],
    dict[str, object],
    dict[str, object],
    dict[str, object],
]:
    return (
        _load(_BASELINE_PATH),
        _load(_DIFFERENTIAL_PATH),
        _load(_MOUNT_GRAPH_PATH),
        _load(_CROSS_LANGUAGE_PATH),
    )


def test_m5_p4a_packet_artifacts_pass_strict_validators() -> None:
    baseline, differential, mount_graph, cross_language = _artifacts()
    assert validate_baseline_v1(baseline) == []
    assert validate_differential_v1(differential, baseline) == []
    assert validate_mount_graph_v1(mount_graph) == []
    assert (
        validate_cross_language_v1(
            cross_language,
            baseline,
            mount_graph,
        )
        == []
    )


def test_m5_p4a_baseline_has_accept_and_reject_for_every_source_command() -> None:
    baseline = _load(_BASELINE_PATH)
    inventory = cast(list[dict[str, object]], baseline["command_inventory"])
    fixtures = cast(list[dict[str, object]], baseline["fixtures"])
    mounted = {
        cast(str, row["command_kind"])
        for row in inventory
        if row["mounted"] is True and row["supported"] is True
    }
    outcomes = {
        command: {
            cast(bool, fixture["accepted"])
            for fixture in fixtures
            if fixture["command_kind"] == command
        }
        for command in mounted
    }
    assert outcomes == {command: {False, True} for command in mounted}


def test_m5_p4a_duplicate_json_key_is_rejected(tmp_path: Path) -> None:
    path = tmp_path / "duplicate.json"
    path.write_text('{"schema":"one","schema":"two"}', encoding="utf-8")
    with pytest.raises(ValueError):
        load_canonical_json_v1(path)


def test_m5_p4a_noncanonical_json_is_rejected(tmp_path: Path) -> None:
    path = tmp_path / "spaced.json"
    path.write_text('{"a": 1}\n', encoding="utf-8")
    with pytest.raises(ValueError, match="not canonical JSON"):
        load_canonical_json_v1(path)


def test_mutant_01_stale_baseline_hash_is_killed() -> None:
    baseline = _clone(_load(_BASELINE_PATH))
    baseline["fixture_count"] = cast(int, baseline["fixture_count"]) + 1
    assert any("artifact_sha256 mismatch" in error for error in validate_baseline_v1(baseline))


def test_mutant_02_unknown_source_command_is_killed() -> None:
    baseline = _clone(_load(_BASELINE_PATH))
    inventory = cast(list[dict[str, object]], baseline["command_inventory"])
    inventory[0]["classification"] = "unknown"
    _rehash(baseline)
    assert any("UNKNOWN" in error for error in validate_baseline_v1(baseline))


def test_mutant_03_missing_rejected_fixture_is_killed() -> None:
    baseline = _clone(_load(_BASELINE_PATH))
    fixtures = cast(list[dict[str, object]], baseline["fixtures"])
    target = cast(str, fixtures[0]["command_kind"])
    baseline["fixtures"] = [
        fixture
        for fixture in fixtures
        if not (fixture["command_kind"] == target and fixture["accepted"] is False)
    ]
    baseline["fixture_count"] = len(cast(list[object], baseline["fixtures"]))
    _rehash(baseline)
    assert any(
        target in error and "accepted and rejected" in error
        for error in validate_baseline_v1(baseline)
    )


def test_mutant_04_differential_input_substitution_is_killed() -> None:
    baseline = _load(_BASELINE_PATH)
    differential = _clone(_load(_DIFFERENTIAL_PATH))
    fixtures = cast(list[dict[str, object]], differential["fixtures"])
    binding = cast(dict[str, object], fixtures[0]["input_binding"])
    exact = cast(dict[str, object], binding["exact"])
    exact["context_hash"] = "0x" + "ff" * 32
    _rehash(differential)
    assert any(
        "input bytes differ" in error for error in validate_differential_v1(differential, baseline)
    )


def test_mutant_05_expected_difference_allowlist_is_killed() -> None:
    baseline = _load(_BASELINE_PATH)
    differential = _clone(_load(_DIFFERENTIAL_PATH))
    differential["reviewed_expected_difference_allowlist"] = ["$.algorithm_id"]
    _rehash(differential)
    assert any(
        "allowlist must remain empty" in error
        for error in validate_differential_v1(differential, baseline)
    )


def test_mutant_06_omitted_observable_field_is_killed() -> None:
    baseline = _load(_BASELINE_PATH)
    differential = _clone(_load(_DIFFERENTIAL_PATH))
    fields = cast(list[str], differential["observable_fields"])
    fields.remove("effects_bytes")
    _rehash(differential)
    assert any(
        "observable field contract changed" in error
        for error in validate_differential_v1(differential, baseline)
    )


def test_mutant_07_reject_with_commit_plan_is_killed() -> None:
    baseline = _load(_BASELINE_PATH)
    differential = _clone(_load(_DIFFERENTIAL_PATH))
    fixtures = cast(list[dict[str, object]], differential["fixtures"])
    fixture = next(
        row
        for row in fixtures
        if cast(dict[str, object], row["comparison"])["exact"]
        and cast(
            dict[str, object],
            cast(dict[str, object], row["comparison"])["exact"],
        )["result_kind"]
        == "reject"
    )
    comparison = cast(dict[str, object], fixture["comparison"])
    exact = cast(dict[str, object], comparison["exact"])
    exact["commit_plan_bytes"] = "00"
    fixture["comparison"] = compare_observations_v1(
        cast(dict[str, object], comparison["legacy"]), exact
    )
    _rehash(differential)
    assert any(
        "exposes committable field commit_plan_bytes" in error
        for error in validate_differential_v1(differential, baseline)
    )


@pytest.mark.parametrize("field", sorted(_OBSERVABLE_FIELDS))
def test_mutant_08_comparator_observes_every_declared_field(field: str) -> None:
    legacy: dict[str, object] = {observable: None for observable in _OBSERVABLE_FIELDS}
    exact = dict(legacy)
    exact[field] = "mutated"
    comparison = compare_observations_v1(legacy, exact)
    assert comparison["parity"] == "DIVERGENCE"
    assert comparison["first_difference_path"] == f"$.{field}"


def test_mutant_09_state_root_only_comparator_is_killed_by_effect_change() -> None:
    legacy: dict[str, object] = {observable: None for observable in _OBSERVABLE_FIELDS}
    legacy["next_state_snapshot_root"] = "0x" + "11" * 32
    exact = dict(legacy)
    exact["effects_bytes"] = "01"
    comparison = compare_observations_v1(legacy, exact)
    assert comparison["parity"] == "DIVERGENCE"
    assert comparison["first_difference_path"] == "$.effects_bytes"


def test_mutant_10_rejection_code_change_is_observable() -> None:
    legacy: dict[str, object] = {observable: None for observable in _OBSERVABLE_FIELDS}
    legacy["rejection"] = {"code": "A", "path": []}
    exact = _clone(legacy)
    cast(dict[str, object], exact["rejection"])["code"] = "B"
    comparison = compare_observations_v1(legacy, exact)
    assert comparison["parity"] == "DIVERGENCE"
    assert comparison["first_difference_path"] == "$.rejection.code"


def test_mutant_11_omitted_mount_violation_is_killed() -> None:
    mount_graph = _clone(_load(_MOUNT_GRAPH_PATH))
    rows = cast(list[dict[str, object]], mount_graph["violation_rows"])
    rows.pop()
    _rehash(mount_graph)
    assert any("violation count" in error for error in validate_mount_graph_v1(mount_graph))


def test_mutant_12_unknown_mount_status_is_killed() -> None:
    mount_graph = _clone(_load(_MOUNT_GRAPH_PATH))
    rows = cast(list[dict[str, object]], mount_graph["violation_rows"])
    rows[0]["status"] = "PASSED_BY_REVIEW"
    _rehash(mount_graph)
    assert any("unknown status" in error for error in validate_mount_graph_v1(mount_graph))


def test_mutant_13_unclosed_violation_marked_ready_is_killed() -> None:
    mount_graph = _clone(_load(_MOUNT_GRAPH_PATH))
    rows = cast(list[dict[str, object]], mount_graph["violation_rows"])
    rows[0]["status"] = "EXACT_READY"
    statuses = cast(dict[str, object], mount_graph["status_counts"])
    statuses["BLOCKER"] = cast(int, statuses["BLOCKER"]) - 1
    statuses["EXACT_READY"] = 1
    _rehash(mount_graph)
    assert any("cannot be EXACT_READY" in error for error in validate_mount_graph_v1(mount_graph))


def test_mutant_14_duplicate_mount_violation_identity_is_killed() -> None:
    mount_graph = _clone(_load(_MOUNT_GRAPH_PATH))
    rows = cast(list[dict[str, object]], mount_graph["violation_rows"])
    rows[1]["violation_id"] = rows[0]["violation_id"]
    _rehash(mount_graph)
    assert any("duplicated" in error for error in validate_mount_graph_v1(mount_graph))


def test_mutant_15_missing_cross_consumer_row_is_killed() -> None:
    baseline, _, mount_graph, cross_language = _artifacts()
    rows = cast(list[dict[str, object]], cross_language["rows"])
    removed_surface = cast(str, rows[0]["surface_id"])
    rows.pop(0)
    cross_language["row_count"] = len(rows)
    _rehash(cross_language)
    assert any(
        removed_surface in error and "full consumer coverage" in error
        for error in validate_cross_language_v1(
            cross_language,
            baseline,
            mount_graph,
        )
    )


def test_mutant_16_unknown_cross_language_status_is_killed() -> None:
    baseline, _, mount_graph, cross_language = _artifacts()
    rows = cast(list[dict[str, object]], cross_language["rows"])
    rows[0]["status"] = "READY"
    _rehash(cross_language)
    assert any(
        "unknown status" in error
        for error in validate_cross_language_v1(
            cross_language,
            baseline,
            mount_graph,
        )
    )


def test_mutant_17_source_presence_cannot_promote_exact_bytes() -> None:
    baseline, _, mount_graph, cross_language = _artifacts()
    rows = cast(list[dict[str, object]], cross_language["rows"])
    previous = cast(str, rows[0]["status"])
    rows[0]["status"] = "PASS_EXACT_BYTES"
    status_counts = cast(dict[str, object], cross_language["status_counts"])
    status_counts[previous] = cast(int, status_counts[previous]) - 1
    status_counts["PASS_EXACT_BYTES"] = 1
    cross_language["pass_exact_bytes_count"] = 1
    _rehash(cross_language)
    assert any(
        "without a promoted consumer replay" in error
        for error in validate_cross_language_v1(
            cross_language,
            baseline,
            mount_graph,
        )
    )


def test_mutant_18_authority_or_config_path_change_is_killed() -> None:
    assert classify_changed_paths_v1(
        {
            "tools/check_fcis_m5_p4a_readiness.py",
            "docs/research/FCIS_M5_P4A_REVIEW.md",
            "src/core/dex.py",
            "config/deploy/public-testnet.yaml",
        }
    ) == ["config/deploy/public-testnet.yaml", "src/core/dex.py"]


def test_m5_p4a_receipt_is_complete_and_honestly_blocked() -> None:
    receipt = build_readiness_receipt_v1()
    assert receipt["packet_complete"] is True
    assert receipt["check_violations"] == 0
    assert receipt["verdict"] == "BLOCKED"
    assert receipt["mount_ready"] is False
    assert receipt["honest_blocked_outcome"] is True
    blockers = {
        cast(str, row["code"]): cast(int, row["count"])
        for row in cast(list[dict[str, object]], receipt["blockers"])
    }
    assert blockers["FINAL_MOUNT_STRUCTURAL_VIOLATIONS"] == 79
    assert blockers["DIFFERENTIAL_PARITY_OPEN"] == 24
    assert blockers["CROSS_CONSUMER_EXACT_BYTES_MISSING"] > 0
