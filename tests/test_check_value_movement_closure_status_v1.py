from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

from tools.check_value_movement_closure_status_v1 import (
    DEFAULT_STATUS_PATH,
    M6_ATDD_PATH,
    REPO_ROOT,
    check_value_movement_closure_status_v1,
    validate_m6_zdex_semantic_anchor_v1,
)


def _status() -> dict[str, object]:
    return json.loads((REPO_ROOT / DEFAULT_STATUS_PATH).read_text(encoding="utf-8"))


def _write_status(tmp_path: Path, value: dict[str, object]) -> Path:
    path = tmp_path / "status.json"
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")
    return path


def _replay_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in value["implemented_slices"]  # type: ignore[index]
        if row["id"] == "ECONOMIC_INITIAL_STATE_REPLAY_PRESERVATION_V1"
    )


def _source_head_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in value["implemented_slices"]  # type: ignore[index]
        if row["id"] == "ECONOMIC_INITIAL_STATE_SOURCE_HEAD_ACTIVATION_V1"
    )


def _durable_activation_slice(value: dict[str, object]) -> dict[str, object]:
    return next(
        row
        for row in value["implemented_slices"]  # type: ignore[index]
        if row["id"] == "GLOBAL_ECONOMIC_DURABLE_ACTIVATION_JOURNAL_V1"
    )


def test_current_value_movement_closure_status_is_exact_and_fail_closed() -> None:
    report = check_value_movement_closure_status_v1()

    assert report["ok"] is True
    assert report["findings"] == []
    assert report["gate_count"] == 12
    assert report["production_authority"] == "NONE"


def test_checker_rejects_authority_gate_and_semantic_promotion_drift(
    tmp_path: Path,
) -> None:
    mutated = deepcopy(_status())
    mutated["authority"]["production_authority"] = "GLOBAL_EPOCH"  # type: ignore[index]
    mutated["gate_status"] = mutated["gate_status"][:-1]  # type: ignore[index]
    mutated["semantic_anchors"]["buy_and_burn"] = "burn treasury ZDEX"  # type: ignore[index]
    mutated["claim_contract"]["status"] = "PROVED"  # type: ignore[index]

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "authority or readiness nonclaim drift" in report["findings"]
    assert "VM gate IDs must be complete and ordered" in report["findings"]
    assert "buy-and-burn semantic anchor drift" in report["findings"]
    assert "claim status drift" in report["findings"]


def test_checker_rejects_stale_claim_hash_and_duplicate_json_key(tmp_path: Path) -> None:
    stale = deepcopy(_status())
    stale["claim_contract"]["sha256"] = "0" * 64  # type: ignore[index]
    stale_report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, stale)
    )

    duplicate_path = tmp_path / "duplicate.json"
    duplicate_path.write_text('{"schema":"a","schema":"b"}', encoding="utf-8")
    duplicate_report = check_value_movement_closure_status_v1(
        status_path=duplicate_path
    )

    assert stale_report["ok"] is False
    assert "claim contract hash mismatch" in stale_report["findings"]
    assert duplicate_report["ok"] is False
    assert "duplicate JSON key" in duplicate_report["findings"][0]


def test_checker_rejects_stale_replay_slice_evidence(tmp_path: Path) -> None:
    mutated = deepcopy(_status())
    replay = _replay_slice(mutated)
    replay["commit"] = "0" * 40
    replay["python_sha256"] = "0" * 64
    replay["golden_continuity_root"] = "0x" + "0" * 64

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "replay slice implementation commit mismatch" in report["findings"]
    assert (
        "replay slice artifact hash mismatch: python_sha256" in report["findings"]
    )
    assert (
        "replay slice golden evidence mismatch: golden_continuity_root"
        in report["findings"]
    )


def test_checker_rejects_stale_source_head_slice_evidence(tmp_path: Path) -> None:
    mutated = deepcopy(_status())
    source_head = _source_head_slice(mutated)
    source_head["commit"] = "0" * 40
    source_head["python_commit_port_sha256"] = "0" * 64

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "source-head slice subject commit mismatch" in report["findings"]
    assert (
        "source-head slice artifact hash mismatch: python_commit_port_sha256"
        in report["findings"]
    )


def test_checker_rejects_stale_durable_activation_slice_evidence(
    tmp_path: Path,
) -> None:
    mutated = deepcopy(_status())
    durable = _durable_activation_slice(mutated)
    durable["commit"] = "0" * 40
    durable["artifact_subject_commit"] = "1" * 40
    durable["python_journal_sha256"] = "0" * 64

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert (
        "durable activation slice implementation commit mismatch" in report["findings"]
    )
    assert (
        "durable activation slice artifact subject commit mismatch"
        in report["findings"]
    )
    assert (
        "durable activation slice artifact hash mismatch: python_journal_sha256"
        in report["findings"]
    )


def test_checker_kills_fixed_floor_and_treasury_burn_semantic_mutants() -> None:
    contract = json.loads((REPO_ROOT / M6_ATDD_PATH).read_text(encoding="utf-8"))
    zdex = next(
        row
        for row in contract["managed_asset_policy"]
        if row["asset_class"] == "zdex_protocol_token"
    )

    fixed_floor = deepcopy(contract)
    fixed_floor_row = next(
        row
        for row in fixed_floor["managed_asset_policy"]
        if row["asset_class"] == "zdex_protocol_token"
    )
    fixed_floor_row["production_rule"] = "Burn treasury ZDEX until a 10% floor."
    shortcut = deepcopy(contract)
    shortcut_row = next(
        row
        for row in shortcut["managed_asset_policy"]
        if row["asset_class"] == "zdex_protocol_token"
    )
    shortcut_row["burn_authority"] = "treasury balance burn"

    assert validate_m6_zdex_semantic_anchor_v1(contract) == []
    assert validate_m6_zdex_semantic_anchor_v1(fixed_floor) == [
        "M6 ATDD ZDEX retained-supply or purchase-and-burn drift"
    ]
    assert validate_m6_zdex_semantic_anchor_v1(shortcut) == [
        "M6 ATDD ZDEX burn authority drift"
    ]
    assert zdex["production_rule"].endswith(
        "no fixed initial-supply percentage floor is authoritative."
    )


def test_checker_rejects_erased_known_semantic_conflict(tmp_path: Path) -> None:
    mutated = deepcopy(_status())
    mutated["known_semantic_conflicts"] = mutated["known_semantic_conflicts"][1:]  # type: ignore[index]

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "known semantic conflict IDs are incomplete or unordered" in report["findings"]


def test_checker_rejects_stale_value_sink_observation(tmp_path: Path) -> None:
    mutated = deepcopy(_status())
    mutated["live_gate_observations"]["value_sink_inventory"][  # type: ignore[index]
        "observed_occurrence_count"
    ] = 0

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "value sink inventory observation is stale or incomplete" in report["findings"]


def test_checker_rejects_stale_asset_precision_observation(tmp_path: Path) -> None:
    mutated = deepcopy(_status())
    mutated["live_gate_observations"]["asset_precision_policy"][  # type: ignore[index]
        "decimal_places"
    ] = 18

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "asset precision policy observation is stale or incomplete" in report["findings"]
