from __future__ import annotations

import json
from copy import deepcopy
from pathlib import Path

from tools.check_value_movement_closure_status_v1 import (
    DEFAULT_STATUS_PATH,
    REPO_ROOT,
    check_value_movement_closure_status_v1,
)


def _status() -> dict[str, object]:
    return json.loads((REPO_ROOT / DEFAULT_STATUS_PATH).read_text(encoding="utf-8"))


def _write_status(tmp_path: Path, value: dict[str, object]) -> Path:
    path = tmp_path / "status.json"
    path.write_text(json.dumps(value, indent=2, sort_keys=True), encoding="utf-8")
    return path


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

    report = check_value_movement_closure_status_v1(
        status_path=_write_status(tmp_path, mutated)
    )

    assert report["ok"] is False
    assert "authority or readiness nonclaim drift" in report["findings"]
    assert "VM gate IDs must be complete and ordered" in report["findings"]
    assert "buy-and-burn semantic anchor drift" in report["findings"]


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
