from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from tools.check_adversarial_hardening_pokayoke_matrix import (
    DEFAULT_MANIFEST,
    validate_matrix,
)

REPO = Path(__file__).resolve().parents[1]


def _matrix() -> dict[str, Any]:
    return json.loads(DEFAULT_MANIFEST.read_text(encoding="utf-8"))


def _scenario_report(report: dict[str, Any], scenario_id: str) -> dict[str, Any]:
    for item in report["scenarios"]["items"]:
        if item["id"] == scenario_id:
            return item
    raise AssertionError(f"missing scenario report for {scenario_id}")


def test_default_matrix_accepts_and_preserves_advisory_boundary() -> None:
    report = validate_matrix(_matrix())

    assert report["ok"] is True
    assert report["facts"]["scenario_count"] == 8
    assert report["facts"]["missing_required_scenarios"] == []
    assert report["promotion_boundary"]["facts"]["public_claim_allowed"] is False
    assert report["promotion_boundary"]["facts"]["claim_registry_entry_allowed"] is False
    assert report["promotion_boundary"]["facts"]["model_authority"] == "advisory_only"


def test_matrix_rejects_missing_mallory_actor() -> None:
    matrix = _matrix()
    matrix["actors"] = [actor for actor in matrix["actors"] if actor["id"] != "mallory"]

    report = validate_matrix(matrix)

    assert report["ok"] is False
    assert "actors rejected" in report["errors"]
    assert "missing required actors: mallory" in report["actors"]["errors"]


def test_matrix_rejects_scenario_without_side_channel_controls() -> None:
    matrix = _matrix()
    scenario = copy.deepcopy(matrix["scenarios"][0])
    scenario["side_channels"] = []
    scenario["controls"] = [control for control in scenario["controls"] if control != "side_channel_budget"]
    matrix["scenarios"][0] = scenario

    report = validate_matrix(matrix)

    assert report["ok"] is False
    item = _scenario_report(report, "AH-PK-001")
    assert "scenarios[0].side_channels must be non-empty" in item["errors"]
    assert "scenario must include side_channel_budget" in item["errors"]


def test_matrix_rejects_production_claim_boundary() -> None:
    matrix = _matrix()
    matrix["promotion_boundary"]["public_claim_allowed"] = True
    matrix["scenarios"][0]["promotion_boundary"]["claim_status"] = "production_ready"

    report = validate_matrix(matrix)

    assert report["ok"] is False
    assert "promotion_boundary rejected" in report["errors"]
    item = _scenario_report(report, "AH-PK-001")
    assert "scenarios[0].promotion_boundary.claim_status cannot be production_ready" in item["errors"]


def test_cli_checks_default_manifest() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_adversarial_hardening_pokayoke_matrix.py", "--json"],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode == 0
    assert proc.stderr == ""
    report = json.loads(proc.stdout)
    assert report["ok"] is True
    assert report["schema"] == "zenodex/adversarial_hardening_pokayoke_matrix_report/v1"
