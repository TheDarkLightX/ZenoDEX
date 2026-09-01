from __future__ import annotations

import json
import subprocess
import sys
from collections.abc import Callable
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest

from tools.check_o008_formal_cycle_v1 import check_artifact

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "docs" / "research" / "ZENODEX_O008_FORMAL_CYCLE_V1.json"
CHECKER = ROOT / "tools" / "check_o008_formal_cycle_v1.py"


def _artifact() -> dict[str, Any]:
    value = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _mutated(
    tmp_path: Path,
    name: str,
    mutation: Callable[[dict[str, Any]], None],
) -> Path:
    value = deepcopy(_artifact())
    mutation(value)
    path = tmp_path / f"{name}.json"
    path.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
    return path


def test_current_o008_formal_cycle_packet_passes_fail_closed_checker() -> None:
    result = check_artifact(ARTIFACT)
    assert result == {
        "ok": True,
        "artifact": str(ARTIFACT),
        "subject_commit": "fd071bcb53daf5e37c083b610003ec36c7391f18",
        "formal_cycle_status": "FORMAL_CYCLE_COMPLETE_O008_OPEN",
        "o008_status": "OPEN_EXACT_ALL_12_RECONCILIATION_MISSING",
        "source_pin_count": 11,
        "lane_count": 12,
        "errors": [],
    }


def test_cli_emits_machine_readable_open_o008_verdict() -> None:
    process = subprocess.run(
        [sys.executable, str(CHECKER)],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=120,
        check=False,
    )
    assert process.returncode == 0, process.stdout + process.stderr
    payload = json.loads(process.stdout)
    assert payload["ok"] is True
    assert payload["formal_cycle_status"] == "FORMAL_CYCLE_COMPLETE_O008_OPEN"
    assert payload["o008_status"] == "OPEN_EXACT_ALL_12_RECONCILIATION_MISSING"


@pytest.mark.parametrize(
    ("name", "mutation", "expected_error"),
    (
        pytest.param(
            "promote_formal_core",
            lambda value: value.__setitem__("formal_core_complete", True),
            "unsafe or unexpected formal_core_complete",
            id="promote_formal_core",
        ),
        pytest.param(
            "promote_authority",
            lambda value: value.__setitem__("settlement_authority", "ACTIVE"),
            "unsafe or unexpected settlement_authority",
            id="promote_authority",
        ),
        pytest.param(
            "drift_source",
            lambda value: value["source_pins"][0].__setitem__("sha256", "0" * 64),
            "source drift: src/core/global_economic_state_effect_refinement_v1.py",
            id="drift_source",
        ),
        pytest.param(
            "drop_lane",
            lambda value: value["lane_source_data"].pop(),
            "lane source-data inventory must cover the exact twelve-lane order",
            id="drop_lane",
        ),
        pytest.param(
            "drop_sidecar_check",
            lambda value: value["required_sidecar"]["required_checks"].pop(),
            "sidecar checker obligation inventory drift",
            id="drop_sidecar_check",
        ),
        pytest.param(
            "promote_lane",
            lambda value: value["lane_source_data"][0].__setitem__("status", "COMPLETE"),
            "no lane may claim complete exact reconciliation",
            id="promote_lane",
        ),
    ),
)
def test_unsafe_packet_mutations_fail_closed(
    tmp_path: Path,
    name: str,
    mutation: Callable[[dict[str, Any]], None],
    expected_error: str,
) -> None:
    result = check_artifact(_mutated(tmp_path, name, mutation))
    assert result["ok"] is False
    assert expected_error in result["errors"]


def test_duplicate_json_key_fails_closed(tmp_path: Path) -> None:
    source = ARTIFACT.read_text(encoding="utf-8")
    duplicate = source.replace(
        '  "schema": "zenodex/o008-formal-cycle-evidence/v1",',
        '  "schema": "zenodex/o008-formal-cycle-evidence/v1",\n'
        '  "schema": "forged",',
        1,
    )
    path = tmp_path / "duplicate.json"
    path.write_text(duplicate, encoding="utf-8")
    result = check_artifact(path)
    assert result["ok"] is False
    assert result["errors"] == ["duplicate JSON key: schema"]


def test_packet_names_the_exact_v1_information_loss_and_nonclaims() -> None:
    artifact = _artifact()
    assert artifact["v1_information_loss"]["terminal_missing_fields"] == [
        "liability_domain",
        "custody_principal",
    ]
    assert artifact["required_sidecar"]["host_only_authority"] == "EVIDENCE_ONLY"
    nonclaims = " ".join(artifact["nonclaims"])
    assert "does not complete O-008" in nonclaims
    assert "exact all-twelve-lane" in nonclaims
    assert "whole-program value safety" in nonclaims
