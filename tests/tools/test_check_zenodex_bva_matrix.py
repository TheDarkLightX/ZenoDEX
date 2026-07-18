from __future__ import annotations

import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECKER = ROOT / "tools" / "check_zenodex_bva_matrix.py"
MATRIX = ROOT / "docs" / "assurance" / "zenodex_bva_matrix_v1.json"


def _module():
    spec = importlib.util.spec_from_file_location("zenodex_bva_checker", CHECKER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_repository_matrix_structure_and_vector_112_are_critical_green() -> None:
    result = _module().check(
        MATRIX,
        ROOT,
        promotion=False,
        verify_files=True,
        require_executed=False,
    )
    assert result["status"] == "accepted", result["errors"]
    assert result["surface_count"] == 10
    assert result["command_count"] == 85
    assert result["field_count"] == 228
    assert result["errors"] == []


def test_repository_matrix_blocks_production_until_every_item_is_closed() -> None:
    result = _module().check(
        MATRIX,
        ROOT,
        promotion=True,
        verify_files=True,
        require_executed=True,
    )
    assert result["status"] == "blocked"
    assert "claim_status=blocked" in result["errors"]
    assert any(error.endswith("coverage missing") for error in result["errors"])
    assert any("inventory is not fully source-bound" in error for error in result["errors"])


def test_duplicate_json_keys_fail_closed(tmp_path: Path) -> None:
    bad = tmp_path / "bad.json"
    bad.write_text('{"schema":"a","schema":"b"}', encoding="utf-8")
    result = _module().check(
        bad,
        tmp_path,
        promotion=False,
        verify_files=False,
        require_executed=False,
    )
    assert result["status"] == "blocked"
    assert any("duplicate JSON key" in error for error in result["errors"])


def test_unknown_coverage_inventory_key_fails_closed(tmp_path: Path) -> None:
    matrix = json.loads(MATRIX.read_text(encoding="utf-8"))
    matrix["surfaces"][0]["coverage"]["field:not_real"] = {
        "status": "complete",
        "profiles": ["numeric"],
        "covered_cases": matrix["profiles"]["numeric"],
        "evidence": [],
        "note": "invalid test entry",
    }
    bad = tmp_path / "bad.json"
    bad.write_text(json.dumps(matrix), encoding="utf-8")
    result = _module().check(
        bad,
        ROOT,
        promotion=False,
        verify_files=False,
        require_executed=False,
    )
    assert result["status"] == "blocked"
    assert any("coverage key not in inventory" in error for error in result["errors"])


def test_missing_vector_112_sentinel_fails_critical_mode(tmp_path: Path) -> None:
    matrix = json.loads(MATRIX.read_text(encoding="utf-8"))
    matrix["regressions"] = [
        {
            "id": "OTHER",
            "critical": True,
            "status": "complete",
            "cases": ["reject_is_noop"],
            "tests": [
                "tests/core/test_perp_v4_parity.py::test_v4_settlement_oracle_boundaries_match_generated_reference"
            ],
            "note": "replacement",
        }
    ]
    bad = tmp_path / "bad.json"
    bad.write_text(json.dumps(matrix), encoding="utf-8")
    result = _module().check(
        bad,
        ROOT,
        promotion=False,
        verify_files=True,
        require_executed=False,
    )
    assert result["status"] == "blocked"
    assert "vector 112 regression sentinel missing" in result["errors"]


def test_boolean_coercion_in_schema_fails_closed(tmp_path: Path) -> None:
    matrix = json.loads(MATRIX.read_text(encoding="utf-8"))
    matrix["surfaces"][0]["source_bound"] = 1
    bad = tmp_path / "bad.json"
    bad.write_text(json.dumps(matrix), encoding="utf-8")
    result = _module().check(
        bad,
        ROOT,
        promotion=False,
        verify_files=False,
        require_executed=False,
    )
    assert result["status"] == "blocked"
    assert any("must be a bool" in error for error in result["errors"])
