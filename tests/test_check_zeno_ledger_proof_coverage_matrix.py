from __future__ import annotations

import json
import subprocess
import sys
from copy import deepcopy
from pathlib import Path

from tools.check_zeno_ledger_proof_coverage_matrix import (
    MATRIX_PATH,
    REQUIRED_GAP_IDS,
    REQUIRED_NON_CLAIMS,
    REQUIRED_SUPPORTED_IDS,
    validate_proof_coverage_matrix_v0,
)

ROOT = Path(__file__).resolve().parents[1]


def _load_matrix() -> dict[str, object]:
    return json.loads(MATRIX_PATH.read_text(encoding="utf-8"))


def test_default_matrix_is_accepted() -> None:
    result = validate_proof_coverage_matrix_v0(_load_matrix())

    assert result["ok"] is True
    assert result["supported_surface_count"] >= len(REQUIRED_SUPPORTED_IDS)
    assert result["gap_surface_count"] >= len(REQUIRED_GAP_IDS)
    assert result["non_claim_count"] >= len(REQUIRED_NON_CLAIMS)
    assert {row["id"] for row in result["supported_surfaces"]} >= REQUIRED_SUPPORTED_IDS


def test_rejects_missing_required_supported_surface() -> None:
    matrix = _load_matrix()
    matrix["supported_surfaces"] = [
        entry
        for entry in matrix["supported_surfaces"]  # type: ignore[index]
        if not (isinstance(entry, dict) and entry.get("id") == "risc0_supported_transition_real_proof_smoke")
    ]

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("missing required supported surfaces" in error for error in result["errors"])


def test_rejects_missing_required_gap_surface() -> None:
    matrix = _load_matrix()
    matrix["gap_surfaces"] = [
        entry
        for entry in matrix["gap_surfaces"]  # type: ignore[index]
        if not (isinstance(entry, dict) and entry.get("id") == "perps_settlement_real_proof")
    ]

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("missing required gap surfaces" in error for error in result["errors"])


def test_rejects_missing_required_non_claim() -> None:
    matrix = _load_matrix()
    matrix["non_claims"] = [
        item
        for item in matrix["non_claims"]  # type: ignore[index]
        if item != "does_not_claim_upba_zk_execution"
    ]

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("missing required non-claims" in error for error in result["errors"])


def test_rejects_gap_surface_with_claim_id() -> None:
    matrix = _load_matrix()
    matrix["gap_surfaces"] = deepcopy(matrix["gap_surfaces"])  # type: ignore[index]
    first_gap = matrix["gap_surfaces"][0]  # type: ignore[index]
    assert isinstance(first_gap, dict)
    first_gap["claim_id"] = "py:zeno_ledger:risc0_proof_metadata_adapter_v0"

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("gap surface must not carry claim_id" in error for error in result["errors"])


def test_rejects_unknown_claim_id_on_supported_surface() -> None:
    matrix = _load_matrix()
    matrix["supported_surfaces"] = deepcopy(matrix["supported_surfaces"])  # type: ignore[index]
    first_supported = matrix["supported_surfaces"][0]  # type: ignore[index]
    assert isinstance(first_supported, dict)
    first_supported["claim_id"] = "missing:claim"

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("claim_id missing from claims registry" in error for error in result["errors"])


def test_rejects_duplicate_supported_surface_id() -> None:
    matrix = _load_matrix()
    matrix["supported_surfaces"] = deepcopy(matrix["supported_surfaces"])  # type: ignore[index]
    assert isinstance(matrix["supported_surfaces"], list)
    matrix["supported_surfaces"].append(deepcopy(matrix["supported_surfaces"][0]))

    result = validate_proof_coverage_matrix_v0(matrix)

    assert result["ok"] is False
    assert any("supported surface id must be unique" in error for error in result["errors"])


def test_cli_pretty_accepts_default_matrix() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(ROOT / "tools/check_zeno_ledger_proof_coverage_matrix.py"),
            "--pretty",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    result = json.loads(completed.stdout)
    assert result["ok"] is True
