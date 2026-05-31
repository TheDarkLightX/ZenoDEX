from __future__ import annotations

import json
import subprocess
import sys
from copy import deepcopy
from pathlib import Path

from tools.check_zenodex_trust_minimization_target import (
    DEFAULT_TARGET,
    validate_trust_minimization_target_v0,
)

ROOT = Path(__file__).resolve().parents[1]


def _load_target() -> dict[str, object]:
    return json.loads(DEFAULT_TARGET.read_text(encoding="utf-8"))


def test_default_trust_minimization_target_is_accepted() -> None:
    result = validate_trust_minimization_target_v0(_load_target())

    assert result["ok"] is True
    assert result["target_status"] == "frontier_open"
    assert result["lower_than_uniswap_claim"] is False
    assert result["open_surface_count"] >= 1
    assert "upba_batch_clearing" in result["open_surfaces"]
    assert result["supported_surface_count"] >= 3


def test_rejects_claiming_lower_than_uniswap_while_frontier_is_open() -> None:
    target = _load_target()
    target["lower_than_uniswap_claim"] = True

    result = validate_trust_minimization_target_v0(target)

    assert result["ok"] is False
    assert "frontier_open target must set lower_than_uniswap_claim=false" in result["errors"]


def test_rejects_achieved_status_with_open_surfaces() -> None:
    target = _load_target()
    target["target_status"] = "achieved"
    target["lower_than_uniswap_claim"] = True

    result = validate_trust_minimization_target_v0(target)

    assert result["ok"] is False
    assert any(error.startswith("achieved target cannot have open surfaces:") for error in result["errors"])


def test_rejects_missing_host_adversary_assumption() -> None:
    target = _load_target()
    host_model = dict(target["host_adversary_model"])  # type: ignore[index]
    host_model["host_is_adversary"] = False
    target["host_adversary_model"] = host_model

    result = validate_trust_minimization_target_v0(target)

    assert result["ok"] is False
    assert "host_adversary_model.host_is_adversary must be true" in result["errors"]


def test_rejects_open_gap_without_matrix_backed_non_claim() -> None:
    target = _load_target()
    target["required_surfaces"] = deepcopy(target["required_surfaces"])  # type: ignore[index]
    surface = target["required_surfaces"][4]  # type: ignore[index]
    assert isinstance(surface, dict)
    surface["non_claim"] = "does_not_claim_missing_gap"

    result = validate_trust_minimization_target_v0(target)

    assert result["ok"] is False
    assert any("non_claim missing from target non_claims" in error for error in result["errors"])


def test_rejects_supported_surface_unknown_to_proof_matrix() -> None:
    target = _load_target()
    target["required_surfaces"] = deepcopy(target["required_surfaces"])  # type: ignore[index]
    surface = target["required_surfaces"][0]  # type: ignore[index]
    assert isinstance(surface, dict)
    surface["supported_surface_id"] = "missing_supported_surface"

    result = validate_trust_minimization_target_v0(target)

    assert result["ok"] is False
    assert any("supported_surface_id unknown:missing_supported_surface" in error for error in result["errors"])


def test_cli_pretty_accepts_default_target() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            str(ROOT / "tools/check_zenodex_trust_minimization_target.py"),
            "--pretty",
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    result = json.loads(completed.stdout)
    assert result["ok"] is True
    assert result["schema"] == "zenodex.trust_minimization_target_report.v0"
