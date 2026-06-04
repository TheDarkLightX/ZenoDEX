"""Tests for the CBC matrix-closure gate (Phase 0)."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

import tools.gate_cbc_matrix_closure as gate
from src.integration.surface_security_claim import CBC_COLUMNS, SPOT_DEX_SCOPE

DEFAULT_EVIDENCE = gate.DEFAULT_EVIDENCE


def _all_clear_surface() -> dict:
    ev = {c: {"ref": f"x/{c}.py", "verified": True} for c in CBC_COLUMNS if c != "open_gaps_closed"}
    ev["open_gaps_closed"] = True
    return ev


def test_default_registry_is_blocked_failclosed() -> None:
    # The shipped registry is an honest work-tracker: every column unverified, so
    # the gate MUST fail closed (exit 1) — no surface is production-ready yet.
    rc = gate.run(DEFAULT_EVIDENCE, scope_override=None, as_json=True)
    assert rc == 1


def test_default_registry_covers_spot_dex_scope() -> None:
    raw = json.loads(DEFAULT_EVIDENCE.read_text(encoding="utf-8"))
    assert set(raw["surfaces"].keys()) == set(SPOT_DEX_SCOPE)
    # Honesty guard: nothing in the shipped registry is hand-set to verified:true.
    for surface in raw["surfaces"].values():
        for col, val in surface.items():
            if col == "open_gaps_closed":
                assert val is False
            elif isinstance(val, dict) and "verified" in val:
                assert val["verified"] is False


def test_all_clear_registry_passes(tmp_path: Path) -> None:
    reg = {"schema": "x", "scope_id": "t", "surfaces": {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}}
    p = tmp_path / "ev.json"
    p.write_text(json.dumps(reg), encoding="utf-8")
    rc = gate.run(p, scope_override=None, as_json=True)
    assert rc == 0


def test_one_blocked_surface_fails_the_scope(tmp_path: Path) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    surfaces["state_root"]["open_gaps_closed"] = False  # D-CANON-002 still open
    reg = {"schema": "x", "scope_id": "t", "surfaces": surfaces}
    p = tmp_path / "ev.json"
    p.write_text(json.dumps(reg), encoding="utf-8")
    rc = gate.run(p, scope_override=None, as_json=True)
    assert rc == 1


def test_missing_registry_fails_closed(tmp_path: Path) -> None:
    rc = gate.run(tmp_path / "does_not_exist.json", scope_override=None, as_json=True)
    assert rc == 2  # structural error → fail closed (not a silent pass)


def test_main_exit_code_matches_run() -> None:
    assert gate.main(["--evidence", str(DEFAULT_EVIDENCE), "--json"]) == 1
