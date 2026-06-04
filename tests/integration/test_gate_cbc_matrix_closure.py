"""Tests for the CBC matrix-closure gate (Phase 0)."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

import tools.gate_cbc_matrix_closure as gate
from src.integration.surface_security_claim import (
    CBC_COLUMNS,
    SPOT_DEX_SCOPE,
    is_evidence_only,
)

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
    surfaces = raw["surfaces"]
    # The claim-scope surfaces (authority path) are exactly SPOT_DEX_SCOPE; any
    # evidence-only row (a proof-carrier) is retained but excluded from the claim.
    claim_surfaces = {s for s, ev in surfaces.items() if not is_evidence_only(ev)}
    evidence_only = {s for s, ev in surfaces.items() if is_evidence_only(ev)}
    assert claim_surfaces == set(SPOT_DEX_SCOPE)
    # replay_guard is off the authority path: kept as evidence attached to nonces,
    # NOT deleted (deleting a row to pass the AND would be dishonest).
    assert "replay_guard" in evidence_only
    assert surfaces["replay_guard"].get("attached_to") == "nonces"
    # Honesty guard: nothing in the shipped registry is hand-set to verified:true.
    for surface in surfaces.values():
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


def test_blocked_evidence_only_surface_does_not_block_the_claim(tmp_path: Path) -> None:
    # All authority surfaces clear, plus a fully-BLOCKED evidence-only proof-carrier.
    # The carrier must NOT block the claim — it is excluded from the AND.
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    blocked_carrier = {
        c: {"ref": f"x/{c}.py", "verified": False} for c in CBC_COLUMNS if c != "open_gaps_closed"
    }
    blocked_carrier["open_gaps_closed"] = False
    blocked_carrier["claim_role"] = "evidence_only"
    blocked_carrier["attached_to"] = "nonces"
    surfaces["replay_guard"] = blocked_carrier
    reg = {"schema": "x", "scope_id": "t", "surfaces": surfaces}
    p = tmp_path / "ev.json"
    p.write_text(json.dumps(reg), encoding="utf-8")
    assert gate.run(p, scope_override=None, as_json=True) == 0


def test_evidence_only_surface_excluded_from_scope_and_listed(tmp_path: Path, capsys) -> None:
    # Even a fully-CLEAR evidence-only row stays OUT of the claim scope (it can
    # neither block nor inflate the claim) and is reported separately.
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    carrier = _all_clear_surface()
    carrier["claim_role"] = "evidence_only"
    carrier["attached_to"] = "nonces"
    surfaces["replay_guard"] = carrier
    reg = {"schema": "x", "scope_id": "t", "surfaces": surfaces}
    p = tmp_path / "ev.json"
    p.write_text(json.dumps(reg), encoding="utf-8")
    rc = gate.run(p, scope_override=None, as_json=True)
    out = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert "replay_guard" not in out["scope"]
    assert out["evidence_only_surfaces"] == ["replay_guard"]


def test_all_evidence_only_registry_fails_closed(tmp_path: Path) -> None:
    # A registry with no authority surfaces (every row evidence_only) is a
    # structural error — there is nothing to claim. Fail closed (exit 2).
    carrier = _all_clear_surface()
    carrier["claim_role"] = "evidence_only"
    reg = {"schema": "x", "scope_id": "t", "surfaces": {"replay_guard": carrier}}
    p = tmp_path / "ev.json"
    p.write_text(json.dumps(reg), encoding="utf-8")
    assert gate.run(p, scope_override=None, as_json=True) == 2


def test_unknown_claim_role_fails_closed(tmp_path: Path) -> None:
    # An unknown/typo'd claim_role must fail closed, not be silently treated as
    # authority (or silently dropped).
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    surfaces["nonces"]["claim_role"] = "evidenceonly"  # typo
    reg = {"schema": "x", "scope_id": "t", "surfaces": surfaces}
    p = tmp_path / "ev.json"
    p.write_text(json.dumps(reg), encoding="utf-8")
    assert gate.run(p, scope_override=None, as_json=True) == 2


def test_dangling_evidence_only_attachment_fails_closed(tmp_path: Path) -> None:
    # An evidence_only row attached to a non-authority / missing surface is an
    # orphan — fail closed (no claim theater).
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    carrier = _all_clear_surface()
    carrier["claim_role"] = "evidence_only"
    carrier["attached_to"] = "ghost_surface"
    surfaces["replay_guard"] = carrier
    reg = {"schema": "x", "scope_id": "t", "surfaces": surfaces}
    p = tmp_path / "ev.json"
    p.write_text(json.dumps(reg), encoding="utf-8")
    assert gate.run(p, scope_override=None, as_json=True) == 2


def test_mismarking_authority_surface_evidence_only_fails_closed(tmp_path: Path) -> None:
    # The declared claim_scope is a backstop: mismarking a real authority surface
    # as evidence_only shrinks the computed scope, which no longer matches the
    # declared claim_scope -> fail closed (the surface cannot silently vanish).
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    surfaces["state_root"]["claim_role"] = "evidence_only"
    surfaces["state_root"]["attached_to"] = "balances"  # even with a valid attach
    reg = {
        "schema": "x",
        "scope_id": "t",
        "claim_scope": list(SPOT_DEX_SCOPE),  # still declares state_root as authority
        "surfaces": surfaces,
    }
    p = tmp_path / "ev.json"
    p.write_text(json.dumps(reg), encoding="utf-8")
    assert gate.run(p, scope_override=None, as_json=True) == 2
