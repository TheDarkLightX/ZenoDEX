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


def _registry(surfaces: dict, *, scope_id: str = "t", claim_scope: list | None = None) -> dict:
    """Build a registry. ``claim_scope`` defaults to the non-evidence_only rows
    (the gate REQUIRES an explicit claim_scope); pass it to test a mismatch."""
    if claim_scope is None:
        claim_scope = [s for s, ev in surfaces.items() if not is_evidence_only(ev)]
    return {
        "schema": gate.REGISTRY_SCHEMA,
        "scope_id": scope_id,
        "claim_scope": claim_scope,
        "surfaces": surfaces,
    }


def _write(tmp_path: Path, reg: dict) -> Path:
    p = tmp_path / "ev.json"
    p.write_text(json.dumps(reg), encoding="utf-8")
    return p


def _run(reg_path: Path, *, override=None, dev: bool = True) -> int:
    """Run the gate. ``dev=True`` (require_known_scope=False) is for synthetic
    't'-scope registries; ``dev=False`` exercises production mode (the scope_id
    must be a known, source-pinned scope)."""
    return gate.run(reg_path, scope_override=override, as_json=True, require_known_scope=not dev)


# --- shipped (production) registry ------------------------------------------


def test_default_registry_is_blocked_failclosed() -> None:
    # The shipped registry is an honest work-tracker: every column unverified, so
    # the gate MUST fail closed (exit 1) — no surface is production-ready yet.
    # Run in PRODUCTION mode (default): scope_id spot_dex is source-pinned.
    assert gate.run(DEFAULT_EVIDENCE, scope_override=None, as_json=True) == 1


def test_default_registry_covers_spot_dex_scope() -> None:
    raw = json.loads(DEFAULT_EVIDENCE.read_text(encoding="utf-8"))
    surfaces = raw["surfaces"]
    claim_surfaces = {s for s, ev in surfaces.items() if not is_evidence_only(ev)}
    evidence_only = {s for s, ev in surfaces.items() if is_evidence_only(ev)}
    assert claim_surfaces == set(SPOT_DEX_SCOPE)
    assert set(raw["claim_scope"]) == set(SPOT_DEX_SCOPE)
    assert raw["scope_id"] == "spot_dex"  # the source-pinned production scope
    # replay_guard is off the authority path: kept as evidence attached to nonces,
    # NOT deleted (deleting a row to pass the AND would be dishonest).
    assert "replay_guard" in evidence_only
    assert surfaces["replay_guard"].get("attached_to") == "nonces"
    # Honesty guard: NO surface has prematurely fully-cleared (open_gaps_closed),
    # so the scope claim stays blocked. Individual evidence columns MAY be
    # genuinely verified as surfaces make progress (e.g. nonces.authority_mode in
    # Phase 2); the gate's own tests assert the scope claim is still False.
    for surface in surfaces.values():
        assert surface["open_gaps_closed"] is False
    assert gate.run(DEFAULT_EVIDENCE, scope_override=None, as_json=True) == 1


def test_main_exit_code_matches_run() -> None:
    assert gate.main(["--evidence", str(DEFAULT_EVIDENCE), "--json"]) == 1


# --- generic claim logic (dev mode: synthetic scope_id) ----------------------


def test_all_clear_registry_passes(tmp_path: Path) -> None:
    assert _run(_write(tmp_path, _registry({s: _all_clear_surface() for s in SPOT_DEX_SCOPE}))) == 0


def test_one_blocked_surface_fails_the_scope(tmp_path: Path) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    surfaces["state_root"]["open_gaps_closed"] = False  # state_root evidence row still open
    assert _run(_write(tmp_path, _registry(surfaces))) == 1


def test_missing_registry_fails_closed(tmp_path: Path) -> None:
    assert _run(tmp_path / "does_not_exist.json") == 2  # structural error → fail closed


def test_missing_claim_scope_fails_closed(tmp_path: Path) -> None:
    reg = {
        "schema": gate.REGISTRY_SCHEMA,
        "scope_id": "t",
        "surfaces": {s: _all_clear_surface() for s in SPOT_DEX_SCOPE},
    }
    assert _run(_write(tmp_path, reg)) == 2


def test_wrong_registry_schema_fails_closed(tmp_path: Path) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    reg = _registry(surfaces)
    reg["schema"] = "zenodex/cbc-surface-evidence/v0"
    assert _run(_write(tmp_path, reg)) == 2


def test_duplicate_claim_scope_fails_closed(tmp_path: Path) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    reg = _registry(surfaces, claim_scope=["cpmm_swap", "cpmm_swap", "balances", "state_root", "nonces"])
    assert _run(_write(tmp_path, reg)) == 2


def test_blocked_evidence_only_surface_does_not_block_the_claim(tmp_path: Path) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    blocked = {c: {"ref": f"x/{c}.py", "verified": False} for c in CBC_COLUMNS if c != "open_gaps_closed"}
    blocked["open_gaps_closed"] = False
    blocked["claim_role"] = "evidence_only"
    blocked["attached_to"] = "nonces"
    surfaces["replay_guard"] = blocked
    assert _run(_write(tmp_path, _registry(surfaces))) == 0


def test_evidence_only_surface_excluded_from_scope_and_listed(tmp_path: Path, capsys) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    carrier = _all_clear_surface()
    carrier["claim_role"] = "evidence_only"
    carrier["attached_to"] = "nonces"
    surfaces["replay_guard"] = carrier
    rc = _run(_write(tmp_path, _registry(surfaces)))
    out = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert "replay_guard" not in out["scope"]
    assert out["evidence_only_surfaces"] == ["replay_guard"]


def test_all_evidence_only_registry_fails_closed(tmp_path: Path) -> None:
    carrier = _all_clear_surface()
    carrier["claim_role"] = "evidence_only"
    carrier["attached_to"] = "nonces"
    reg = {
        "schema": gate.REGISTRY_SCHEMA,
        "scope_id": "t",
        "claim_scope": ["nonces"],
        "surfaces": {"replay_guard": carrier},
    }
    assert _run(_write(tmp_path, reg)) == 2


def test_unknown_claim_role_fails_closed(tmp_path: Path) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    surfaces["nonces"]["claim_role"] = "evidenceonly"  # typo
    assert _run(_write(tmp_path, _registry(surfaces))) == 2


def test_dangling_evidence_only_attachment_fails_closed(tmp_path: Path) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    carrier = _all_clear_surface()
    carrier["claim_role"] = "evidence_only"
    carrier["attached_to"] = "ghost_surface"
    surfaces["replay_guard"] = carrier
    assert _run(_write(tmp_path, _registry(surfaces))) == 2


def test_mismarking_authority_surface_evidence_only_fails_closed(tmp_path: Path) -> None:
    # claim_scope-vs-computed mismatch backstop (fires in any mode).
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    surfaces["state_root"]["claim_role"] = "evidence_only"
    surfaces["state_root"]["attached_to"] = "balances"
    reg = _registry(surfaces, claim_scope=list(SPOT_DEX_SCOPE))  # still declares state_root
    assert _run(_write(tmp_path, reg)) == 2


def test_non_mapping_surface_row_fails_closed(tmp_path: Path) -> None:
    # A malformed (non-object) surface row must fail closed (exit 2), NOT escape
    # as a raw exit 1 that the release pipeline would treat as advisory.
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    surfaces["balances"] = "oops-not-an-object"
    reg = {
        "schema": gate.REGISTRY_SCHEMA,
        "scope_id": "t",
        "claim_scope": list(SPOT_DEX_SCOPE),
        "surfaces": surfaces,
    }
    assert _run(_write(tmp_path, reg)) == 2


@pytest.mark.parametrize(
    "mutate",
    [
        lambda s: s.__setitem__("running_impl", "src/x.py"),       # column should be an object
        lambda s: s.__setitem__("open_gaps_closed", "yes"),         # gate column should be a bool
        lambda s: s.__setitem__("formal_spec", {"ref": ["x"], "verified": True}),  # ref should be a str
        lambda s: s.__setitem__("proof_artifact", {"ref": "x", "verified": "true"}),  # verified should be a bool
    ],
)
def test_malformed_column_fails_closed(tmp_path: Path, mutate) -> None:
    # A present-but-malformed column is a SCHEMA violation -> exit 2, not a silent
    # uncleared gap (exit 1). (Gemini final review.)
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    mutate(surfaces["state_root"])
    reg = {
        "schema": gate.REGISTRY_SCHEMA,
        "scope_id": "t",
        "claim_scope": list(SPOT_DEX_SCOPE),
        "surfaces": surfaces,
    }
    assert _run(_write(tmp_path, reg)) == 2


def test_deeply_nested_registry_fails_closed(tmp_path: Path) -> None:
    # A pathological registry whose JSON is deeply nested makes json.loads raise
    # RecursionError; the gate must still fail closed (exit 2), not leak a raw
    # exit-1 traceback the pipeline treats as advisory. (Codex final review.)
    p = tmp_path / "ev.json"
    p.write_text("[" * 200_000 + "]" * 200_000, encoding="utf-8")
    assert _run(p) == 2


# --- --scope override safety -------------------------------------------------


def test_scope_override_cannot_claim_evidence_only_surface(tmp_path: Path) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    carrier = _all_clear_surface()
    carrier["claim_role"] = "evidence_only"
    carrier["attached_to"] = "nonces"
    surfaces["replay_guard"] = carrier
    assert _run(_write(tmp_path, _registry(surfaces)), override=["replay_guard"]) == 2


def test_scope_override_subset_of_authority_still_works(tmp_path: Path) -> None:
    p = _write(tmp_path, _registry({s: _all_clear_surface() for s in SPOT_DEX_SCOPE}))
    assert _run(p, override=["cpmm_swap"]) == 0
    assert _run(p, override=["nope"]) == 2  # unknown surface in override fails closed


def test_scope_override_disallowed_in_production_mode(tmp_path: Path) -> None:
    p = _write(
        tmp_path,
        _registry(
            {s: _all_clear_surface() for s in SPOT_DEX_SCOPE},
            scope_id="spot_dex",
            claim_scope=list(SPOT_DEX_SCOPE),
        ),
    )
    assert _run(p, override=["cpmm_swap"], dev=False) == 2
    assert gate.main(["--evidence", str(p), "--json", "--scope", "cpmm_swap"]) == 2


# --- production-mode scope pinning (the name-binding fix) --------------------


def test_pinned_scope_with_full_authority_set_passes(tmp_path: Path) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    reg = _registry(surfaces, scope_id="spot_dex", claim_scope=list(SPOT_DEX_SCOPE))
    assert _run(_write(tmp_path, reg), dev=False) == 0  # production mode, full pinned set


def test_paired_shrink_of_pinned_scope_fails_closed(tmp_path: Path) -> None:
    # Coordinated edit: mark state_root evidence_only + drop from claim_scope, but
    # keep scope_id=spot_dex -> anchored to source SPOT_DEX_SCOPE -> fail closed.
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    surfaces["state_root"]["claim_role"] = "evidence_only"
    surfaces["state_root"]["attached_to"] = "balances"
    reg = _registry(surfaces, scope_id="spot_dex", claim_scope=["cpmm_swap", "balances", "nonces"])
    assert _run(_write(tmp_path, reg), dev=False) == 2


def test_renamed_scope_id_paired_shrink_fails_closed(tmp_path: Path) -> None:
    # The name-binding bypass: rename scope_id to an UNKNOWN value alongside the
    # paired shrink. Production mode requires a known scope_id, so this fails
    # closed instead of fail-open-skipping the source pin.
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    surfaces["state_root"]["claim_role"] = "evidence_only"
    surfaces["state_root"]["attached_to"] = "balances"
    reg = _registry(surfaces, scope_id="spot_dex_bypassed", claim_scope=["cpmm_swap", "balances", "nonces"])
    assert _run(_write(tmp_path, reg), dev=False) == 2


def test_missing_scope_id_fails_closed_in_production(tmp_path: Path) -> None:
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    reg = {
        "schema": gate.REGISTRY_SCHEMA,
        "claim_scope": list(SPOT_DEX_SCOPE),
        "surfaces": surfaces,
    }  # no scope_id
    assert _run(_write(tmp_path, reg), dev=False) == 2


def test_allow_unpinned_scope_flag_permits_dev_registry(tmp_path: Path) -> None:
    # The escape hatch: an arbitrary scope_id is allowed in dev mode (and via the
    # --allow-unpinned-scope CLI flag), but NEVER in production mode.
    surfaces = {s: _all_clear_surface() for s in SPOT_DEX_SCOPE}
    p = _write(tmp_path, _registry(surfaces, scope_id="my_dev_scope"))
    assert _run(p, dev=True) == 0  # dev: unpinned scope_id allowed
    assert _run(p, dev=False) == 2  # production: unknown scope_id fails closed
    assert gate.main(["--evidence", str(p), "--json", "--allow-unpinned-scope"]) == 0
    assert gate.main(["--evidence", str(p), "--json"]) == 2  # production default
