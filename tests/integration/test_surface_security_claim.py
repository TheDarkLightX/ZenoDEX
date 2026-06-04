"""Tests for the per-surface computed production-security claim (Phase 0).

Covers the accept path, every fail-closed reject path (per CBC column), the
gate-vs-evidence column distinction, scope AND semantics, deterministic gap
ordering, and invalid-input handling.
"""

from __future__ import annotations

import pytest

from src.integration.surface_security_claim import (
    CBC_COLUMNS,
    SPOT_DEX_SCOPE,
    evaluate_scope_security_claim,
    evaluate_surface_security_claim,
)


def _verified(ref: str) -> dict:
    return {"ref": ref, "verified": True}


def _complete_evidence() -> dict:
    """All seven CBC columns cleared."""
    return {
        "running_impl": _verified("src/core/cpmm.py"),
        "formal_spec": _verified("src/kernels/dex/cpmm_v1.yaml"),
        "proof_artifact": _verified("runs/cpmm.synth.json"),
        "differential_tests": _verified("tests/runtime/test_cbc_closure_cpmm.py"),
        "runtime_invariants": _verified("src/tau_specs/cpmm_v1.tau"),
        "authority_mode": _verified("config/deploy/production-strict.yaml"),
        "open_gaps_closed": True,
    }


# --- single-surface accept / reject ---------------------------------------


def test_complete_evidence_claims_ready() -> None:
    res = evaluate_surface_security_claim("cpmm_swap", _complete_evidence())
    assert res["surface_security_claim"] is True
    assert res["status"] == "ready"
    assert res["gaps"] == []
    assert all(res["columns"][c] for c in CBC_COLUMNS)


def test_empty_evidence_fails_closed_with_all_gaps() -> None:
    res = evaluate_surface_security_claim("cpmm_swap", {})
    assert res["surface_security_claim"] is False
    assert res["status"] == "blocked"
    assert len(res["gaps"]) == len(CBC_COLUMNS)
    assert all(res["columns"][c] is False for c in CBC_COLUMNS)


@pytest.mark.parametrize("missing", CBC_COLUMNS)
def test_each_missing_column_blocks_the_claim(missing: str) -> None:
    evidence = _complete_evidence()
    del evidence[missing]
    res = evaluate_surface_security_claim("balances", evidence)
    assert res["surface_security_claim"] is False
    assert res["columns"][missing] is False
    assert res["gaps"] == [f"balances: CBC column '{missing}' not cleared"]


def test_gaps_are_in_deterministic_cbc_column_order() -> None:
    res = evaluate_surface_security_claim("state_root", {})
    expected = [f"state_root: CBC column '{c}' not cleared" for c in CBC_COLUMNS]
    assert res["gaps"] == expected


# --- evidence-column clearing rules (fail-closed) --------------------------


def test_evidence_column_requires_verified_true_literal() -> None:
    evidence = _complete_evidence()
    evidence["proof_artifact"] = {"ref": "runs/x.json", "verified": "true"}  # string, not bool
    res = evaluate_surface_security_claim("nonces", evidence)
    assert res["columns"]["proof_artifact"] is False
    assert res["surface_security_claim"] is False


def test_evidence_column_requires_nonempty_ref() -> None:
    evidence = _complete_evidence()
    evidence["formal_spec"] = {"ref": "   ", "verified": True}
    res = evaluate_surface_security_claim("nonces", evidence)
    assert res["columns"]["formal_spec"] is False


def test_evidence_column_missing_verified_is_not_cleared() -> None:
    evidence = _complete_evidence()
    evidence["differential_tests"] = {"ref": "tests/x.py"}  # no verified flag
    res = evaluate_surface_security_claim("nonces", evidence)
    assert res["columns"]["differential_tests"] is False


def test_evidence_column_non_mapping_is_not_cleared() -> None:
    evidence = _complete_evidence()
    evidence["running_impl"] = "src/core/cpmm.py"  # bare string, not a verified ref
    res = evaluate_surface_security_claim("nonces", evidence)
    assert res["columns"]["running_impl"] is False


# --- gate column (open_gaps_closed) ----------------------------------------


def test_open_gaps_gate_requires_literal_true() -> None:
    for bad in (False, 1, "true", {"ref": "x", "verified": True}, None):
        evidence = _complete_evidence()
        evidence["open_gaps_closed"] = bad
        res = evaluate_surface_security_claim("replay_guard", evidence)
        assert res["columns"]["open_gaps_closed"] is False, bad
        assert res["surface_security_claim"] is False


# --- scope AND semantics ---------------------------------------------------


def test_scope_claim_true_only_when_all_surfaces_ready() -> None:
    by_surface = {s: _complete_evidence() for s in SPOT_DEX_SCOPE}
    res = evaluate_scope_security_claim(SPOT_DEX_SCOPE, by_surface)
    assert res["production_security_claim"] is True
    assert res["status"] == "ready"
    assert res["gaps"] == []


def test_scope_claim_false_if_one_surface_blocked() -> None:
    by_surface = {s: _complete_evidence() for s in SPOT_DEX_SCOPE}
    del by_surface["state_root"]["proof_artifact"]  # block one surface
    res = evaluate_scope_security_claim(SPOT_DEX_SCOPE, by_surface)
    assert res["production_security_claim"] is False
    assert res["per_surface"]["state_root"]["surface_security_claim"] is False
    assert res["per_surface"]["cpmm_swap"]["surface_security_claim"] is True
    assert any("state_root" in g and "proof_artifact" in g for g in res["gaps"])


def test_scope_missing_surface_evidence_fails_closed() -> None:
    by_surface = {s: _complete_evidence() for s in SPOT_DEX_SCOPE}
    del by_surface["nonces"]  # no evidence object at all
    res = evaluate_scope_security_claim(SPOT_DEX_SCOPE, by_surface)
    assert res["production_security_claim"] is False
    assert res["per_surface"]["nonces"]["surface_security_claim"] is False
    assert any("nonces: no evidence object provided" == g for g in res["gaps"])


def test_independent_surfaces_one_ready_one_blocked() -> None:
    # The whole point of per-surface: a ready surface stays ready even while a
    # sibling in the same scope is blocked (the scope AND is false, but the ready
    # surface's own claim is true).
    by_surface = {"cpmm_swap": _complete_evidence(), "balances": {}}
    res = evaluate_scope_security_claim(["cpmm_swap", "balances"], by_surface)
    assert res["per_surface"]["cpmm_swap"]["surface_security_claim"] is True
    assert res["per_surface"]["balances"]["surface_security_claim"] is False
    assert res["production_security_claim"] is False


# --- invalid inputs raise (structural, not evidence gaps) ------------------


def test_invalid_inputs_raise() -> None:
    with pytest.raises(ValueError):
        evaluate_surface_security_claim("", _complete_evidence())
    with pytest.raises(ValueError):
        evaluate_surface_security_claim("x", ["not", "a", "mapping"])  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        evaluate_scope_security_claim([], {})
    with pytest.raises(ValueError):
        evaluate_scope_security_claim(SPOT_DEX_SCOPE, ["nope"])  # type: ignore[arg-type]
