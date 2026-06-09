"""Differential parity: the Tau spec and gov_gate.py must AGREE with the shared expected
verdict on every boundary scenario (the repo's dual-checker discipline). Neither gate is
trusted over the other.

Each case is evaluated:
  * in Python  -- the relevant gov_gate.py gate function;
  * in Tau     -- ground `sat(spec_body && <all inputs> && out=1)` (T iff admitted).
Both must equal the shared `expect`. Skips cleanly if the Tau binary is unavailable.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

_GOV = Path(__file__).resolve().parents[3] / "src" / "tau_specs" / "governance"
sys.path.insert(0, str(_GOV))

import gov_gate  # noqa: E402
import gov_parity_cases as cases  # noqa: E402
from validate_governance_specs import TAU, extract_body, run_tau  # noqa: E402

PY_GATE = {
    "fee": gov_gate.fee_revision_ok,
    "router_split": gov_gate.router_split_revision_ok,
    "collateral": gov_gate.collateral_ratio_revision_ok,
    "whale": gov_gate.whale_defense_revision_ok,
    "action": gov_gate.action_bound_ok,
    "funding": gov_gate.funding_rate_revision_ok,
    # trajectory tier (pure bits)
    "drift": gov_gate.drift_budget_ok,
    "cooldown": gov_gate.cooldown_ok,
    "charter": gov_gate.charter_ok,
    "epoch_budget": gov_gate.epoch_budget_ok,
}


def _tau_admits(surface: str, kwargs: dict) -> bool:
    spec_file, out, mapping = cases.SURFACE_TAU[surface]
    body = extract_body(_GOV / spec_file)
    clauses = []
    for key, val in kwargs.items():
        kind, var = mapping[key]
        if kind == "sbf":
            clauses.append(f"({var}:sbf = {1 if val else 0}:sbf)")
        else:
            clauses.append(f"({var}:bv[16] = {{ #x{int(val) & 0xFFFF:04X} }}:bv[16])")
    clauses.append(f"({out}:sbf = 1:sbf)")
    query = f"sat ({body}) && " + " && ".join(clauses)
    return run_tau(query) == "T"


@pytest.mark.skipif(not TAU.exists(), reason="tau binary not available")
@pytest.mark.parametrize("surface,kwargs,expect", cases.CASES)
def test_tau_python_parity(surface: str, kwargs: dict, expect: bool):
    py = PY_GATE[surface](**kwargs)
    assert py == expect, f"python gate {surface} {kwargs}: got {py}, expected {expect}"
    tau = _tau_admits(surface, kwargs)
    assert tau == expect, f"tau spec {surface} {kwargs}: got {tau}, expected {expect}"
    assert py == tau, f"DUAL-CHECKER DISAGREEMENT {surface} {kwargs}: python={py} tau={tau}"

