"""Focused tests for the fail-closed K07 deployment audit."""

from experiments.fcis_m6_k07_deployment_audit_check import run_checks


def test_k07_audit_preserves_deployment_gaps() -> None:
    result = run_checks()
    assert result["status"] == "GAP"
    assert result["finding_count"] == 5
    assert result["clean_gate"] == "BLOCKED"
    assert result["mutants_killed"] == 4
