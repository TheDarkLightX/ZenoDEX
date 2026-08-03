"""Focused adversarial tests for the K06 legacy-path seal."""

from experiments.fcis_m6_k06_legacy_seal_check import run_checks


def test_k06_legacy_seal_and_runtime_gate() -> None:
    result = run_checks()
    assert result["target_admission"] == "PASS"
    assert result["legacy_admission"] == "REJECTED"
    assert result["mutants_killed"] == 10
