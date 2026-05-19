from __future__ import annotations

from tools.check_production_key_management_completion import run_check


def test_production_key_management_completion_audit_accepts() -> None:
    result = run_check()

    assert result["schema"] == "zenodex.production_key_management.completion_audit.v1"
    assert result["ok"] is True
    assert result["errors"] == []
    assert {
        item["criterion"]
        for item in result["criteria"]
        if item["ok"] is True
    } == {
        "property_checker_green",
        "ESSO_or_equivalent_finite_model_green",
        "Lean_receipt_green",
        "runtime_admission_library_green",
        "privileged_action_gates_wired",
        "release_gate_checks_key_management",
        "operator_runbook_exists",
        "no_private_key_material_in_repo",
    }
