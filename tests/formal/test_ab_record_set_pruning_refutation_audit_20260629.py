from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from tools.check_ab_record_set_pruning_refutation_audit_20260629 import (
    REPORT_JSON,
    TARGET_NEGATIVE_CONTROL_COUNT,
    build_report,
)

ROOT = Path(__file__).resolve().parents[2]


@pytest.fixture(scope="module")
def audit_report() -> dict[str, object]:
    return build_report()


def test_record_set_refutation_audit_report(audit_report: dict[str, object]) -> None:
    search = audit_report["search"]

    assert audit_report["ok"] is True
    assert search["ok"] is True
    assert search["reasons"] == []
    assert search["negative_control_count"] == TARGET_NEGATIVE_CONTROL_COUNT
    assert search["negative_control_accept_count"] == 0
    assert audit_report["deterministic_replay"]["ok"] is True
    assert audit_report["hypothesis_card"]["status"] == "supported"


def test_record_set_refutation_audit_lean_surface(audit_report: dict[str, object]) -> None:
    lean_surface = audit_report["search"]["lean_surface"]
    claim_surface = audit_report["search"]["claim_surface"]

    assert lean_surface["placeholder_free"] is True
    assert lean_surface["required_theorem_count"] == 8
    assert len(lean_surface["strict_record_set_certificate_decl_hash"]) == 64
    assert len(lean_surface["strict_record_set_validates_decl_hash"]) == 64
    assert claim_surface == {
        "same_processed_reserve_bound": True,
        "selected_min_reserve_bound": True,
        "selected_suffix_executable_bound": True,
        "economic_key_dominance_bound": True,
        "scope_nonclaims_bound": True,
    }


def test_record_set_refutation_audit_report_bindings(audit_report: dict[str, object]) -> None:
    bindings = audit_report["search"]["report_bindings"]

    assert bindings["record_key_schema"] == (
        "zenodex.ab_strict_zero_min_record_key_certificate_lean_report.v1"
    )
    assert bindings["record_key_ok"] is True
    assert bindings["record_key_theorem_count"] == 6
    assert bindings["record_set_status"] == "pass"
    assert bindings["record_set_theorem_count"] == 4


def test_record_set_refutation_audit_verification_commands(
    audit_report: dict[str, object],
) -> None:
    commands = audit_report["search"]["verification_commands"]

    assert set(commands) == {
        "lake_env_lean",
        "lake_build_module",
        "focused_pytest",
        "public_claim_scope",
        "claims_registry",
    }
    for result in commands.values():
        assert result["ok"] is True
        assert result["returncode"] == 0


def test_record_set_refutation_audit_negative_controls(
    audit_report: dict[str, object],
) -> None:
    controls = audit_report["search"]["negative_controls"]

    assert len(controls) == TARGET_NEGATIVE_CONTROL_COUNT
    for control in controls:
        assert control["accepted"] is False
        assert control["expected_reason"] in control["reasons"]

    assert {control["expected_reason"] for control in controls} == {
        "lean_placeholder_token_present",
        "same_processed_reserve_premise_missing",
        "selected_min_reserve_premise_missing",
        "selected_suffix_executable_premise_missing",
        "forbidden_full_subset_dp_claim",
        "record_key_report_not_ok",
        "record_key_theorem_list_incomplete",
        "forbidden_authority_claim",
    }


def test_record_set_refutation_audit_non_claims(audit_report: dict[str, object]) -> None:
    non_claims = "\n".join(audit_report["non_claims"])

    assert "does not prove Python-to-Lean refinement" in non_claims
    assert "does not construct a subset DP table" in non_claims
    assert "does not define canonical tie order" in non_claims
    assert "does not cover nonzero min_amount_out behavior" in non_claims
    assert "No settlement" in non_claims


def test_record_set_refutation_audit_cli_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/check_ab_record_set_pruning_refutation_audit_20260629.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=240,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["search"]["negative_control_accept_count"] == 0
