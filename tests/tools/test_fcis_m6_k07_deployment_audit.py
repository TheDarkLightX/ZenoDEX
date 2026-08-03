"""Focused tests for the fail-closed K07 deployment audit."""

import os
import subprocess
from pathlib import Path

from experiments.fcis_m6_k07_deployment_audit_check import run_checks
from src.core.fcis_m6_k07_deployment_audit import K07FindingKindV1
from tools.build_fcis_m6_k07_deployment_audit import _credential_findings

ROOT = Path(__file__).resolve().parents[2]


def test_k07_audit_preserves_deployment_gaps() -> None:
    result = run_checks()
    assert result["status"] == "GAP"
    assert result["finding_count"] == 3
    assert result["credential_findings"] == 0
    assert result["clean_gate"] == "BLOCKED"
    assert result["mutants_killed"] == 4


def test_k07_credential_default_mutant_remains_auditable() -> None:
    findings = _credential_findings(
        ".docker/entrypoint.sh",
        'export DEMO_API_TOKEN="${DEMO_API_TOKEN:-local-test-token}"\n',
        ("DEMO_API_TOKEN:-", "local-test-token"),
    )
    assert {(finding.kind, finding.marker) for finding in findings} == {
        (K07FindingKindV1.CREDENTIAL_POLICY_GAP, "DEMO_API_TOKEN:-"),
        (K07FindingKindV1.CREDENTIAL_POLICY_GAP, "local-test-token"),
    }


def test_entrypoint_rejects_demo_mode_without_secret_token() -> None:
    environment = os.environ.copy()
    environment.pop("DEMO_API_TOKEN", None)
    environment["ZENODEX_TESTNET_DEMO"] = "1"
    result = subprocess.run(
        ["bash", ".docker/entrypoint.sh"],
        cwd=ROOT,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
        timeout=5,
    )
    assert result.returncode != 0
    assert "DEMO_API_TOKEN must be supplied" in result.stderr
