from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
REPORT_JSON = REPO / "generated" / "zenodex_oracle_coupled_inequality_certificate_20260627" / "report.json"
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_coupled_inequality_certificate_20260627 import build_certificate, run_cases  # noqa: E402
from zenodex_oracle_economic_security import sample_envelope  # noqa: E402


def _case(report: dict, case_id: str) -> dict:
    for row in report["cases"]:
        if row["case_id"] == case_id:
            return row
    raise AssertionError(f"missing case {case_id}")


def test_coupled_inequality_certificate_replay() -> None:
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_coupled_inequality_certificate_20260627.py"],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=30,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    result = json.loads(proc.stdout)
    assert result["ok"] is True
    assert result["rule_count"] == 8
    assert result["case_count"] == 5

    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert all(row["parity_ok"] for row in report["cases"])


def test_coupled_certificate_rejects_previous_cartesian_counterexamples() -> None:
    report = run_cases()
    attack = _case(report, "attack_margin_counterexample_now_rejected")
    reward = _case(report, "reporter_reward_counterexample_now_rejected")
    slash = _case(report, "slash_counterexample_now_rejected")

    assert attack["certificate_ok"] is False
    assert attack["failed_rule_errors"] == ["attack_cost_floor_below_required_margin"]
    assert reward["certificate_ok"] is False
    assert reward["failed_rule_errors"] == ["reporter_reward_budget_exceeded"]
    assert slash["certificate_ok"] is False
    assert slash["failed_rule_errors"] == ["slash_deterrence_below_required_margin"]


def test_slash_rule_matches_floor_ceil_boundary() -> None:
    envelope = sample_envelope()
    envelope["reporter_bond_required_e8"] = 120_000_000_000
    envelope["slash_fraction_bps"] = 2_400
    rejected = build_certificate(envelope)
    assert rejected["certificate_ok"] is False
    assert rejected["failed_rule_errors"] == ["slash_deterrence_below_required_margin"]
    assert rejected["parity_ok"] is True

    envelope["slash_fraction_bps"] = 5_000
    accepted = build_certificate(envelope)
    assert accepted["certificate_ok"] is True
    assert accepted["verifier_ok"] is True
    assert accepted["parity_ok"] is True


def test_domain_error_parity_for_boolean_amount() -> None:
    envelope = sample_envelope()
    envelope["attack_cost_floor_e8"] = True
    certificate = build_certificate(envelope)

    assert certificate["certificate_ok"] is False
    assert certificate["verifier_ok"] is False
    assert certificate["parity_ok"] is True
    assert "attack_cost_floor_e8_must_be_int_between_0_and_1000000000000000000000000000000" in certificate["domain_errors"]


def test_metadata_domain_errors_match_pointwise_verifier() -> None:
    envelope = sample_envelope()
    envelope["schema"] = "zenodex.oracle.economic_security_envelope.v0"
    envelope["query_id"] = "not-a-hash"
    envelope["consumer_module"] = "ZenoDEX Perps"
    envelope["action_kind"] = ""
    envelope["hidden_mint"] = 1
    certificate = build_certificate(envelope)

    assert certificate["certificate_ok"] is False
    assert certificate["verifier_ok"] is False
    assert certificate["parity_ok"] is True
    assert set(certificate["domain_errors"]) == {
        "unknown_economic_security_field:hidden_mint",
        "economic_security_schema_mismatch",
        "query_id_must_be_sha256",
        "consumer_module_must_be_token",
        "action_kind_must_be_token",
    }


def test_coupled_certificate_non_claims_are_scoped() -> None:
    report = run_cases()
    non_claims = "\n".join(report["non_claims"])
    assert "does not estimate MEV" in non_claims
    assert "does not authorize oracle updates" in non_claims
    assert "not a maximal polytope enumerator" in non_claims
