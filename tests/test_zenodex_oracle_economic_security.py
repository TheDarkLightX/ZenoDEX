from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_economic_security import sample_envelope  # noqa: E402

from src.core.oracle_economic_security import (  # noqa: E402
    verify_economic_security_envelope,
)


def _run_verify(tmp_path: Path, envelope: dict) -> tuple[int, dict]:
    path = tmp_path / "economic-security.json"
    path.write_text(json.dumps(envelope, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_economic_security.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_economic_security_accepts_sample_envelope(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_envelope())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["required_attack_cost_e8"] == 60_000_000_000
    assert result["required_reporter_reward_per_report_e8"] == 25_000_000
    assert result["total_reporter_reward_e8"] == 90_000_000
    assert result["slash_amount_e8"] == 125_000_000_000
    assert result["required_deterrence_slash_e8"] == 60_000_000_000
    assert result["fee_spend_total_e8"] == 100_000_000
    assert result["errors"] == []


def test_economic_security_rejects_extractable_above_notional(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["max_extractable_value_e8"] = envelope["notional_value_e8"] + 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "extractable_value_exceeds_notional" in result["errors"]


def test_economic_security_rejects_attack_cost_below_margin(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["attack_cost_floor_e8"] = 59_999_999_999
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "attack_cost_floor_below_required_margin" in result["errors"]


def test_economic_security_rejects_reward_below_honest_cost(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["reporter_reward_per_report_e8"] = 24_999_999
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "reporter_reward_below_honest_cost_plus_risk" in result["errors"]


def test_economic_security_rejects_reward_budget_exceeded(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["reporter_reward_budget_e8"] = 89_999_999
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "reporter_reward_budget_exceeded" in result["errors"]


def test_economic_security_rejects_expected_cheat_gain_above_extractable(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["expected_cheat_gain_e8"] = envelope["max_extractable_value_e8"] + 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "expected_cheat_gain_exceeds_extractable_value" in result["errors"]


def test_economic_security_rejects_weak_slash_deterrence(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["slash_fraction_bps"] = 1_000
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "slash_deterrence_below_required_margin" in result["errors"]


def test_economic_security_rejects_dispute_reward_budget_exceeded(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["dispute_reward_e8"] = envelope["dispute_budget_e8"] + 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "dispute_reward_budget_exceeded" in result["errors"]


def test_economic_security_rejects_fee_overspend(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["burn_fee_share_e8"] += 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "fee_shares_exceed_fee_paid" in result["errors"]


def test_economic_security_rejects_hidden_field(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["hidden_mint"] = 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "unknown_economic_security_field:hidden_mint" in result["errors"]


def test_economic_security_rejects_boolean_amount(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["attack_cost_floor_e8"] = True
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "attack_cost_floor_e8_must_be_int_between_0_and_1000000000000000000000000000000" in result["errors"]


def test_economic_security_rejects_wrong_schema(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["schema"] = "zenodex.oracle.economic_security_envelope.v0"
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "economic_security_schema_mismatch" in result["errors"]


def test_economic_security_rejects_hostile_key_before_lookup() -> None:
    class ExplodingKey:
        def __hash__(self) -> int:
            return hash("query_id")

        def __eq__(self, _other: object) -> bool:
            raise AssertionError("hostile envelope key was compared")

    envelope: dict[Any, Any] = sample_envelope()
    del envelope["query_id"]
    envelope[ExplodingKey()] = "sha256:" + "1" * 64

    result = verify_economic_security_envelope(envelope)

    assert result.status == "rejected"
    assert result.errors == ("economic_security_field_must_be_string",)


def test_economic_security_rejects_hostile_schema_without_comparison() -> None:
    class ExplodingEq:
        def __eq__(self, _other: object) -> bool:
            raise AssertionError("hostile schema value was compared")

    envelope = sample_envelope()
    envelope["schema"] = ExplodingEq()

    result = verify_economic_security_envelope(envelope)

    assert result.status == "rejected"
    assert "economic_security_schema_mismatch" in result.errors


def test_economic_security_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-economic-security.json"
    path.write_text('{"padding":"' + ("x" * 250_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_economic_security.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(error.startswith("economic_security_load_failed:economic_security_file_too_large:") for error in result["errors"])


def test_economic_security_sample_cli_emits_verifiable_envelope(tmp_path: Path) -> None:
    path = tmp_path / "sample-economic-security.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_economic_security.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_economic_security.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"
