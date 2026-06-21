from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

from zenodex_oracle_dispute_game import sample_envelope  # noqa: E402
from zenodex_oracle_dispute_game import verify_dispute_game_envelope  # noqa: E402


def _run_verify(tmp_path: Path, envelope: dict) -> tuple[int, dict]:
    path = tmp_path / "dispute-game.json"
    path.write_text(json.dumps(envelope, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_dispute_game.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.stderr == ""
    return proc.returncode, json.loads(proc.stdout)


def test_dispute_game_accepts_sample_envelope(tmp_path: Path) -> None:
    code, result = _run_verify(tmp_path, sample_envelope())
    assert code == 0
    assert result["ok"] is True
    assert result["status"] == "accepted"
    assert result["honest_challenge_profit_e8"] == 5_000_000
    assert result["frivolous_dispute_profit_e8"] == -10_000_000
    assert result["profit_feasible"] is True
    assert result["slash_amount_e8"] == 125_000_000_000
    assert result["required_deterrence_slash_e8"] == 60_000_000_000
    assert result["errors"] == []


def test_dispute_game_rejects_zero_bond(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["dispute_bond_e8"] = 0
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "dispute_bond_must_be_positive" in result["errors"]


def test_dispute_game_rejects_bond_above_honest_gain(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["dispute_bond_e8"] = envelope["dispute_reward_e8"] + 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "honest_challenge_not_profitable" in result["errors"]
    assert result["profit_feasible"] is False


def test_dispute_game_rejects_bond_below_frivolous_mev(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["mev_reject_dispute_e8"] = envelope["dispute_bond_e8"]
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "frivolous_dispute_not_deterred" in result["errors"]
    assert result["profit_feasible"] is False


def test_dispute_game_rejects_mev_reject_exceeds_honest_gain(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["mev_reject_dispute_e8"] = envelope["dispute_reward_e8"] + 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "frivolous_dispute_not_deterred" in result["errors"]
    assert "dispute_game_infeasible_mev_reject_exceeds_honest_gain" in result["errors"]


def test_dispute_game_rejects_mev_reject_equals_honest_gain(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["mev_reject_dispute_e8"] = envelope["dispute_reward_e8"]
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "dispute_game_infeasible_mev_reject_equals_honest_gain" in result["errors"]


def test_dispute_game_rejects_reward_budget_exceeded(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["dispute_reward_e8"] = envelope["dispute_budget_e8"] + 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "dispute_reward_budget_exceeded" in result["errors"]


def test_dispute_game_rejects_weak_slash_deterrence(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["slash_fraction_bps"] = 1_000
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "slash_deterrence_below_required_margin" in result["errors"]


def test_dispute_game_rejects_prob_inversion(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["prob_upheld_when_wrong_bps"] = 0
    envelope["prob_upheld_when_correct_bps"] = 100
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "prob_upheld_when_wrong_below_prob_upheld_when_correct" in result["errors"]


def test_dispute_game_rejects_unknown_field(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["hidden_field"] = 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "unknown_dispute_game_field:hidden_field" in result["errors"]


def test_dispute_game_rejects_wrong_schema(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["schema"] = "zenodex.oracle.dispute_game_envelope.v0"
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "dispute_game_schema_mismatch" in result["errors"]


def test_dispute_game_verify_inconclusive_on_oversized_file(tmp_path: Path) -> None:
    path = tmp_path / "oversized-dispute-game.json"
    path.write_text('{"padding":"' + ("x" * 250_001) + '"}', encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_dispute_game.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    assert proc.stderr == ""
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any(
        error.startswith("dispute_game_load_failed:dispute_game_file_too_large:")
        for error in result["errors"]
    )


def test_dispute_game_sample_cli_emits_verifiable_envelope(tmp_path: Path) -> None:
    path = tmp_path / "sample-dispute-game.json"
    sample = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_dispute_game.py", "sample", "--output", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    verify = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_dispute_game.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    result = json.loads(verify.stdout)
    assert result["status"] == "accepted"


def test_dispute_game_accepts_mev_uphold_nonzero(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["mev_uphold_dispute_e8"] = 5_000_000
    envelope["dispute_bond_e8"] = 18_000_000
    code, result = _run_verify(tmp_path, envelope)
    assert code == 0
    assert result["honest_challenge_profit_e8"] == 2_000_000
    assert result["frivolous_dispute_profit_e8"] == -18_000_000
    assert result["profit_feasible"] is True


def test_dispute_game_rejects_adjacent_gap_infeasible(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["mev_reject_dispute_e8"] = envelope["dispute_reward_e8"] - 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "dispute_game_infeasible_adjacent_gap" in result["errors"]


def test_dispute_game_rejects_boundary_bond_equals_honest_gain(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["dispute_bond_e8"] = envelope["dispute_reward_e8"]
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert result["honest_challenge_profit_e8"] == 0
    assert "honest_challenge_not_profitable" in result["errors"]


def test_dispute_game_rejects_boolean_amount(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["dispute_bond_e8"] = True
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert any("dispute_bond_e8_must_be_int" in e for e in result["errors"])


def test_dispute_game_rejects_negative_amount(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["dispute_reward_e8"] = -1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert any("dispute_reward_e8_must_be_int" in e for e in result["errors"])


def test_dispute_game_rejects_malformed_json(tmp_path: Path) -> None:
    path = tmp_path / "malformed.json"
    path.write_text("{not valid json", encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_dispute_game.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"
    assert any("dispute_game_load_failed" in e for e in result["errors"])


def test_dispute_game_rejects_root_list(tmp_path: Path) -> None:
    path = tmp_path / "root-list.json"
    path.write_text("[1, 2, 3]", encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_dispute_game.py", "verify", str(path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 3
    result = json.loads(proc.stdout)
    assert result["status"] == "inconclusive"


def test_dispute_game_rejects_equal_probabilities_frivolous_not_deterred(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["prob_upheld_when_wrong_bps"] = 8000
    envelope["prob_upheld_when_correct_bps"] = 8000
    envelope["dispute_bond_e8"] = 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "frivolous_dispute_not_deterred" in result["errors"]
    assert result["profit_feasible"] is False


def test_dispute_game_bps_rounding_boundary(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["prob_upheld_when_wrong_bps"] = 9999
    envelope["prob_upheld_when_correct_bps"] = 0
    envelope["dispute_reward_e8"] = 10_000_000
    envelope["mev_uphold_dispute_e8"] = 0
    envelope["dispute_bond_e8"] = 9_999_000
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "honest_challenge_not_profitable" in result["errors"]
    assert result["profit_feasible"] is False


def test_dispute_game_verify_with_output_flag(tmp_path: Path) -> None:
    envelope = sample_envelope()
    input_path = tmp_path / "envelope.json"
    output_path = tmp_path / "result.json"
    input_path.write_text(json.dumps(envelope, indent=2, sort_keys=True), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, "tools/zenodex_oracle_dispute_game.py", "verify", str(input_path), "--output", str(output_path)],
        cwd=REPO,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr
    assert proc.stdout == ""
    result = json.loads(output_path.read_text(encoding="utf-8"))
    assert result["status"] == "accepted"


def test_dispute_game_rejects_bps_above_max(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["prob_upheld_when_wrong_bps"] = 10_001
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert any("prob_upheld_when_wrong_bps_must_be_int" in e for e in result["errors"])


def test_dispute_game_rejects_missing_required_field(tmp_path: Path) -> None:
    envelope = sample_envelope()
    del envelope["dispute_bond_e8"]
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert any("dispute_bond_e8_must_be_int" in e for e in result["errors"])


def test_dispute_game_rejects_invalid_hash(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["query_id"] = "not-a-hash"
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "query_id_must_be_sha256" in result["errors"]


def test_dispute_game_rejects_invalid_token(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["consumer_module"] = "Invalid Module!"
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "consumer_module_must_be_token" in result["errors"]


def test_dispute_game_rejects_max_amount_exceeded(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["dispute_bond_e8"] = 10**30 + 1
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert any("dispute_bond_e8_must_be_int" in e for e in result["errors"])


def test_dispute_game_rejects_p_f_at_max(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["prob_upheld_when_correct_bps"] = 10_000
    code, result = _run_verify(tmp_path, envelope)
    assert code == 2
    assert "frivolous_dispute_not_deterred" in result["errors"]


def test_dispute_game_accepts_non_deterministic_probabilistic(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["prob_upheld_when_wrong_bps"] = 8000
    envelope["prob_upheld_when_correct_bps"] = 1000
    envelope["dispute_bond_e8"] = 11_000_000
    envelope["dispute_reward_e8"] = 15_000_000
    envelope["mev_uphold_dispute_e8"] = 0
    envelope["mev_reject_dispute_e8"] = 0
    code, result = _run_verify(tmp_path, envelope)
    assert code == 0
    assert result["profit_feasible"] is True


def test_dispute_game_slash_equals_required_deterrence(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["slash_fraction_bps"] = 6_000
    code, result = _run_verify(tmp_path, envelope)
    assert code == 0
    assert result["status"] == "accepted"


def test_dispute_game_profit_summary_rounds_to_zero_but_feasible(tmp_path: Path) -> None:
    envelope = sample_envelope()
    envelope["prob_upheld_when_wrong_bps"] = 9_999
    envelope["prob_upheld_when_correct_bps"] = 0
    envelope["dispute_reward_e8"] = 10_001
    envelope["mev_uphold_dispute_e8"] = 0
    envelope["mev_reject_dispute_e8"] = 0
    envelope["dispute_bond_e8"] = 9_999
    code, result = _run_verify(tmp_path, envelope)
    assert code == 0
    assert result["profit_feasible"] is True
    assert result["honest_challenge_profit_e8"] == 0


def test_direct_verify_accepts_sample() -> None:
    result = verify_dispute_game_envelope(sample_envelope())
    assert result.status == "accepted"
    assert result.errors == []
    assert result.profit_feasible is True


def test_direct_verify_rejects_zero_bond() -> None:
    envelope = sample_envelope()
    envelope["dispute_bond_e8"] = 0
    result = verify_dispute_game_envelope(envelope)
    assert result.status == "rejected"
    assert "dispute_bond_must_be_positive" in result.errors


def test_direct_verify_rejects_prob_inversion() -> None:
    envelope = sample_envelope()
    envelope["prob_upheld_when_wrong_bps"] = 0
    envelope["prob_upheld_when_correct_bps"] = 10_000
    result = verify_dispute_game_envelope(envelope)
    assert result.status == "rejected"
    assert "prob_upheld_when_wrong_below_prob_upheld_when_correct" in result.errors


def test_direct_verify_profit_feasible_with_other_errors() -> None:
    envelope = sample_envelope()
    envelope["dispute_reward_e8"] = envelope["dispute_budget_e8"] + 1
    result = verify_dispute_game_envelope(envelope)
    assert result.status == "rejected"
    assert "dispute_reward_budget_exceeded" in result.errors
    assert result.profit_feasible is True
