from __future__ import annotations

import copy
import json
import subprocess
import sys
from pathlib import Path

from tools.check_upba_v2_grid_policy import check_policy, policy_content_hash, sample_policy


ROOT = Path(__file__).resolve().parents[2]


def _with_fresh_id(policy: dict[str, object]) -> dict[str, object]:
    policy = copy.deepcopy(policy)
    policy["policy_id"] = policy_content_hash(policy)
    return policy


def test_upba_v2_grid_policy_accepts_sample_candidate() -> None:
    result = check_policy(sample_policy())

    assert result["schema"] == "zenodex.upba.v2.grid_economic_sufficiency_check.v1"
    assert result["status"] == "accepted"
    assert result["error_count"] == 0
    assert result["derived"]["absolute_loss_bound_atoms"] == 704
    assert result["derived"]["relative_loss_ppm"] == 234_667
    assert result["derived"]["raw_price_grid_row_count"] == 441
    assert result["derived"]["computed_fill_levels_per_intent"] == 5
    assert result["derived"]["fill_vector_count"] == 625
    assert result["derived"]["candidate_evaluation_count"] == 275_625
    assert result["derived"]["min_fee_adjusted_notional_output_atoms"] == 3_190


def test_upba_v2_grid_policy_rejects_unknown_field_and_policy_id_drift() -> None:
    policy = sample_policy()
    policy["surprise"] = True

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "unknown_policy_field:surprise" in result["errors"]
    assert "policy_id_mismatch" in result["errors"]


def test_upba_v2_grid_policy_rejects_v1_policy_id() -> None:
    policy = sample_policy()
    policy["upba_policy_id"] = "zenodex/upba_v1/fixed_admission_full_fill_cpmm_exact_in"
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "unsupported_upba_policy_id" in result["errors"]


def test_upba_v2_grid_policy_rejects_fill_level_cap_drift() -> None:
    policy = sample_policy()
    policy["max_fill_levels_per_intent"] = 4
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "max_fill_levels_per_intent_mismatch" in result["errors"]


def test_upba_v2_grid_policy_rejects_fill_vector_cap_too_small() -> None:
    policy = sample_policy()
    policy["max_fill_vectors"] = 624
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "fill_vector_count_exceeds_policy" in result["errors"]


def test_upba_v2_grid_policy_rejects_candidate_evaluation_cap_too_small() -> None:
    policy = sample_policy()
    policy["max_candidate_evaluations"] = 275_624
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "candidate_evaluation_count_exceeds_policy" in result["errors"]


def test_upba_v2_grid_policy_rejects_total_executed_input_above_active_intent_cap() -> None:
    policy = sample_policy()
    policy["max_total_executed_input_atoms"] = 4_001
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "max_total_executed_input_atoms_exceeds_active_intent_cap" in result["errors"]


def test_upba_v2_grid_policy_rejects_trade_size_above_reserve_fraction() -> None:
    policy = sample_policy()
    policy["max_total_executed_input_atoms"] = 6_000
    policy["max_absolute_loss_atoms"] = 1_050
    policy["max_relative_loss_ppm"] = 400_000
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "max_trade_fraction_bps_exceeded" in result["errors"]


def test_upba_v2_grid_policy_rejects_absolute_and_relative_loss_budget_breach() -> None:
    policy = sample_policy()
    policy["max_absolute_loss_atoms"] = 703
    policy["max_relative_loss_ppm"] = 234_000
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "absolute_loss_bound_exceeds_policy" in result["errors"]
    assert "relative_loss_bound_exceeds_policy" in result["errors"]


def test_upba_v2_grid_policy_rejects_min_notional_above_fee_adjusted_floor() -> None:
    policy = sample_policy()
    policy["min_notional_output_atoms"] = 3_191
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "min_notional_output_atoms_above_conservative_fee_adjusted_floor" in result["errors"]


def test_upba_v2_grid_policy_rejects_grid_that_does_not_cover_price_interval() -> None:
    policy = sample_policy()
    policy["grid_max_price_num"] = 19
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "grid_max_price_num_does_not_cover_economic_max_price" in result["errors"]


def test_upba_v2_grid_policy_rejects_grid_that_does_not_cover_fixed_denominator_ladder() -> None:
    policy = sample_policy()
    policy["grid_max_price_den"] = 19
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "grid_max_price_den_does_not_cover_economic_price_scale" in result["errors"]


def test_upba_v2_grid_policy_rejects_missing_non_claim_boundary() -> None:
    policy = sample_policy()
    not_claimed = policy["not_claimed"]
    assert isinstance(not_claimed, list)
    not_claimed.remove("does_not_claim_multi_hop_or_exact_out")
    policy = _with_fresh_id(policy)

    result = check_policy(policy)

    assert result["status"] == "rejected"
    assert "missing_not_claim:does_not_claim_multi_hop_or_exact_out" in result["errors"]


def test_upba_v2_grid_policy_cli_sample_and_verify(tmp_path: Path) -> None:
    policy_path = tmp_path / "upba-v2-grid-policy.json"

    subprocess.run(
        [
            sys.executable,
            "tools/check_upba_v2_grid_policy.py",
            "sample",
            "--output",
            str(policy_path),
        ],
        cwd=ROOT,
        check=True,
    )

    proc = subprocess.run(
        [
            sys.executable,
            "tools/check_upba_v2_grid_policy.py",
            "verify",
            str(policy_path),
            "--format",
            "json",
        ],
        cwd=ROOT,
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    )
    report = json.loads(proc.stdout)

    assert report["status"] == "accepted"
