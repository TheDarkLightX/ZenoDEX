from __future__ import annotations

import json
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_zeno_oracle_math_witness_sweep_accepts_expected_cases() -> None:
    result = subprocess.run(
        ["julia", "tools/zeno_oracle_math_witness_sweep.jl", "--json"],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
    receipt = json.loads(result.stdout)
    assert receipt["schema"] == "zenodex.oracle.math_witness_sweep.v1"
    assert receipt["status"] == "accepted"
    assert receipt["case_count"] == 43
    assert receipt["failed_count"] == 0
    case_ids = {case["id"] for case in receipt["cases"]}
    assert "live_economics_escrow_floor_matches_replay" in case_ids
    assert "live_economics_escrow_shortfall_rejects" in case_ids
    assert "live_economics_governance_timelock_accepts" in case_ids
    assert "live_economics_governance_early_execution_rejects" in case_ids
    assert "live_economics_receipt_chain_order_accepts" in case_ids
    assert "live_economics_receipt_chain_order_inversion_rejects" in case_ids
    assert "live_economics_receipt_dependency_chain_accepts" in case_ids
    assert "live_economics_receipt_dependency_chain_drift_rejects" in case_ids
    assert "production_network_receipt_chain_order_accepts" in case_ids
    assert "production_network_receipt_chain_order_inversion_rejects" in case_ids
    assert "live_economics_settlement_execution_totals_match_replay" in case_ids
    assert "live_economics_settlement_execution_total_drift_rejects" in case_ids
    assert "live_economics_settlement_execution_components_bounded_by_total" in case_ids
    assert "live_economics_settlement_execution_budget_caps_components" in case_ids
    assert "live_economics_settlement_execution_budget_widening_preserves_component_caps" in case_ids
    assert "live_economics_settlement_execution_receipt_accepts_bound_obligations" in case_ids
    assert "live_economics_settlement_execution_receipt_rejects_asset_or_contract_drift" in case_ids
    assert "live_economics_settlement_execution_receipt_rejects_missing_totals_binding" in case_ids
    assert "median_deviation_small_grid_decomposes_to_side_obligations" in case_ids
    assert "median_deviation_acceptance_monotone_in_bound" in case_ids
    assert "o5_oracle_use_rejects_proof_window_kind_or_root_drift" in case_ids
    assert "o3_action_binding_accepts_dag_runtime_sync" in case_ids
    assert "terminal_dag_duplicate_receipt_rejects" in case_ids
    assert "o3_action_binding_missing_value_binding_rejects" in case_ids
    assert "o3_action_binding_wrong_consumer_action_rejects" in case_ids
    assert "oracle_sync_window_epoch_lag_rejects" in case_ids
    assert "o3_action_binding_sync_window_widening_preserves_acceptance" in case_ids
    assert "oracle_sync_window_composition_preserves_bound" in case_ids
    assert "o3_action_binding_sync_window_composition_preserves_binding" in case_ids


def test_zenoproof_julia_replay_profile_minimum_tracks_witness_sweep() -> None:
    import tools.zenoproof_verify as zenoproof_verify

    assert zenoproof_verify.MIN_JULIA_MATH_WITNESS_CASE_COUNT == 43
