from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest

from src.integration.autonomous_governance_q_policy import (
    evaluate_autonomous_governance_surface_q_policy_v1,
    policy_content_hash_v1,
)
from tools.autonomous_governance_policy_factory import (
    _build_training_corpus,
    _write_json,
    build_policy_artifact_check_report,
)
from tools.support.autonomous_governance_policy_samples import (
    sample_autonomous_governance_surface_q_policy_v1,
)


def _surface_state() -> dict[str, int]:
    return {
        "fee_bps": 30,
        "buyburn_bps": 6_000,
        "stakers_bps": 0,
        "reserve_bps": 2_000,
        "hosts_bps": 2_000,
        "mcr_bps": 11_000,
        "ccr_bps": 15_000,
        "staker_bps": 5_000,
        "funding_cap_bps": 120,
    }


def _observation() -> dict[str, int]:
    return {
        "observed_price_bps": 10_500,
        "target_price_bps": 10_000,
        "volatility_bps": 250,
        "divergence_bps": 10,
        "freshness_lag_epochs": 0,
        "liquidity_depth_bps": 5_000,
    }


@pytest.mark.skipif(shutil.which("julia") is None, reason="Julia is not installed")
def test_julia_optimizer_generates_evaluable_governance_surface_policy(tmp_path: Path) -> None:
    policy_path = tmp_path / "policy.json"
    report_path = tmp_path / "report.json"

    proc = subprocess.run(
        [
            "julia",
            "tools/autonomous_governance_q_table_optimize.jl",
            "--policy-output",
            str(policy_path),
            "--report-output",
            str(report_path),
            "--quiet",
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr

    policy = json.loads(policy_path.read_text(encoding="utf-8"))
    report = json.loads(report_path.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["state_count"] == 48
    assert report["policy"]["policy_id"] == policy["policy_id"]
    assert report["best_actions"]["3|2|2"] == "raise_fee_10_tighten_funding_5"

    policy["policy_hash"] = policy_content_hash_v1(policy)
    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(),
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        last_update_epoch=32,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["approved"] is True
    assert result["action_id"] == "raise_fee_10_tighten_funding_5"
    assert result["governance_surface_all_gates_ok"] is True


def test_policy_artifact_checker_rejects_embedded_policy_hash_mismatch(tmp_path: Path) -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()
    policy_path = tmp_path / "policy.frozen.json"
    corpus_path = tmp_path / "ebr_training_corpus.json"
    optimizer_report_path = tmp_path / "optimizer_report.json"
    factory_report_path = tmp_path / "policy_factory_report.json"

    _write_json(policy_path, policy)
    _write_json(corpus_path, _build_training_corpus(policy))
    _write_json(
        optimizer_report_path,
        {
            "schema": "zenodex.autonomous_governance.q_table_optimizer_report.v1",
            "ok": True,
            "state_count": 48,
            "action_count": len(policy["actions"]),
        },
    )

    seed_report = build_policy_artifact_check_report(
        policy_path=policy_path,
        training_corpus_path=corpus_path,
        optimizer_report_path=optimizer_report_path,
    )
    _write_json(
        factory_report_path,
        {
            "schema": "zenodex.autonomous_governance.policy_factory_report.v1",
            "ok": True,
            "policy": {
                "policy_hash": policy["policy_hash"],
                "policy_id": policy["policy_id"],
                "schema": policy["schema"],
            },
            "replay": seed_report["replay"],
            "coverage_profile": seed_report["coverage_profile"],
            "training_corpus_summary": seed_report["training_corpus_summary"],
            "promotion_gate": seed_report["promotion_gate"],
            "source_manifest": seed_report["source_manifest"],
        },
    )

    report = build_policy_artifact_check_report(
        policy_path=policy_path,
        training_corpus_path=corpus_path,
        optimizer_report_path=optimizer_report_path,
        factory_report_path=factory_report_path,
    )
    assert report["artifact_gate"]["ok"] is True
    assert report["artifact_gate"]["checks"]["policy_hash_matches_content"] is True
    assert report["artifact_gate"]["checks"]["factory_report_policy_hash_matches"] is True
    assert report["artifact_gate"]["checks"]["factory_report_policy_hash_matches_embedded"] is True
    assert report["artifact_gate"]["checks"]["factory_report_source_manifest_matches_current"] is True
    assert report["artifact_gate"]["checks"]["factory_report_replay_matches_recomputed"] is True
    assert report["artifact_gate"]["checks"]["factory_report_coverage_profile_matches_recomputed"] is True
    assert report["artifact_gate"]["checks"]["factory_report_training_summary_matches_recomputed"] is True
    assert report["artifact_gate"]["checks"]["factory_report_promotion_gate_matches_recomputed"] is True
    assert report["artifact_gate"]["checks"]["training_corpus_rows_match_recomputed"] is True

    tampered = dict(policy)
    tampered["policy_hash"] = "0x" + "11" * 32
    tampered_path = tmp_path / "policy.tampered.json"
    _write_json(tampered_path, tampered)

    tampered_report = build_policy_artifact_check_report(
        policy_path=tampered_path,
        training_corpus_path=corpus_path,
        optimizer_report_path=optimizer_report_path,
        factory_report_path=factory_report_path,
    )
    assert tampered_report["ok"] is False
    assert tampered_report["artifact_gate"]["ok"] is False
    assert tampered_report["artifact_gate"]["checks"]["policy_hash_matches_content"] is False
    assert tampered_report["artifact_gate"]["checks"]["factory_report_policy_hash_matches"] is True
    assert tampered_report["artifact_gate"]["checks"]["factory_report_policy_hash_matches_embedded"] is False
    assert tampered_report["artifact_gate"]["checks"]["factory_report_replay_matches_recomputed"] is True
    assert tampered_report["artifact_gate"]["checks"]["training_corpus_summary_matches_recomputed"] is True

    replay_drift = json.loads(factory_report_path.read_text(encoding="utf-8"))
    replay_drift["replay"]["optimized"]["utility_score_total"] += 1
    replay_drift_path = tmp_path / "policy_factory_report.replay_drift.json"
    _write_json(replay_drift_path, replay_drift)
    replay_drift_report = build_policy_artifact_check_report(
        policy_path=policy_path,
        training_corpus_path=corpus_path,
        optimizer_report_path=optimizer_report_path,
        factory_report_path=replay_drift_path,
    )
    assert replay_drift_report["ok"] is False
    assert replay_drift_report["artifact_gate"]["ok"] is False
    assert replay_drift_report["artifact_gate"]["checks"]["factory_report_replay_matches_recomputed"] is False
    assert replay_drift_report["artifact_gate"]["checks"]["factory_report_source_manifest_matches_current"] is True

    promotion_drift = json.loads(factory_report_path.read_text(encoding="utf-8"))
    promotion_drift["promotion_gate"]["checks"]["optimizer_ok"] = False
    promotion_drift_path = tmp_path / "policy_factory_report.promotion_drift.json"
    _write_json(promotion_drift_path, promotion_drift)
    promotion_drift_report = build_policy_artifact_check_report(
        policy_path=policy_path,
        training_corpus_path=corpus_path,
        optimizer_report_path=optimizer_report_path,
        factory_report_path=promotion_drift_path,
    )
    assert promotion_drift_report["ok"] is False
    assert promotion_drift_report["artifact_gate"]["ok"] is False
    assert (
        promotion_drift_report["artifact_gate"]["checks"]["factory_report_promotion_gate_matches_recomputed"]
        is False
    )
    assert (
        promotion_drift_report["factory_report_artifact"]["provided_promotion_gate_sha256"]
        != promotion_drift_report["factory_report_artifact"]["recomputed_promotion_gate_sha256"]
    )

    source_drift = json.loads(factory_report_path.read_text(encoding="utf-8"))
    source_drift["source_manifest"][0]["sha256"] = "0x" + "00" * 32
    source_drift_path = tmp_path / "policy_factory_report.source_drift.json"
    _write_json(source_drift_path, source_drift)
    source_drift_report = build_policy_artifact_check_report(
        policy_path=policy_path,
        training_corpus_path=corpus_path,
        optimizer_report_path=optimizer_report_path,
        factory_report_path=source_drift_path,
    )
    assert source_drift_report["ok"] is False
    assert source_drift_report["artifact_gate"]["ok"] is False
    assert source_drift_report["artifact_gate"]["checks"]["factory_report_source_manifest_matches_current"] is False
    assert source_drift_report["artifact_gate"]["checks"]["factory_report_replay_matches_recomputed"] is True
    assert (
        source_drift_report["source_manifest_artifact"]["provided_sha256"]
        != source_drift_report["source_manifest_artifact"]["recomputed_sha256"]
    )


@pytest.mark.skipif(shutil.which("julia") is None, reason="Julia is not installed")
def test_policy_factory_generates_frozen_policy_and_replay_report(tmp_path: Path) -> None:
    out_dir = tmp_path / "factory"

    proc = subprocess.run(
        [
            "python3",
            "tools/autonomous_governance_policy_factory.py",
            "--out-dir",
            str(out_dir),
            "--quiet",
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout

    frozen_policy = json.loads((out_dir / "optimized_policy.frozen.json").read_text(encoding="utf-8"))
    report = json.loads((out_dir / "policy_factory_report.json").read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert frozen_policy["policy_hash"] == report["policy"]["policy_hash"]
    assert frozen_policy["selection"] == {
        "anti_oscillation": {
            "enabled": True,
            "parameters": ["fee_bps", "funding_cap_bps"],
        },
        "mode": "first_admissible",
        "trajectory_budget": {
            "enabled": True,
            "limits": {
                "buyburn_bps": 1000,
                "ccr_bps": 2000,
                "fee_bps": 250,
                "funding_cap_bps": 125,
                "hosts_bps": 1000,
                "mcr_bps": 2000,
                "reserve_bps": 1000,
                "staker_bps": 1000,
                "stakers_bps": 1000,
            },
        },
    }
    assert frozen_policy["state_bins"]["fee_bps"] == [9, 50, 990]
    assert frozen_policy["state_bins"]["funding_cap_bps"] == [10, 190]
    assert frozen_policy["state_bins"]["buyburn_bps"] == [0, 9000, 9900]
    assert frozen_policy["state_bins"]["reserve_bps"] == [0, 9000, 9900]
    assert {layer["id"] for layer in frozen_policy["q_layers"]} >= {
        "fee_edge_bias",
        "funding_edge_bias",
        "buyburn_edge_bias",
        "reserve_edge_bias",
        "reserve_cap_liquidity_recovery_bias",
        "reserve_cap_liquidity_floor_bias",
        "fee_reserve_cap_liquidity_floor_fallback",
        "funding_floor_liquidity_floor_fallback",
        "trained_ebr_residual_train_split_v1",
    }
    residual_layer = next(
        layer for layer in frozen_policy["q_layers"] if layer["id"] == "trained_ebr_residual_train_split_v1"
    )
    assert residual_layer["features"] == [
        "deviation_bps",
        "volatility_bps",
        "liquidity_depth_bps",
        "fee_bps",
        "funding_cap_bps",
        "buyburn_bps",
        "reserve_bps",
    ]
    assert len(residual_layer["q_table"]) == 253
    assert residual_layer["q_table"]["*"] == {
        "hold": 0,
        "lower_fee_10": 0,
        "lower_fee_10_relax_funding_5": 0,
        "lower_fee_10_relax_funding_5_shift_router_to_reserve_100": 0,
        "raise_fee_10": 0,
        "raise_fee_10_shift_router_to_reserve_100": 0,
        "raise_fee_10_tighten_funding_5": 0,
        "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100": 0,
        "shift_router_to_buyburn_100": 0,
        "shift_router_to_reserve_100": 0,
    }
    assert report["promotion_gate"]["checks"] == {
        "action_gate_diagnostics_ok": True,
        "all_bins_covered": True,
        "coverage_profile_ok": True,
        "environment_curriculum_diagnostics_ok": True,
        "inconsistent_accept_count_zero": True,
        "invalid_accept_count_zero": True,
        "intra_bin_stress_bins_complete": True,
        "intra_bin_stress_frontier_regret_zero": True,
        "intra_bin_stress_frontier_utility_complete": True,
        "intra_bin_stress_inconsistent_accept_count_zero": True,
        "intra_bin_stress_invalid_accept_count_zero": True,
        "intra_bin_stress_nonempty": True,
        "intra_bin_stress_observed_bins_match_expected": True,
        "intra_bin_stress_ok": True,
        "intra_bin_stress_profiles_complete": True,
        "intra_bin_stress_safety_feasible_opportunities_complete": True,
        "long_horizon_cumulative_drift_within_limits": True,
        "long_horizon_final_states_safe": True,
        "long_horizon_frontier_regret_zero": True,
        "long_horizon_frontier_utility_complete": True,
        "long_horizon_hold_only_invalid_accept_count_zero": True,
        "long_horizon_ids_complete": True,
        "long_horizon_inconsistent_accept_count_zero": True,
        "long_horizon_invalid_accept_count_zero": True,
        "long_horizon_nonempty": True,
        "long_horizon_pid_like_invalid_accept_count_zero": True,
        "long_horizon_safety_feasible_count_positive": True,
        "long_horizon_safety_feasible_opportunities_complete": True,
        "long_horizon_trajectory_budget_within_limits": True,
        "long_horizon_utility_beats_hold_only": True,
        "long_horizon_utility_not_worse_than_pid_like": True,
        "negative_controls_expected_errors_present": True,
        "negative_controls_invalid_accept_count_zero": True,
        "negative_controls_reject_all": True,
        "optimized_frontier_regret_zero": True,
        "optimized_frontier_utility_complete": True,
        "optimized_safety_feasible_count_positive": True,
        "optimized_safety_feasible_opportunities_complete": True,
        "optimizer_ok": True,
        "policy_hash_present": True,
        "safety_boundary_expected_errors_present": True,
        "safety_boundary_inside_cases_approve": True,
        "safety_boundary_invalid_accept_count_zero": True,
        "safety_boundary_outside_cases_reject": True,
        "safety_boundary_sweep_ok": True,
        "safety_interaction_expected_errors_present": True,
        "safety_interaction_inside_cases_approve": True,
        "safety_interaction_invalid_accept_count_zero": True,
        "safety_interaction_outside_cases_reject": True,
        "safety_interaction_sweep_ok": True,
        "safety_lanes_expected_errors_present": True,
        "safety_lanes_reject_all": True,
        "source_manifest_complete": True,
        "stress_grid_nonempty": True,
        "surface_boundary_expected_rejections_present": True,
        "surface_boundary_invalid_accept_count_zero": True,
        "surface_boundary_profiles_complete": True,
        "surface_boundary_selected_cases_approve": True,
        "surface_boundary_selected_q_rows_complete": True,
        "surface_boundary_sweep_ok": True,
        "training_corpus_ok": True,
        "training_diversity_diagnostics_ok": True,
        "training_entropy_diagnostics_ok": True,
        "training_feature_contract_ok": True,
        "training_pairwise_diagnostics_ok": True,
        "training_ranking_diagnostics_ok": True,
        "training_sequence_ranking_diagnostics_ok": True,
        "training_split_diagnostics_ok": True,
        "training_supervision_targets_ok": True,
        "utility_beats_hold_only": True,
        "utility_not_worse_than_pid_like": True,
    }
    assert report["replay"]["action_gate_diagnostics"]["ok"] is True
    assert report["replay"]["action_gate_diagnostics"]["action_count"] == 10
    assert report["replay"]["action_gate_diagnostics"]["failing_actions"] == []
    assert report["replay"]["action_gate_diagnostics"]["checks"] == {
        "action_map_complete": True,
        "all_actions_gate_admissible": True,
        "base_state_safe": True,
        "policy_actions_present": True,
    }
    assert [
        action["action_id"]
        for action in report["replay"]["action_gate_diagnostics"]["actions"]
    ] == [
        "hold",
        "raise_fee_10",
        "lower_fee_10",
        "raise_fee_10_tighten_funding_5",
        "lower_fee_10_relax_funding_5",
        "shift_router_to_reserve_100",
        "shift_router_to_buyburn_100",
        "raise_fee_10_shift_router_to_reserve_100",
        "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100",
        "lower_fee_10_relax_funding_5_shift_router_to_reserve_100",
    ]
    assert all(
        action["accepted"] is True
        and action["gate_report"] == {
            "collateral": True,
            "fee": True,
            "funding": True,
            "master": True,
            "router": True,
            "whale": True,
        }
        for action in report["replay"]["action_gate_diagnostics"]["actions"]
    )
    environment = report["replay"]["environment_curriculum_diagnostics"]
    assert environment["ok"] is True
    assert environment["checks"] == {
        "all_sequences_multi_step": True,
        "cumulative_drift_within_limits": True,
        "final_states_safe": True,
        "frontier_regret_zero": True,
        "hold_steps_present": True,
        "no_inconsistent_accepts": True,
        "no_invalid_accepts": True,
        "noop_rejections_present": True,
        "router_budget_walk_spends_router_budget": True,
        "router_recovery_walk_spends_router_budget": True,
        "safety_interrupt_mixed_outcomes": True,
        "sequence_count_matches": True,
        "sequence_ids_complete": True,
        "state_transitions_present": True,
        "step_count_positive": True,
        "trajectory_budget_within_limits": True,
        "trajectory_safety_interrupt_mixed_outcomes": True,
        "unique_bin_paths_diverse": True,
    }
    assert environment["sequence_count"] == 10
    assert environment["step_count"] == 127
    assert environment["state_transition_count"] == 90
    assert environment["hold_step_count"] == 26
    assert environment["noop_rejection_count"] == 11
    assert environment["unique_bin_key_count"] == 4
    assert environment["missing_sequence_ids"] == []
    assert environment["observed_sequence_ids"] == [
        "alternating_pressure",
        "calm_fee_floor",
        "funding_floor_pressure",
        "persistent_high_deviation",
        "router_budget_walk",
        "router_edge_pressure",
        "router_recovery_walk",
        "safety_interrupt",
        "trajectory_budget_walk",
        "trajectory_safety_interrupt",
    ]
    assert environment["sequence_step_counts"] == {
        "alternating_pressure": 8,
        "calm_fee_floor": 6,
        "funding_floor_pressure": 6,
        "persistent_high_deviation": 8,
        "router_budget_walk": 14,
        "router_edge_pressure": 5,
        "router_recovery_walk": 14,
        "safety_interrupt": 4,
        "trajectory_budget_walk": 30,
        "trajectory_safety_interrupt": 32,
    }
    assert environment["sequence_outcomes"]["router_budget_walk"] == {
        "approved_count": 14,
        "rejected_count": 0,
        "safety_blocked_count": 0,
    }
    assert environment["sequence_trajectory_used"]["router_budget_walk"]["buyburn_bps"] == 1_000
    assert environment["sequence_trajectory_used"]["router_budget_walk"]["reserve_bps"] == 1_000
    assert environment["sequence_outcomes"]["router_recovery_walk"] == {
        "approved_count": 14,
        "rejected_count": 0,
        "safety_blocked_count": 0,
    }
    assert environment["sequence_trajectory_used"]["router_recovery_walk"]["buyburn_bps"] == 1_000
    assert environment["sequence_trajectory_used"]["router_recovery_walk"]["reserve_bps"] == 1_000
    assert environment["sequence_outcomes"]["router_edge_pressure"] == {
        "approved_count": 0,
        "rejected_count": 5,
        "safety_blocked_count": 5,
    }
    assert environment["sequence_outcomes"]["safety_interrupt"] == {
        "approved_count": 2,
        "rejected_count": 2,
        "safety_blocked_count": 2,
    }
    assert environment["sequence_outcomes"]["trajectory_budget_walk"] == {
        "approved_count": 30,
        "rejected_count": 0,
        "safety_blocked_count": 0,
    }
    assert environment["sequence_outcomes"]["trajectory_safety_interrupt"] == {
        "approved_count": 28,
        "rejected_count": 4,
        "safety_blocked_count": 4,
    }
    assert environment["unique_bin_keys"] == ["0|0|1", "0|0|2", "0|1|0", "3|2|2"]
    residual_model = json.loads((out_dir / "ebr_residual_model.json").read_text(encoding="utf-8"))
    assert report["artifacts"]["ebr_residual_model"] == str(out_dir / "ebr_residual_model.json")
    assert report["ebr_residual_model"] == residual_model
    assert residual_model["ok"] is True
    assert residual_model["applied_to_policy"] is True
    assert residual_model["candidate_policy_hash"] == frozen_policy["policy_hash"]
    assert residual_model["q_table_key_count"] == 253
    assert residual_model["q_table_learned_key_count"] == 252
    assert residual_model["q_table_materialized_key_count"] == 253
    assert residual_model["q_table_effective_completed_key_count"] == 9216
    assert residual_model["q_table_neutral_fill_key_count"] == 8964
    assert residual_model["q_table_entry_count"] == 2530
    assert residual_model["q_table_sha256"] == (
        "0x2e81113a1fab9a6251e92dc490a1662cf976ac246cb7d5c085102b6e80b24805"
    )
    assert residual_model["training_config"]["score_clamp"] == 320
    assert residual_model["training_config"]["score_scale"] == 2
    assert residual_model["q_table_completion"]["ok"] is True
    assert residual_model["q_table_completion"]["fallback_key"] == "*"
    assert residual_model["q_table_completion"]["expected_key_count"] == 9216
    assert residual_model["q_table_completion"]["effective_completed_key_count"] == 9216
    assert residual_model["q_table_completion"]["effective_completed_entry_count"] == 92160
    assert residual_model["q_table_completion"]["materialized_key_count"] == 253
    assert residual_model["q_table_completion"]["materialized_entry_count"] == 2530
    assert residual_model["q_table_completion"]["missing_action_fill_count"] == 0
    assert residual_model["q_table_completion"]["neutral_edge_prior_enabled"] is True
    assert residual_model["q_table_completion"]["neutral_edge_prior_penalty"] == 320
    assert residual_model["q_table_completion"]["neutral_edge_prior_key_count"] == 3
    assert residual_model["q_table_completion"]["neutral_edge_prior_adjustment_count"] == 12
    assert residual_model["checks"] == {
        "cross_seed_diagnostics_ok": True,
        "q_table_complete": True,
        "q_table_nonempty": True,
        "train_hybrid_frontier_rank1_complete": True,
        "training_rows_present": True,
        "validation_hybrid_calls_not_worse_than_policy": True,
        "validation_hybrid_frontier_rank1_complete": True,
        "validation_hybrid_hard_negative_accuracy_not_worse_than_policy": True,
        "validation_hybrid_hard_negative_margin_positive": True,
        "validation_hybrid_hard_negative_min_not_worse_than_policy": True,
        "validation_hybrid_nonfrontier_p50_improves_policy": True,
    }
    assert residual_model["cross_seed_diagnostics"]["ok"] is True
    assert residual_model["cross_seed_diagnostics"]["seed_count"] == 7
    assert residual_model["cross_seed_diagnostics"]["failing_salts"] == []
    assert residual_model["cross_seed_diagnostics"]["min_validation_group_count"] == 191
    assert residual_model["cross_seed_diagnostics"]["min_validation_accepting_group_count"] == 156
    assert residual_model["cross_seed_diagnostics"]["min_nonfrontier_p50_lift"] == 634
    assert residual_model["cross_seed_diagnostics"]["min_hard_negative_p50_lift"] == 975
    assert residual_model["cross_seed_diagnostics"]["min_hard_negative_min_lift"] == 15
    assert residual_model["cross_seed_diagnostics"]["checks"] == {
        "all_seed_checks_pass": True,
        "hard_negative_margin_positive_all_seeds": True,
        "hard_negative_p50_lift_positive_all_seeds": True,
        "nonfrontier_p50_lift_positive_all_seeds": True,
        "seed_count_matches": True,
        "validation_accepting_groups_present_all_seeds": True,
        "validation_groups_present_all_seeds": True,
    }
    assert [seed["salt"] for seed in residual_model["cross_seed_diagnostics"]["seeds"]] == [
        "seed0",
        "seed1",
        "seed2",
        "seed3",
        "seed4",
        "seed5",
        "seed6",
    ]
    assert min(
        seed["hybrid"]["hard_negative_margin_summary"]["min"]
        for seed in residual_model["cross_seed_diagnostics"]["seeds"]
    ) == 300
    assert residual_model["metrics"]["validation"]["policy"]["mean_calls_to_frontier"] == 1.0
    assert residual_model["metrics"]["validation"]["hybrid"]["mean_calls_to_frontier"] == 1.0
    assert residual_model["metrics"]["validation"]["policy"]["all_nonfrontier_margin_summary"]["p50"] == 300
    assert residual_model["metrics"]["validation"]["residual"]["pairwise_accuracy"] == 0.988898
    assert residual_model["metrics"]["validation"]["residual"]["hard_negative_accuracy"] == 1.0
    assert residual_model["metrics"]["validation"]["residual"]["all_nonfrontier_margin_summary"]["p50"] == 686
    assert residual_model["metrics"]["validation"]["residual"]["hard_negative_margin_summary"]["min"] == 320
    assert residual_model["metrics"]["validation"]["residual"]["hard_negative_margin_summary"]["p50"] == 1280
    assert residual_model["metrics"]["validation"]["residual"]["rank1_frontier_count"] == 159
    assert residual_model["metrics"]["validation"]["hybrid"]["all_nonfrontier_margin_summary"]["p50"] == 948
    assert residual_model["metrics"]["validation"]["policy"]["hard_negative_margin_summary"]["min"] == 285
    assert residual_model["metrics"]["validation"]["hybrid"]["hard_negative_margin_summary"]["min"] == 605
    assert residual_model["metrics"]["validation"]["hybrid"]["hard_negative_margin_summary"]["p50"] == 2110
    assert residual_model["metrics"]["validation"]["policy"]["selection_blocked_margin_summary"]["min"] == 215
    assert residual_model["metrics"]["validation"]["hybrid"]["selection_blocked_margin_summary"]["min"] == 1026
    corpus = json.loads((out_dir / "ebr_training_corpus.json").read_text(encoding="utf-8"))
    assert report["artifacts"]["ebr_training_corpus"] == str(out_dir / "ebr_training_corpus.json")
    assert report["training_corpus_summary"] == corpus["summary"]
    assert corpus["summary"]["ok"] is True
    assert corpus["summary"]["row_count"] == 11002
    assert corpus["summary"]["expected_normal_grid_row_count"] == 2400
    assert corpus["summary"]["expected_intra_bin_stress_row_count"] == 4800
    assert corpus["summary"]["expected_intra_bin_stress_scenario_count"] == 480
    assert corpus["summary"]["expected_safety_boundary_sweep_row_count"] == 800
    assert corpus["summary"]["expected_safety_boundary_sweep_scenario_count"] == 80
    assert corpus["summary"]["expected_safety_interaction_sweep_row_count"] == 1600
    assert corpus["summary"]["expected_safety_interaction_sweep_scenario_count"] == 160
    assert corpus["summary"]["expected_surface_boundary_sweep_row_count"] == 120
    assert corpus["summary"]["expected_surface_boundary_sweep_scenario_count"] == 12
    assert corpus["summary"]["expected_sequence_step_row_count"] == 1270
    assert corpus["summary"]["expected_sequence_step_count"] == 127
    assert corpus["summary"]["sequence_actions_per_step"] == 10
    assert corpus["summary"]["sequence_selection_blocked_count"] == 318
    assert corpus["summary"]["policy_action_count"] == 10
    assert corpus["summary"]["invalid_accept_count"] == 0
    assert corpus["summary"]["checks"]["intra_bin_stress_row_count_matches"] is True
    assert corpus["summary"]["checks"]["safety_boundary_sweep_row_count_matches"] is True
    assert corpus["summary"]["checks"]["safety_interaction_sweep_row_count_matches"] is True
    assert corpus["summary"]["checks"]["surface_boundary_sweep_row_count_matches"] is True
    assert corpus["summary"]["checks"]["ranking_diagnostics_ok"] is True
    assert corpus["summary"]["checks"]["sequence_ranking_diagnostics_ok"] is True
    assert corpus["summary"]["checks"]["pairwise_diagnostics_ok"] is True
    assert corpus["summary"]["checks"]["supervision_targets_ok"] is True
    assert corpus["summary"]["checks"]["split_diagnostics_ok"] is True
    assert corpus["summary"]["checks"]["entropy_diagnostics_ok"] is True
    assert corpus["summary"]["checks"]["feature_contract_ok"] is True
    assert corpus["summary"]["checks"]["diversity_diagnostics_ok"] is True
    assert corpus["summary"]["feature_contract"]["ok"] is True
    assert corpus["summary"]["feature_contract"]["feature_count"] == 37
    assert corpus["summary"]["feature_contract"]["row_count"] == 11002
    assert corpus["summary"]["feature_contract"]["feature_vector_count"] == 11002
    assert corpus["summary"]["feature_contract"]["missing_vector_count"] == 0
    assert corpus["summary"]["feature_contract"]["wrong_length_count"] == 0
    assert corpus["summary"]["feature_contract"]["non_numeric_value_count"] == 0
    assert corpus["summary"]["feature_contract"]["leaked_feature_name_tokens"] == []
    assert corpus["summary"]["feature_contract"]["forbidden_source_intersection"] == []
    assert corpus["summary"]["feature_contract"]["private_context_removed_count"] == 33006
    assert corpus["summary"]["feature_contract"]["source_histogram"] == {
        "intra_bin_stress": 4800,
        "negative_control": 6,
        "normal_grid": 2400,
        "safety_boundary_sweep": 800,
        "safety_interaction_sweep": 1600,
        "safety_lane": 6,
        "sequence_step": 1270,
        "surface_boundary_sweep": 120,
    }
    diversity = corpus["summary"]["diversity_diagnostics"]
    assert diversity["ok"] is True
    assert diversity["checks"] == {
        "all_actions_present": True,
        "candidate_groups_complete": True,
        "duplicate_feature_vector_rate_bounded": True,
        "failure_families_diverse": True,
        "feature_vectors_present": True,
        "hard_negative_families_diverse": True,
        "intra_bin_vectors_unique_per_row": True,
        "no_single_vector_dominates": True,
        "normal_grid_vectors_unique_per_row": True,
        "required_target_classes_present": True,
        "rows_present": True,
        "safety_boundary_vectors_unique_per_row": True,
        "safety_interaction_vectors_unique_per_row": True,
        "sequence_vectors_diverse": True,
        "surface_boundary_vectors_unique_per_row": True,
        "target_classes_present_in_train": True,
        "target_classes_present_in_validation": True,
        "unique_feature_vector_ratio_high": True,
    }
    assert diversity["row_count"] == 11002
    assert diversity["unique_feature_vector_count"] == 11000
    assert diversity["unique_feature_vector_ppm"] == 999818
    assert diversity["duplicate_feature_vector_count"] == 2
    assert diversity["duplicate_feature_vector_ppm"] == 181
    assert diversity["max_duplicate_feature_vector_count"] == 3
    assert diversity["missing_feature_vector_count"] == 0
    assert diversity["candidate_group_count"] == 1099
    assert diversity["expected_candidate_group_count"] == 1099
    assert diversity["missing_target_classes"] == []
    assert diversity["split_missing_target_classes"] == {"train": [], "validation": []}
    assert diversity["hard_negative_failure_families"] == [
        "anti_oscillation:fee_bps",
        "governance_surface_gate_rejected:collateral",
        "governance_surface_gate_rejected:fee",
        "governance_surface_gate_rejected:funding",
        "governance_surface_gate_rejected:router",
        "governance_surface_gate_rejected:whale",
        "trajectory_budget_exceeded:buyburn_bps",
        "trajectory_budget_exceeded:fee_bps",
    ]
    assert diversity["source_unique_feature_vector_counts"] == {
        "intra_bin_stress": 4800,
        "negative_control": 6,
        "normal_grid": 2400,
        "safety_boundary_sweep": 800,
        "safety_interaction_sweep": 1600,
        "safety_lane": 4,
        "sequence_step": 1270,
        "surface_boundary_sweep": 120,
    }
    assert diversity["source_duplicate_feature_vector_counts"] == {
        "intra_bin_stress": 0,
        "negative_control": 0,
        "normal_grid": 0,
        "safety_boundary_sweep": 0,
        "safety_interaction_sweep": 0,
        "safety_lane": 2,
        "sequence_step": 0,
        "surface_boundary_sweep": 0,
    }
    assert diversity["target_class_histogram"] == {
        "admissible_dominated": 3828,
        "frontier": 2284,
        "gate_rejected": 2068,
        "negative_control": 6,
        "no_accept_rejected": 2492,
        "safety_lane": 6,
        "selection_blocked": 318,
    }
    assert corpus["summary"]["feature_contract"]["source_histogram_by_split"] == {
        "train": {
            "intra_bin_stress": 3970,
            "negative_control": 4,
            "normal_grid": 2000,
            "safety_boundary_sweep": 690,
            "safety_interaction_sweep": 1270,
            "safety_lane": 4,
            "sequence_step": 990,
            "surface_boundary_sweep": 110,
        },
        "validation": {
            "intra_bin_stress": 830,
            "negative_control": 2,
            "normal_grid": 400,
            "safety_boundary_sweep": 110,
            "safety_interaction_sweep": 330,
            "safety_lane": 2,
            "sequence_step": 280,
            "surface_boundary_sweep": 10,
        },
    }
    assert corpus["summary"]["feature_contract"]["checks"] == {
        "feature_names_nonempty": True,
        "feature_values_numeric": True,
        "feature_vector_lengths_fixed": True,
        "feature_vectors_present": True,
        "forbidden_feature_name_tokens_absent": True,
        "forbidden_source_fields_absent_from_feature_names": True,
        "private_feature_context_removed": True,
        "train_feature_rows_present": True,
        "validation_feature_rows_present": True,
    }
    assert corpus["summary"]["supervision_targets"]["ok"] is True
    assert corpus["summary"]["supervision_targets"]["candidate_group_count"] == 1099
    assert corpus["summary"]["supervision_targets"]["expected_candidate_group_count"] == 1099
    assert corpus["summary"]["supervision_targets"]["accepting_candidate_group_count"] == 848
    assert corpus["summary"]["supervision_targets"]["no_accept_candidate_group_count"] == 251
    assert corpus["summary"]["supervision_targets"]["frontier_row_count"] == 2284
    assert corpus["summary"]["supervision_targets"]["accepted_nonfrontier_count"] == 3828
    assert corpus["summary"]["supervision_targets"]["gate_rejected_target_count"] == 2068
    assert corpus["summary"]["supervision_targets"]["no_accept_target_count"] == 2492
    assert corpus["summary"]["supervision_targets"]["selection_blocked_target_count"] == 318
    assert corpus["summary"]["supervision_targets"]["negative_control_target_count"] == 6
    assert corpus["summary"]["supervision_targets"]["safety_lane_target_count"] == 6
    assert corpus["summary"]["supervision_targets"]["missing_target_field_count"] == 0
    assert corpus["summary"]["supervision_targets"]["negative_regret_count"] == 0
    assert corpus["summary"]["supervision_targets"]["negative_rank_gap_count"] == 0
    assert corpus["summary"]["supervision_targets"]["selection_blocked_negative_rank_gap_count"] == 48
    assert corpus["summary"]["supervision_targets"]["candidate_rows_missing_policy_rank"] == 0
    assert corpus["summary"]["supervision_targets"]["target_class_histogram"] == {
        "admissible_dominated": 3828,
        "frontier": 2284,
        "gate_rejected": 2068,
        "negative_control": 6,
        "no_accept_rejected": 2492,
        "safety_lane": 6,
        "selection_blocked": 318,
    }
    assert corpus["summary"]["supervision_targets"]["checks"] == {
        "accepted_nonfrontier_rows_present": True,
        "candidate_group_count_matches": True,
        "candidate_policy_ranks_present": True,
        "frontier_rows_present": True,
        "gate_rejected_targets_present": True,
        "negative_control_targets_present": True,
        "no_accept_targets_present": True,
        "rank_gap_nonnegative": True,
        "safety_lane_targets_present": True,
        "selection_blocked_targets_present": True,
        "target_fields_present": True,
        "utility_regret_nonnegative": True,
    }
    assert corpus["summary"]["split_diagnostics"]["ok"] is True
    assert corpus["summary"]["split_diagnostics"]["group_count"] == 1111
    assert corpus["summary"]["split_diagnostics"]["expected_group_count"] == 1111
    assert corpus["summary"]["split_diagnostics"]["candidate_group_count"] == 1099
    assert corpus["summary"]["split_diagnostics"]["expected_candidate_group_count"] == 1099
    assert corpus["summary"]["split_diagnostics"]["forced_validation_group_count"] == 0
    assert corpus["summary"]["split_diagnostics"]["group_split_leak_count"] == 0
    assert corpus["summary"]["split_diagnostics"]["missing_split_field_count"] == 0
    assert corpus["summary"]["split_diagnostics"]["row_count_by_split"] == {
        "train": 9038,
        "validation": 1964,
    }
    assert corpus["summary"]["split_diagnostics"]["group_count_by_split"] == {
        "train": 911,
        "validation": 200,
    }
    assert corpus["summary"]["split_diagnostics"]["source_group_count_by_split"] == {
        "train": {
            "intra_bin_stress": 397,
            "negative_control": 4,
            "normal_grid": 200,
            "safety_boundary_sweep": 69,
            "safety_interaction_sweep": 127,
            "safety_lane": 4,
            "sequence_step": 99,
            "surface_boundary_sweep": 11,
        },
        "validation": {
            "intra_bin_stress": 83,
            "negative_control": 2,
            "normal_grid": 40,
            "safety_boundary_sweep": 11,
            "safety_interaction_sweep": 33,
            "safety_lane": 2,
            "sequence_step": 28,
            "surface_boundary_sweep": 1,
        },
    }
    assert corpus["summary"]["split_diagnostics"]["target_class_histogram_by_split"] == {
        "train": {
            "admissible_dominated": 3074,
            "frontier": 1867,
            "gate_rejected": 1714,
            "negative_control": 4,
            "no_accept_rejected": 2128,
            "safety_lane": 4,
            "selection_blocked": 247,
        },
        "validation": {
            "admissible_dominated": 754,
            "frontier": 417,
            "gate_rejected": 354,
            "negative_control": 2,
            "no_accept_rejected": 364,
            "safety_lane": 2,
            "selection_blocked": 71,
        },
    }
    assert corpus["summary"]["split_diagnostics"]["validation"] == {
        "accepting_group_count": 159,
        "actual_calls_to_frontier_max": 1,
        "actual_calls_to_frontier_total": 159,
        "all_nonfrontier_margin_summary": {
            "count": 1173,
            "max": 3612,
            "min": -869,
            "p05": 242,
            "p50": 944,
            "p95": 2660,
        },
        "candidate_group_count": 196,
        "dominated_margin_summary": {
            "count": 754,
            "max": 1764,
            "min": 5,
            "p05": 190,
            "p50": 729,
            "p95": 1209,
        },
        "entropy_mass_total": 20.828951,
        "hard_negative_margin_summary": {
            "count": 354,
            "max": 3612,
            "min": 605,
            "p05": 1595,
            "p50": 2110,
            "p95": 2998,
        },
        "mean_actual_calls_to_frontier": 1.0,
        "mean_entropy_call_bound": 1.131,
        "mean_entropy_mass_per_accepting_group": 0.131,
        "negative_margin_count": 0,
        "no_accept_group_count": 37,
        "selection_blocked_entropy_mass_total": 16866.885438,
    }
    assert corpus["summary"]["split_diagnostics"]["train"]["candidate_group_count"] == 903
    assert corpus["summary"]["split_diagnostics"]["train"]["accepting_group_count"] == 689
    assert corpus["summary"]["split_diagnostics"]["train"]["no_accept_group_count"] == 214
    assert corpus["summary"]["split_diagnostics"]["train"]["actual_calls_to_frontier_max"] == 1
    assert corpus["summary"]["split_diagnostics"]["train"]["mean_entropy_call_bound"] == 1.099663
    assert corpus["summary"]["split_diagnostics"]["train"]["hard_negative_margin_summary"]["min"] == 1330
    assert (
        corpus["summary"]["split_diagnostics"]["train"]["selection_blocked_entropy_mass_total"]
        == 77982.167666
    )
    assert corpus["summary"]["split_diagnostics"]["checks"] == {
        "candidate_group_count_matches": True,
        "group_count_matches": True,
        "no_group_split_leakage": True,
        "split_fields_present": True,
        "train_entropy_bound_below_exhaustive": True,
        "train_frontier_calls_max_is_one": True,
        "train_hard_negative_margins_positive": True,
        "train_rows_present": True,
        "train_sources_complete": True,
        "train_target_classes_complete": True,
        "validation_accepting_groups_present": True,
        "validation_entropy_bound_below_exhaustive": True,
        "validation_frontier_calls_max_is_one": True,
        "validation_hard_negative_margins_positive": True,
        "validation_no_accept_groups_present": True,
        "validation_rows_present": True,
        "validation_sources_complete": True,
        "validation_target_classes_complete": True,
    }
    assert corpus["summary"]["entropy_diagnostics"]["ok"] is True
    assert corpus["summary"]["entropy_diagnostics"]["candidate_group_count"] == 1099
    assert corpus["summary"]["entropy_diagnostics"]["expected_candidate_group_count"] == 1099
    assert corpus["summary"]["entropy_diagnostics"]["accepting_group_count"] == 848
    assert corpus["summary"]["entropy_diagnostics"]["no_accept_group_count"] == 251
    assert corpus["summary"]["entropy_diagnostics"]["actual_calls_to_frontier_total"] == 848
    assert corpus["summary"]["entropy_diagnostics"]["actual_calls_to_frontier_max"] == 1
    assert corpus["summary"]["entropy_diagnostics"]["mean_actual_calls_to_frontier"] == 1.0
    assert corpus["summary"]["entropy_diagnostics"]["entropy_mass_total"] == 89.496835
    assert corpus["summary"]["entropy_diagnostics"]["selection_blocked_entropy_mass_total"] == 94849.053104
    assert corpus["summary"]["entropy_diagnostics"]["mean_entropy_mass_per_accepting_group"] == 0.105539
    assert corpus["summary"]["entropy_diagnostics"]["mean_entropy_call_bound"] == 1.105539
    assert corpus["summary"]["entropy_diagnostics"]["max_entropy_call_bound"] == 3.256883
    assert corpus["summary"]["entropy_diagnostics"]["hard_negative_entropy_mass_total"] == 0.011298
    assert corpus["summary"]["entropy_diagnostics"]["negative_margin_count"] == 0
    assert corpus["summary"]["entropy_diagnostics"]["selection_blocked_negative_margin_count"] == 48
    assert corpus["summary"]["entropy_diagnostics"]["nonfinite_entropy_count"] == 0
    assert corpus["summary"]["entropy_diagnostics"]["all_nonfrontier_margin_summary"] == {
        "count": 6196,
        "max": 3612,
        "min": -869,
        "p05": 242,
        "p50": 954,
        "p95": 2660,
    }
    assert corpus["summary"]["entropy_diagnostics"]["hard_negative_margin_summary"] == {
        "count": 2068,
        "max": 3612,
        "min": 605,
        "p05": 1660,
        "p50": 2222,
        "p95": 3190,
    }
    assert corpus["summary"]["entropy_diagnostics"]["dominated_margin_summary"] == {
        "count": 3828,
        "max": 1988,
        "min": 5,
        "p05": 204,
        "p50": 716,
        "p95": 1203,
    }
    assert corpus["summary"]["entropy_diagnostics"]["target_class_entropy_mass"] == {
        "admissible_dominated": 89.485537,
        "gate_rejected": 0.011298,
        "selection_blocked": 94849.053104,
    }
    assert corpus["summary"]["entropy_diagnostics"]["target_class_margin_histogram"] == {
        "admissible_dominated": 3828,
        "gate_rejected": 2068,
        "selection_blocked": 300,
    }
    assert corpus["summary"]["entropy_diagnostics"]["checks"] == {
        "accepting_groups_present": True,
        "actual_frontier_calls_max_is_one": True,
        "candidate_group_count_matches": True,
        "dominated_margins_nonnegative": True,
        "entropy_mass_finite": True,
        "frontier_action_present": True,
        "hard_negative_margins_positive": True,
        "mean_entropy_call_bound_below_exhaustive": True,
        "score_gaps_nonnegative": True,
    }
    assert corpus["summary"]["ranking_diagnostics"]["ok"] is True
    assert corpus["summary"]["ranking_diagnostics"]["accepting_scenario_count"] == 160
    assert corpus["summary"]["ranking_diagnostics"]["no_accepted_scenario_count"] == 80
    assert corpus["summary"]["ranking_diagnostics"]["calls_to_first_accept_total"] == 160
    assert corpus["summary"]["ranking_diagnostics"]["mean_calls_to_first_accept"] == 1.0
    assert corpus["summary"]["ranking_diagnostics"]["calls_to_first_accept_max"] == 1
    assert corpus["summary"]["ranking_diagnostics"]["best_utility_regret_total"] == 0
    assert corpus["summary"]["ranking_diagnostics"]["hard_negative_count"] == 512
    assert corpus["summary"]["ranking_diagnostics"]["hard_negative_scenario_count"] == 128
    assert corpus["summary"]["ranking_diagnostics"]["hard_negative_margin_min"] == 1595
    assert corpus["summary"]["ranking_diagnostics"]["hard_negative_margin_violation_count"] == 0
    assert corpus["summary"]["ranking_diagnostics"]["verifier_call_savings_vs_exhaustive"] == 0.9
    assert corpus["summary"]["sequence_ranking_diagnostics"]["ok"] is True
    assert corpus["summary"]["sequence_ranking_diagnostics"]["step_count"] == 127
    assert corpus["summary"]["sequence_ranking_diagnostics"]["row_count"] == 1270
    assert corpus["summary"]["sequence_ranking_diagnostics"]["accepting_step_count"] == 116
    assert corpus["summary"]["sequence_ranking_diagnostics"]["no_accepted_step_count"] == 11
    assert corpus["summary"]["sequence_ranking_diagnostics"]["selection_blocked_count"] == 318
    assert corpus["summary"]["sequence_ranking_diagnostics"]["blocked_above_first_accept_count"] == 48
    assert corpus["summary"]["sequence_ranking_diagnostics"]["verifier_calls_to_first_accept_total"] == 116
    assert corpus["summary"]["sequence_ranking_diagnostics"]["verifier_calls_to_first_accept_max"] == 1
    assert corpus["summary"]["sequence_ranking_diagnostics"]["mean_verifier_calls_to_first_accept"] == 1.0
    assert corpus["summary"]["sequence_ranking_diagnostics"]["first_verifier_best_utility_count"] == 116
    assert corpus["summary"]["sequence_ranking_diagnostics"]["best_utility_regret_total"] == 0
    assert corpus["summary"]["sequence_ranking_diagnostics"]["verifier_call_savings_vs_exhaustive"] == 0.9
    assert corpus["summary"]["pairwise_diagnostics"]["ok"] is True
    assert corpus["summary"]["pairwise_diagnostics"]["group_count"] == 1099
    assert corpus["summary"]["pairwise_diagnostics"]["expected_group_count"] == 1099
    assert corpus["summary"]["pairwise_diagnostics"]["action_count"] == 10
    assert corpus["summary"]["pairwise_diagnostics"]["accepting_group_count"] == 848
    assert corpus["summary"]["pairwise_diagnostics"]["no_accepted_group_count"] == 251
    assert corpus["summary"]["pairwise_diagnostics"]["source_group_counts"] == {
        "intra_bin_stress": 480,
        "normal_grid": 240,
        "safety_boundary_sweep": 80,
        "safety_interaction_sweep": 160,
        "sequence_step": 127,
        "surface_boundary_sweep": 12,
    }
    assert corpus["summary"]["pairwise_diagnostics"]["accepting_source_counts"] == {
        "intra_bin_stress": 480,
        "normal_grid": 160,
        "safety_boundary_sweep": 40,
        "safety_interaction_sweep": 40,
        "sequence_step": 116,
        "surface_boundary_sweep": 12,
    }
    assert corpus["summary"]["pairwise_diagnostics"]["no_accepted_source_counts"] == {
        "normal_grid": 80,
        "safety_boundary_sweep": 40,
        "safety_interaction_sweep": 120,
        "sequence_step": 11,
    }
    assert corpus["summary"]["pairwise_diagnostics"]["gate_rejected_pair_count"] == 2068
    assert corpus["summary"]["pairwise_diagnostics"]["gate_rejected_margin_min"] == 605
    assert corpus["summary"]["pairwise_diagnostics"]["gate_rejected_margin_violation_count"] == 0
    assert corpus["summary"]["pairwise_diagnostics"]["utility_dominated_pair_count"] == 3828
    assert corpus["summary"]["pairwise_diagnostics"]["utility_dominated_margin_min"] == 5
    assert corpus["summary"]["pairwise_diagnostics"]["utility_dominated_margin_violation_count"] == 0
    assert corpus["summary"]["pairwise_diagnostics"]["utility_dominated_rank_violation_count"] == 0
    assert corpus["summary"]["pairwise_diagnostics"]["selection_blocked_pair_count"] == 1796
    assert corpus["summary"]["pairwise_diagnostics"]["selection_blocked_above_best_accept_count"] == 48
    assert corpus["summary"]["pairwise_diagnostics"]["negative_failure_family_count"] == 11
    assert corpus["summary"]["pairwise_diagnostics"]["negative_failure_family_histogram"] == {
        "anti_oscillation:fee_bps": 246,
        "cooldown_not_elapsed": 240,
        "divergence_bps_exceeds_max_divergence_bps": 374,
        "freshness_lag_epochs_exceeds_max_freshness_lag_epochs": 414,
        "governance_surface_gate_rejected:fee": 1159,
        "governance_surface_gate_rejected:funding": 292,
        "governance_surface_gate_rejected:router": 873,
        "liquidity_depth_below_minimum": 881,
        "trajectory_budget_exceeded:buyburn_bps": 40,
        "trajectory_budget_exceeded:fee_bps": 32,
        "volatility_bps_exceeds_max_volatility_bps": 327,
    }
    assert corpus["summary"]["label_histogram"]["accepted"] > 0
    assert corpus["summary"]["label_histogram"]["rejected"] > 0
    assert corpus["summary"]["source_histogram"] == {
        "intra_bin_stress": 4800,
        "negative_control": 6,
        "normal_grid": 2400,
        "safety_boundary_sweep": 800,
        "safety_interaction_sweep": 1600,
        "safety_lane": 6,
        "sequence_step": 1270,
        "surface_boundary_sweep": 120,
    }
    assert corpus["summary"]["missing_action_ids"] == []
    assert corpus["summary"]["missing_required_errors"] == []
    assert len(corpus["rows"]) == corpus["summary"]["row_count"]
    assert report["replay"]["optimized"]["scenario_count"] == 240
    assert report["replay"]["optimized"]["bin_count"] == 48
    assert report["replay"]["optimized"]["approved_count"] == 160
    assert report["replay"]["optimized"]["rejected_count"] == 80
    assert report["replay"]["optimized"]["adaptive_approved_count"] == 96
    assert report["replay"]["optimized"]["fallback_used_count"] == 0
    assert report["replay"]["optimized"]["candidate_checked_count_total"] == 160
    assert report["replay"]["optimized"]["selection_screened_count_total"] == 0
    assert report["replay"]["optimized"]["selection_penalized_count_total"] == 0
    assert report["replay"]["optimized"]["candidate_considered_count_total"] == 160
    assert report["replay"]["optimized"]["safety_feasible_count"] == 160
    assert report["replay"]["optimized"]["safety_blocked_count"] == 80
    assert report["replay"]["optimized"]["opportunity_miss_count"] == 0
    assert report["replay"]["optimized"]["opportunity_completion_rate"] == 1.0
    assert report["replay"]["optimized"]["frontier_utility_total"] == 9670
    assert report["replay"]["optimized"]["frontier_regret_total"] == 0
    assert report["replay"]["optimized"]["frontier_regret_count"] == 0
    assert report["replay"]["optimized"]["frontier_utility_completion_rate"] == 1.0
    assert report["replay"]["optimized"]["frontier_sample_misses"] == []
    assert report["replay"]["optimized"]["invalid_accept_count"] == 0
    assert report["replay"]["intra_bin_stress"]["scenario_count"] == 480
    assert report["replay"]["intra_bin_stress"]["bin_count"] == 48
    assert report["replay"]["intra_bin_stress"]["probe_profile_count"] == 2
    assert report["replay"]["intra_bin_stress"]["approved_count"] == 480
    assert report["replay"]["intra_bin_stress"]["rejected_count"] == 0
    assert report["replay"]["intra_bin_stress"]["candidate_checked_count_total"] == 480
    assert report["replay"]["intra_bin_stress"]["selection_screened_count_total"] == 0
    assert report["replay"]["intra_bin_stress"]["selection_penalized_count_total"] == 0
    assert report["replay"]["intra_bin_stress"]["candidate_considered_count_total"] == 480
    assert report["replay"]["intra_bin_stress"]["safety_feasible_count"] == 480
    assert report["replay"]["intra_bin_stress"]["safety_blocked_count"] == 0
    assert report["replay"]["intra_bin_stress"]["opportunity_miss_count"] == 0
    assert report["replay"]["intra_bin_stress"]["utility_score_total"] == 31340
    assert report["replay"]["intra_bin_stress"]["frontier_utility_total"] == 31340
    assert report["replay"]["intra_bin_stress"]["frontier_regret_total"] == 0
    assert report["replay"]["intra_bin_stress"]["frontier_regret_count"] == 0
    assert report["replay"]["intra_bin_stress"]["frontier_regret_max"] == 0
    assert report["replay"]["intra_bin_stress"]["frontier_utility_completion_rate"] == 1.0
    assert report["replay"]["intra_bin_stress"]["invalid_accept_count"] == 0
    assert report["replay"]["intra_bin_stress"]["inconsistent_accept_count"] == 0
    assert report["replay"]["intra_bin_stress"]["bin_mismatch_count"] == 0
    assert report["coverage_profile"]["ok"] is True
    assert report["coverage_profile"]["checks"] == {
        "intra_bin_all_bins_present": True,
        "intra_bin_counts_uniform": True,
        "intra_bin_probe_profiles_present": True,
        "intra_bin_stress_ok": True,
        "long_horizon_ids_complete": True,
        "long_horizon_nonempty": True,
        "negative_control_ids_complete": True,
        "normal_grid_all_bins_present": True,
        "normal_grid_bin_counts_uniform": True,
        "required_rejection_errors_observed": True,
        "safety_boundary_anchor_bins_present": True,
        "safety_boundary_anchor_counts_uniform": True,
        "safety_boundary_probe_counts_uniform": True,
        "safety_boundary_probe_profiles_present": True,
        "safety_boundary_sweep_ok": True,
        "safety_interaction_anchor_bins_present": True,
        "safety_interaction_anchor_counts_uniform": True,
        "safety_interaction_control_pair_counts_uniform": True,
        "safety_interaction_control_pairs_present": True,
        "safety_interaction_profile_counts_uniform": True,
        "safety_interaction_profiles_present": True,
        "safety_interaction_sweep_ok": True,
        "safety_lane_ids_complete": True,
        "surface_boundary_profile_counts_uniform": True,
        "surface_boundary_profiles_present": True,
        "surface_boundary_sweep_ok": True,
        "surface_variant_counts_uniform": True,
        "surface_variants_present": True,
    }
    assert report["coverage_profile"]["normal_grid"]["observed_bin_count"] == 48
    assert report["coverage_profile"]["normal_grid"]["missing_bins"] == []
    assert report["coverage_profile"]["normal_grid"]["missing_surface_variants"] == []
    assert report["coverage_profile"]["safety_lanes"]["missing_ids"] == []
    assert report["coverage_profile"]["negative_controls"]["missing_ids"] == []
    assert report["coverage_profile"]["long_horizon"]["missing_ids"] == []
    assert report["coverage_profile"]["long_horizon"]["step_count"] == 127
    assert report["coverage_profile"]["intra_bin_stress"]["observed_bin_count"] == 48
    assert report["coverage_profile"]["intra_bin_stress"]["missing_bins"] == []
    assert report["coverage_profile"]["intra_bin_stress"]["missing_probe_profiles"] == []
    assert report["coverage_profile"]["intra_bin_stress"]["bin_mismatch_count"] == 0
    assert report["coverage_profile"]["intra_bin_stress"]["probe_histogram"] == {
        "bin_ceiling": 240,
        "bin_floor": 240,
    }
    assert report["coverage_profile"]["safety_boundary_sweep"]["required_probe_profiles"] == [
        "freshness_at_limit",
        "freshness_over_limit",
        "divergence_at_limit",
        "divergence_over_limit",
        "volatility_at_limit",
        "volatility_over_limit",
        "liquidity_at_floor",
        "liquidity_below_floor",
        "cooldown_at_limit",
        "cooldown_under_limit",
    ]
    assert report["coverage_profile"]["safety_boundary_sweep"]["probe_histogram"] == {
        "cooldown_at_limit": 8,
        "cooldown_under_limit": 8,
        "divergence_at_limit": 8,
        "divergence_over_limit": 8,
        "freshness_at_limit": 8,
        "freshness_over_limit": 8,
        "liquidity_at_floor": 8,
        "liquidity_below_floor": 8,
        "volatility_at_limit": 8,
        "volatility_over_limit": 8,
    }
    assert report["coverage_profile"]["safety_boundary_sweep"]["required_anchor_bins"] == [
        "0|0|0",
        "0|3|2",
        "1|1|1",
        "1|3|0",
        "2|0|2",
        "2|2|1",
        "3|1|0",
        "3|3|2",
    ]
    assert report["coverage_profile"]["safety_boundary_sweep"]["anchor_bin_histogram"] == {
        "0|0|0": 10,
        "0|3|2": 10,
        "1|1|1": 10,
        "1|3|0": 10,
        "2|0|2": 10,
        "2|2|1": 10,
        "3|1|0": 10,
        "3|3|2": 10,
    }
    assert report["coverage_profile"]["safety_boundary_sweep"]["missing_probe_profiles"] == []
    assert report["coverage_profile"]["safety_boundary_sweep"]["uneven_probe_profiles"] == []
    assert report["coverage_profile"]["safety_boundary_sweep"]["missing_anchor_bins"] == []
    assert report["coverage_profile"]["safety_boundary_sweep"]["uneven_anchor_bins"] == []
    assert report["coverage_profile"]["rejection_error_coverage"]["missing_errors"] == []
    assert report["replay"]["safety_boundary_sweep"]["ok"] is True
    assert report["replay"]["safety_boundary_sweep"]["scenario_count"] == 80
    assert report["replay"]["safety_boundary_sweep"]["approved_count"] == 40
    assert report["replay"]["safety_boundary_sweep"]["rejected_count"] == 40
    assert report["replay"]["safety_boundary_sweep"]["inside_count"] == 40
    assert report["replay"]["safety_boundary_sweep"]["inside_approved_count"] == 40
    assert report["replay"]["safety_boundary_sweep"]["outside_count"] == 40
    assert report["replay"]["safety_boundary_sweep"]["outside_approved_count"] == 0
    assert report["replay"]["safety_boundary_sweep"]["outside_missing_expected_error_count"] == 0
    assert report["replay"]["safety_boundary_sweep"]["invalid_accept_count"] == 0
    assert report["replay"]["safety_boundary_sweep"]["inconsistent_accept_count"] == 0
    assert report["replay"]["safety_boundary_sweep"]["probe_histogram"] == {
        "cooldown_at_limit": 8,
        "cooldown_under_limit": 8,
        "divergence_at_limit": 8,
        "divergence_over_limit": 8,
        "freshness_at_limit": 8,
        "freshness_over_limit": 8,
        "liquidity_at_floor": 8,
        "liquidity_below_floor": 8,
        "volatility_at_limit": 8,
        "volatility_over_limit": 8,
    }
    assert report["replay"]["safety_boundary_sweep"]["anchor_bin_histogram"] == {
        "0|0|0": 10,
        "0|3|2": 10,
        "1|1|1": 10,
        "1|3|0": 10,
        "2|0|2": 10,
        "2|2|1": 10,
        "3|1|0": 10,
        "3|3|2": 10,
    }
    assert report["replay"]["safety_boundary_sweep"]["error_histogram"] == {
        "cooldown_not_elapsed": 8,
        "divergence_bps_exceeds_max_divergence_bps": 8,
        "freshness_lag_epochs_exceeds_max_freshness_lag_epochs": 8,
        "liquidity_depth_below_minimum": 8,
        "volatility_bps_exceeds_max_volatility_bps": 8,
    }
    assert report["replay"]["safety_boundary_sweep"]["checks"] == {
        "anchor_bins_complete": True,
        "anchor_counts_uniform": True,
        "inconsistent_accept_count_zero": True,
        "inside_cases_approve": True,
        "invalid_accept_count_zero": True,
        "outside_cases_reject": True,
        "outside_expected_errors_present": True,
        "probe_counts_uniform": True,
        "probe_profiles_complete": True,
        "scenarios_present": True,
    }
    assert report["coverage_profile"]["safety_interaction_sweep"]["required_profiles"] == [
        "both_inside",
        "first_outside",
        "second_outside",
        "both_outside",
    ]
    assert report["coverage_profile"]["safety_interaction_sweep"]["profile_histogram"] == {
        "both_inside": 40,
        "both_outside": 40,
        "first_outside": 40,
        "second_outside": 40,
    }
    assert report["coverage_profile"]["safety_interaction_sweep"]["required_control_pairs"] == [
        "freshness+divergence",
        "freshness+volatility",
        "freshness+liquidity",
        "freshness+cooldown",
        "divergence+volatility",
        "divergence+liquidity",
        "divergence+cooldown",
        "volatility+liquidity",
        "volatility+cooldown",
        "liquidity+cooldown",
    ]
    assert report["coverage_profile"]["safety_interaction_sweep"]["control_pair_histogram"] == {
        "divergence+cooldown": 16,
        "divergence+liquidity": 16,
        "divergence+volatility": 16,
        "freshness+cooldown": 16,
        "freshness+divergence": 16,
        "freshness+liquidity": 16,
        "freshness+volatility": 16,
        "liquidity+cooldown": 16,
        "volatility+cooldown": 16,
        "volatility+liquidity": 16,
    }
    assert report["coverage_profile"]["safety_interaction_sweep"]["required_anchor_bins"] == [
        "0|0|0",
        "1|3|0",
        "2|2|1",
        "3|3|2",
    ]
    assert report["coverage_profile"]["safety_interaction_sweep"]["anchor_bin_histogram"] == {
        "0|0|0": 40,
        "1|3|0": 40,
        "2|2|1": 40,
        "3|3|2": 40,
    }
    assert report["coverage_profile"]["safety_interaction_sweep"]["missing_profiles"] == []
    assert report["coverage_profile"]["safety_interaction_sweep"]["uneven_profiles"] == []
    assert report["coverage_profile"]["safety_interaction_sweep"]["missing_control_pairs"] == []
    assert report["coverage_profile"]["safety_interaction_sweep"]["uneven_control_pairs"] == []
    assert report["coverage_profile"]["safety_interaction_sweep"]["missing_anchor_bins"] == []
    assert report["coverage_profile"]["safety_interaction_sweep"]["uneven_anchor_bins"] == []
    assert report["replay"]["safety_interaction_sweep"]["ok"] is True
    assert report["replay"]["safety_interaction_sweep"]["scenario_count"] == 160
    assert report["replay"]["safety_interaction_sweep"]["approved_count"] == 40
    assert report["replay"]["safety_interaction_sweep"]["rejected_count"] == 120
    assert report["replay"]["safety_interaction_sweep"]["inside_count"] == 40
    assert report["replay"]["safety_interaction_sweep"]["inside_approved_count"] == 40
    assert report["replay"]["safety_interaction_sweep"]["outside_count"] == 120
    assert report["replay"]["safety_interaction_sweep"]["outside_approved_count"] == 0
    assert report["replay"]["safety_interaction_sweep"]["outside_missing_expected_error_count"] == 0
    assert report["replay"]["safety_interaction_sweep"]["invalid_accept_count"] == 0
    assert report["replay"]["safety_interaction_sweep"]["inconsistent_accept_count"] == 0
    assert report["replay"]["safety_interaction_sweep"]["profile_histogram"] == {
        "both_inside": 40,
        "both_outside": 40,
        "first_outside": 40,
        "second_outside": 40,
    }
    assert report["replay"]["safety_interaction_sweep"]["control_pair_histogram"] == {
        "divergence+cooldown": 16,
        "divergence+liquidity": 16,
        "divergence+volatility": 16,
        "freshness+cooldown": 16,
        "freshness+divergence": 16,
        "freshness+liquidity": 16,
        "freshness+volatility": 16,
        "liquidity+cooldown": 16,
        "volatility+cooldown": 16,
        "volatility+liquidity": 16,
    }
    assert report["replay"]["safety_interaction_sweep"]["anchor_bin_histogram"] == {
        "0|0|0": 40,
        "1|3|0": 40,
        "2|2|1": 40,
        "3|3|2": 40,
    }
    assert report["replay"]["safety_interaction_sweep"]["error_histogram"] == {
        "cooldown_not_elapsed": 32,
        "divergence_bps_exceeds_max_divergence_bps": 32,
        "freshness_lag_epochs_exceeds_max_freshness_lag_epochs": 32,
        "liquidity_depth_below_minimum": 32,
        "volatility_bps_exceeds_max_volatility_bps": 32,
    }
    assert report["replay"]["safety_interaction_sweep"]["checks"] == {
        "anchor_bins_complete": True,
        "anchor_counts_uniform": True,
        "control_pair_counts_uniform": True,
        "control_pairs_complete": True,
        "inconsistent_accept_count_zero": True,
        "inside_cases_approve": True,
        "invalid_accept_count_zero": True,
        "outside_cases_reject": True,
        "outside_expected_errors_present": True,
        "profile_counts_uniform": True,
        "profiles_complete": True,
        "scenarios_present": True,
    }
    assert report["coverage_profile"]["surface_boundary_sweep"]["required_profiles"] == [
        "fee_floor_inside",
        "fee_floor_at_limit",
        "fee_cap_inside",
        "fee_cap_at_limit",
        "funding_floor_inside",
        "funding_floor_at_limit",
        "funding_cap_inside",
        "funding_cap_at_limit",
        "reserve_cap_inside",
        "reserve_cap_at_limit",
        "buyburn_cap_inside",
        "buyburn_cap_at_limit",
    ]
    assert report["coverage_profile"]["surface_boundary_sweep"]["profile_histogram"] == {
        "buyburn_cap_at_limit": 1,
        "buyburn_cap_inside": 1,
        "fee_cap_at_limit": 1,
        "fee_cap_inside": 1,
        "fee_floor_at_limit": 1,
        "fee_floor_inside": 1,
        "funding_cap_at_limit": 1,
        "funding_cap_inside": 1,
        "funding_floor_at_limit": 1,
        "funding_floor_inside": 1,
        "reserve_cap_at_limit": 1,
        "reserve_cap_inside": 1,
    }
    assert report["coverage_profile"]["surface_boundary_sweep"]["missing_profiles"] == []
    assert report["coverage_profile"]["surface_boundary_sweep"]["uneven_profiles"] == []
    assert report["replay"]["surface_boundary_sweep"]["ok"] is True
    assert report["replay"]["surface_boundary_sweep"]["scenario_count"] == 12
    assert report["replay"]["surface_boundary_sweep"]["approved_count"] == 12
    assert report["replay"]["surface_boundary_sweep"]["rejected_count"] == 0
    assert report["replay"]["surface_boundary_sweep"]["candidate_action_count"] == 10
    assert report["replay"]["surface_boundary_sweep"]["candidate_approved_count"] == 104
    assert report["replay"]["surface_boundary_sweep"]["candidate_rejected_count"] == 16
    assert report["replay"]["surface_boundary_sweep"]["q_row_missing_count"] == 0
    assert report["replay"]["surface_boundary_sweep"]["missing_expected_rejection_count"] == 0
    assert report["replay"]["surface_boundary_sweep"]["invalid_accept_count"] == 0
    assert report["replay"]["surface_boundary_sweep"]["inconsistent_accept_count"] == 0
    assert report["replay"]["surface_boundary_sweep"]["boundary_family_histogram"] == {
        "fee": 4,
        "funding": 4,
        "router": 4,
    }
    assert report["replay"]["surface_boundary_sweep"]["limit_status_histogram"] == {
        "at_limit": 6,
        "inside": 6,
    }
    assert report["replay"]["surface_boundary_sweep"]["error_histogram"] == {}
    assert report["replay"]["surface_boundary_sweep"]["candidate_error_histogram"] == {
        "governance_surface_gate_rejected:fee": 7,
        "governance_surface_gate_rejected:funding": 4,
        "governance_surface_gate_rejected:master": 12,
        "governance_surface_gate_rejected:router": 5,
    }
    assert report["replay"]["surface_boundary_sweep"]["checks"] == {
        "candidate_rejections_present": True,
        "expected_rejections_present": True,
        "inconsistent_accept_count_zero": True,
        "invalid_accept_count_zero": True,
        "profile_counts_uniform": True,
        "profiles_complete": True,
        "scenarios_present": True,
        "selected_cases_approve": True,
        "selected_q_rows_complete": True,
    }
    assert report["replay"]["safety_lanes"]["scenario_count"] == 6
    assert report["replay"]["safety_lanes"]["approved_count"] == 0
    assert report["replay"]["safety_lanes"]["missing_expected_error_count"] == 0
    assert report["replay"]["negative_controls"]["scenario_count"] == 6
    assert report["replay"]["negative_controls"]["approved_count"] == 0
    assert report["replay"]["negative_controls"]["invalid_accept_count"] == 0
    assert report["replay"]["negative_controls"]["missing_expected_error_count"] == 0
    assert report["replay"]["long_horizon"]["sequence_count"] == 10
    assert report["replay"]["long_horizon"]["step_count"] == 127
    assert report["replay"]["long_horizon"]["approved_count"] == 116
    assert report["replay"]["long_horizon"]["rejected_count"] == 11
    assert report["replay"]["long_horizon"]["adaptive_approved_count"] == 90
    assert report["replay"]["long_horizon"]["fallback_used_count"] == 0
    assert report["replay"]["long_horizon"]["candidate_checked_count_total"] == 116
    assert report["replay"]["long_horizon"]["selection_screened_count_total"] == 0
    assert report["replay"]["long_horizon"]["selection_penalized_count_total"] == 48
    assert report["replay"]["long_horizon"]["candidate_considered_count_total"] == 116
    assert report["replay"]["long_horizon"]["safety_feasible_count"] == 116
    assert report["replay"]["long_horizon"]["safety_blocked_count"] == 11
    assert report["replay"]["long_horizon"]["opportunity_miss_count"] == 0
    assert report["replay"]["long_horizon"]["opportunity_completion_rate"] == 1.0
    assert report["replay"]["long_horizon"]["utility_score_total"] == 11380
    assert report["replay"]["long_horizon"]["frontier_utility_total"] == 11380
    assert report["replay"]["long_horizon"]["frontier_regret_total"] == 0
    assert report["replay"]["long_horizon"]["frontier_regret_count"] == 0
    assert report["replay"]["long_horizon"]["frontier_regret_max"] == 0
    assert report["replay"]["long_horizon"]["frontier_utility_completion_rate"] == 1.0
    assert report["replay"]["long_horizon"]["frontier_sample_misses"] == []
    assert report["replay"]["long_horizon"]["frontier_selection_blocked_count"] == 318
    assert report["replay"]["long_horizon"]["oscillation_count"] == 0
    assert report["replay"]["long_horizon"]["invalid_accept_count"] == 0
    assert report["replay"]["long_horizon"]["inconsistent_accept_count"] == 0
    assert report["replay"]["long_horizon"]["cumulative_drift_failures"] == []
    assert report["replay"]["long_horizon"]["trajectory_budget_failures"] == []
    assert report["replay"]["long_horizon"]["max_abs_cumulative_drift"]["fee_bps"] == 250
    assert report["replay"]["long_horizon"]["max_abs_cumulative_drift"]["buyburn_bps"] == 1_000
    assert report["replay"]["long_horizon"]["max_abs_cumulative_drift"]["reserve_bps"] == 1_000
    assert report["replay"]["long_horizon"]["max_trajectory_budget_used"]["fee_bps"] == 250
    assert report["replay"]["long_horizon"]["max_trajectory_budget_used"]["buyburn_bps"] == 1_000
    assert report["replay"]["long_horizon"]["max_trajectory_budget_used"]["reserve_bps"] == 1_000
    assert report["replay"]["long_horizon"]["final_state_error_histogram"] == {}
    assert report["replay"]["hold_only"]["invalid_accept_count"] == 0
    assert report["replay"]["hold_only"]["utility_score_total"] == 1650
    assert report["replay"]["pid_like"]["invalid_accept_count"] == 0
    assert report["replay"]["pid_like"]["utility_score_total"] == 7570
    assert report["replay"]["pid_like"]["frontier_regret_total"] == 2100
    assert report["replay"]["long_horizon_hold_only"]["approved_count"] == 116
    assert report["replay"]["long_horizon_hold_only"]["rejected_count"] == 11
    assert report["replay"]["long_horizon_hold_only"]["invalid_accept_count"] == 0
    assert report["replay"]["long_horizon_hold_only"]["opportunity_miss_count"] == 0
    assert report["replay"]["long_horizon_hold_only"]["utility_score_total"] == 1440
    assert report["replay"]["long_horizon_hold_only"]["frontier_regret_total"] == 12040
    assert report["replay"]["long_horizon_pid_like"]["approved_count"] == 116
    assert report["replay"]["long_horizon_pid_like"]["rejected_count"] == 11
    assert report["replay"]["long_horizon_pid_like"]["invalid_accept_count"] == 0
    assert report["replay"]["long_horizon_pid_like"]["opportunity_miss_count"] == 0
    assert report["replay"]["long_horizon_pid_like"]["utility_score_total"] == 11280
    assert report["replay"]["long_horizon_pid_like"]["frontier_regret_total"] == 130
    assert (
        report["replay"]["optimized"]["utility_score_total"]
        > report["replay"]["hold_only"]["utility_score_total"]
    )
    assert (
        report["replay"]["optimized"]["utility_score_total"]
        >= report["replay"]["pid_like"]["utility_score_total"]
    )
    assert (
        report["replay"]["long_horizon"]["utility_score_total"]
        > report["replay"]["long_horizon_hold_only"]["utility_score_total"]
    )
    assert (
        report["replay"]["long_horizon"]["utility_score_total"]
        >= report["replay"]["long_horizon_pid_like"]["utility_score_total"]
    )

    check_report_path = out_dir / "policy_artifact_check.json"
    check_proc = subprocess.run(
        [
            "python3",
            "tools/autonomous_governance_policy_factory.py",
            "--check-policy",
            str(out_dir / "optimized_policy.frozen.json"),
            "--training-corpus",
            str(out_dir / "ebr_training_corpus.json"),
            "--optimizer-report",
            str(out_dir / "optimizer_report.json"),
            "--factory-report",
            str(out_dir / "policy_factory_report.json"),
            "--report-output",
            str(check_report_path),
            "--quiet",
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert check_proc.returncode == 0, check_proc.stderr + check_proc.stdout

    check_report = json.loads(check_report_path.read_text(encoding="utf-8"))
    assert check_report["ok"] is True
    assert check_report["artifact_gate"]["ok"] is True
    assert check_report["promotion_gate"]["ok"] is True
    assert check_report["policy"]["computed_policy_hash"] == frozen_policy["policy_hash"]
    assert check_report["artifact_gate"]["checks"]["factory_report_source_manifest_matches_current"] is True
    assert check_report["artifact_gate"]["checks"]["factory_report_replay_matches_recomputed"] is True
    assert check_report["artifact_gate"]["checks"]["factory_report_coverage_profile_matches_recomputed"] is True
    assert check_report["artifact_gate"]["checks"]["factory_report_training_summary_matches_recomputed"] is True
    assert check_report["artifact_gate"]["checks"]["factory_report_promotion_gate_matches_recomputed"] is True
    assert check_report["source_manifest_artifact"]["provided_sha256"]
    assert (
        check_report["source_manifest_artifact"]["provided_sha256"]
        == check_report["source_manifest_artifact"]["recomputed_sha256"]
    )
    assert check_report["factory_report_artifact"]["provided_replay_sha256"]
    assert (
        check_report["factory_report_artifact"]["provided_replay_sha256"]
        == check_report["factory_report_artifact"]["recomputed_replay_sha256"]
    )
    assert check_report["factory_report_artifact"]["provided_promotion_gate_sha256"]
    assert (
        check_report["factory_report_artifact"]["provided_promotion_gate_sha256"]
        == check_report["factory_report_artifact"]["recomputed_promotion_gate_sha256"]
    )
    assert check_report["training_corpus_artifact"]["provided_sha256"]
    assert (
        check_report["training_corpus_artifact"]["provided_sha256"]
        == check_report["training_corpus_artifact"]["recomputed_sha256"]
    )
