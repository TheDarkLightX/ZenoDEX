from __future__ import annotations

import json
import subprocess
import sys
from copy import deepcopy
from pathlib import Path

import pytest

from src.integration.autonomous_governance_q_policy import (
    BoundedParameter,
    admit_autonomous_governance_surface_request_v1,
    commit_autonomous_governance_surface_q_policy_v1,
    evaluate_autonomous_governance_q_policy_v1,
    evaluate_autonomous_governance_surface_q_policy_v1,
    policy_content_hash_v1,
    q_learning_update_fixed_point_v1,
    sample_autonomous_governance_next_policy_v1,
    sample_autonomous_governance_q_policy_v1,
    sample_autonomous_governance_surface_q_policy_v1,
)
from src.integration.zeno_governance_hashing import hash_v0
from src.tau_specs.governance import gov_gate


def _params(*, fee_step: int = 10) -> dict[str, BoundedParameter]:
    return {
        "fee": BoundedParameter(current=30, minimum=0, maximum=100, step=fee_step),
        "buyback": BoundedParameter(current=20, minimum=0, maximum=100, step=10),
        "rebate": BoundedParameter(current=10, minimum=0, maximum=100, step=10),
        "floor": BoundedParameter(current=100_000, minimum=0, maximum=1_000_000, step=1_000),
        "unit": BoundedParameter(current=10_000, minimum=1, maximum=10_000, step=0),
        "tier1": BoundedParameter(current=30, minimum=1, maximum=365, step=10),
        "tier2": BoundedParameter(current=90, minimum=2, maximum=730, step=10),
        "weight1": BoundedParameter(current=100, minimum=0, maximum=1_000, step=25),
        "weight2": BoundedParameter(current=200, minimum=0, maximum=1_000, step=25),
        "weight3": BoundedParameter(current=300, minimum=0, maximum=1_000, step=25),
    }


def _observation(**overrides: int) -> dict[str, int]:
    obs = {
        "observed_price_bps": 10_500,
        "target_price_bps": 10_000,
        "volatility_bps": 250,
        "divergence_bps": 10,
        "freshness_lag_epochs": 0,
        "liquidity_depth_bps": 5_000,
    }
    obs.update(overrides)
    return obs


def _next_observation(**overrides: int) -> dict[str, int]:
    obs = _observation(
        observed_price_bps=10_000,
        target_price_bps=10_000,
        volatility_bps=25,
        liquidity_depth_bps=5_000,
    )
    obs.update(
        {
            "oracle_confidence_bps": 9_900,
            "liquidity_concentration_bps": 2_000,
            "recent_governance_churn_bps": 0,
            "proof_market_health_bps": 9_900,
            "validator_stress_bps": 100,
            "network_stress_bps": 100,
        }
    )
    obs.update(overrides)
    return obs


def _surface_state(**overrides: int) -> dict[str, int]:
    state = {
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
    state.update(overrides)
    return state


def _surface_policy_with_selection_mode(mode: str) -> dict:
    policy = deepcopy(sample_autonomous_governance_surface_q_policy_v1())
    policy["selection"] = {"mode": mode}
    policy["policy_hash"] = policy_content_hash_v1(policy)
    return policy


def _surface_policy_forcing_action(action_id: str, *, mode: str = "top_scored") -> dict:
    policy = deepcopy(sample_autonomous_governance_surface_q_policy_v1())
    policy["selection"] = {"mode": mode}
    policy["q_layers"].append(
        {
            "id": f"test_force_{action_id}",
            "features": ["deviation_bps"],
            "q_table": {"*": {action_id: 1_000_000}},
        }
    )
    policy["policy_hash"] = policy_content_hash_v1(policy)
    return policy


def test_q_policy_selects_deterministic_action_and_builds_revision_packet() -> None:
    policy = sample_autonomous_governance_q_policy_v1()
    result = evaluate_autonomous_governance_q_policy_v1(
        policy=policy,
        parameters=_params(),
        observation=_observation(),
        current_epoch=12,
        proposal_epoch=10,
        min_delay_epochs=1,
        last_update_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["approved"] is True
    assert result["action_id"] == "raise_fee_10"
    assert result["proposed"]["fee"] == 40
    assert result["revision_step"]["i1"] == 1
    assert result["revision_step"]["i2"] == 1
    assert result["revision_step"]["i6"] == 30
    assert result["revision_step"]["i7"] == 40
    assert result["revision_step"]["i10"] == 10
    assert "does_not_authorize_settlement" in result["not_claimed"]


def test_stale_oracle_fails_closed_even_when_q_table_wants_action() -> None:
    policy = sample_autonomous_governance_q_policy_v1()
    result = evaluate_autonomous_governance_q_policy_v1(
        policy=policy,
        parameters=_params(),
        observation=_observation(freshness_lag_epochs=3),
        current_epoch=12,
        proposal_epoch=10,
        min_delay_epochs=1,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is False
    assert result["approved"] is False
    assert "freshness_lag_epochs_exceeds_max_freshness_lag_epochs" in result["errors"]
    assert result["action_id"] == "raise_fee_10"
    assert result["revision_step"]["i1"] == 0


def test_policy_hash_mismatch_blocks_autonomous_authority() -> None:
    policy = sample_autonomous_governance_q_policy_v1()
    result = evaluate_autonomous_governance_q_policy_v1(
        policy=policy,
        parameters=_params(),
        observation=_observation(),
        current_epoch=12,
        proposal_epoch=10,
        min_delay_epochs=1,
        expected_policy_hash="0x" + "00" * 32,
    )

    assert result["ok"] is False
    assert "policy_hash_mismatch" in result["errors"]
    assert result["revision_step"]["i1"] == 0


def test_malformed_policy_returns_fail_closed_receipt() -> None:
    result = evaluate_autonomous_governance_q_policy_v1(
        policy=[],  # type: ignore[arg-type]
        parameters=_params(),
        observation=_observation(),
        current_epoch=12,
        proposal_epoch=10,
        min_delay_epochs=1,
        expected_policy_hash="0x" + "00" * 32,
    )

    assert result["ok"] is False
    assert result["approved"] is False
    assert result["policy_hash"] == ""
    assert "policy_must_be_object" in result["errors"]
    assert "policy_hash_unavailable" in result["errors"]
    assert "policy_hash_mismatch" in result["errors"]
    assert result["revision_step"]["i1"] == 0


def test_invalid_policy_version_fails_closed_without_raising() -> None:
    policy = sample_autonomous_governance_q_policy_v1()
    policy = deepcopy(policy)
    policy["version"] = "bad"

    result = evaluate_autonomous_governance_q_policy_v1(
        policy=policy,
        parameters=_params(),
        observation=_observation(),
        current_epoch=12,
        proposal_epoch=10,
        min_delay_epochs=1,
    )

    assert result["ok"] is False
    assert result["approved"] is False
    assert "version must be an int" in result["errors"]
    assert result["revision_step"]["i1"] == 0


def test_bounded_parameter_rejects_non_plain_int_fields() -> None:
    class WeirdInt(int):
        pass

    with pytest.raises(ValueError):
        BoundedParameter(current=True, minimum=0, maximum=100, step=10)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        BoundedParameter(current=WeirdInt(30), minimum=0, maximum=100, step=10)


def test_step_violation_blocks_table_action() -> None:
    policy = sample_autonomous_governance_q_policy_v1()
    result = evaluate_autonomous_governance_q_policy_v1(
        policy=policy,
        parameters=_params(fee_step=5),
        observation=_observation(),
        current_epoch=12,
        proposal_epoch=10,
        min_delay_epochs=1,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["action_id"] == "raise_fee_10"
    assert result["approved"] is False
    assert "fee_step_exceeded" in result["errors"]
    assert result["revision_step"]["i1"] == 0
    assert result["revision_step"]["i7"] == 40


def test_equal_q_scores_tie_break_by_action_order() -> None:
    policy = sample_autonomous_governance_q_policy_v1()
    policy = deepcopy(policy)
    policy["actions"] = [
        {"id": "hold", "deltas": {}},
        {"id": "raise_fee_5", "deltas": {"fee": 5}},
    ]
    policy["q_layers"] = [
        {
            "id": "tie",
            "features": ["deviation_bps"],
            "q_table": {"3": {"hold": 7, "raise_fee_5": 7}},
        }
    ]
    policy["policy_hash"] = policy_content_hash_v1(policy)

    result = evaluate_autonomous_governance_q_policy_v1(
        policy=policy,
        parameters=_params(),
        observation=_observation(),
        current_epoch=12,
        proposal_epoch=10,
        min_delay_epochs=1,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["action_id"] == "hold"
    assert result["proposed"]["fee"] == 30


def test_q_learning_update_is_fixed_point_for_offline_table_generation() -> None:
    updated = q_learning_update_fixed_point_v1(
        q_value=100,
        reward=40,
        next_best_q=200,
        alpha_ppm=500_000,
        gamma_ppm=800_000,
    )

    assert updated == 150


def test_surface_q_policy_uses_verified_governance_gates() -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()

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
    assert result["proposed"]["fee_bps"] == 40
    assert result["proposed"]["funding_cap_bps"] == 115
    assert result["governance_surface_gate_report"] == {
        "fee": True,
        "router": True,
        "collateral": True,
        "whale": True,
        "funding": True,
        "master": True,
    }
    assert result["governance_surface_all_gates_ok"] is True


def test_surface_q_policy_commit_applies_only_after_gate_approval() -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()
    initial = _surface_state()

    result = commit_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=initial,
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        last_update_epoch=32,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["admitted"] is True
    assert result["reason"] == "admitted"
    assert result["committed_state"] == initial
    assert result["applied_state"]["fee_bps"] == 40
    assert result["applied_state"]["funding_cap_bps"] == 115
    assert result["gate_recheck"]["master"] is True


def test_surface_q_policy_commit_noops_on_gate_rejection() -> None:
    policy = _surface_policy_forcing_action("raise_fee_10_tighten_funding_5")
    initial = _surface_state(fee_bps=995)

    result = commit_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=initial,
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["admitted"] is False
    assert result["reason"] == "receipt_rejected_noop"
    assert result["receipt"]["approved"] is False
    assert result["applied_state"] == initial
    assert result["receipt"]["proposed"]["fee_bps"] == 1005


def test_surface_q_policy_commit_noops_on_safety_rejection() -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()
    initial = _surface_state()

    result = commit_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=initial,
        observation=_observation(freshness_lag_epochs=3),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["admitted"] is False
    assert result["reason"] == "receipt_rejected_noop"
    assert result["applied_state"] == initial
    assert "freshness_lag_epochs_exceeds_max_freshness_lag_epochs" in result["receipt"]["errors"]


def test_surface_q_policy_rejects_stale_oracle_before_autonomous_approval() -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(),
        observation=_observation(freshness_lag_epochs=3),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is False
    assert result["approved"] is False
    assert "freshness_lag_epochs_exceeds_max_freshness_lag_epochs" in result["errors"]
    assert result["governance_surface_gate_report"]["fee"] is True
    assert result["governance_surface_all_gates_ok"] is True


def test_surface_q_policy_rejects_int_subclass_state_fail_closed() -> None:
    class WeirdInt(int):
        pass

    policy = sample_autonomous_governance_surface_q_policy_v1()
    state = _surface_state(fee_bps=WeirdInt(30))

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=state,
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is False
    assert result["approved"] is False
    assert "fee_bps must be an int" in result["errors"]


def test_surface_q_policy_hash_mismatch_blocks_approval() -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(),
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash="0x" + "00" * 32,
    )

    assert result["ok"] is False
    assert result["approved"] is False
    assert "policy_hash_mismatch" in result["errors"]
    assert result["governance_surface_all_gates_ok"] is True


def test_surface_q_policy_blocks_verified_fee_cap_breach() -> None:
    policy = _surface_policy_forcing_action("raise_fee_10_tighten_funding_5")

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(fee_bps=995),
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["action_id"] == "raise_fee_10_tighten_funding_5"
    assert result["proposed"]["fee_bps"] == 1005
    assert result["governance_surface_gate_report"]["fee"] is False
    assert result["governance_surface_gate_report"]["master"] is False
    assert result["governance_surface_all_gates_ok"] is False
    assert "governance_surface_gate_rejected:fee" in result["errors"]
    assert result["approved"] is False


def test_surface_q_policy_gate_recheck_uses_import_bound_scalar_gate(monkeypatch: pytest.MonkeyPatch) -> None:
    policy = _surface_policy_forcing_action("raise_fee_10_tighten_funding_5")
    initial = _surface_state(fee_bps=995)

    monkeypatch.setattr(gov_gate, "fee_revision_ok", lambda *args: True)
    monkeypatch.setattr(gov_gate, "master_revision_ok", lambda *args: True)

    result = commit_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=initial,
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["admitted"] is False
    assert result["reason"] == "receipt_rejected_noop"
    assert result["applied_state"] == initial
    assert result["receipt"]["proposed"]["fee_bps"] == 1005
    assert result["receipt"]["governance_surface_gate_report"]["fee"] is False
    assert result["receipt"]["governance_surface_gate_report"]["master"] is False
    assert result["gate_recheck"]["fee"] is False
    assert result["gate_recheck"]["master"] is False


def test_surface_q_policy_gate_recheck_uses_import_bound_group_gate(monkeypatch: pytest.MonkeyPatch) -> None:
    policy = deepcopy(sample_autonomous_governance_surface_q_policy_v1())
    policy["actions"] = [
        {"id": "hold", "deltas": {}},
        {"id": "break_router_sum", "deltas": {"buyburn_bps": 100}},
    ]
    policy["selection"] = {"mode": "top_scored"}
    policy["q_layers"] = [
        {
            "id": "router_spoof_regression",
            "features": ["deviation_bps"],
            "q_table": {"3": {"break_router_sum": 100, "hold": 0}},
        }
    ]
    policy["policy_hash"] = policy_content_hash_v1(policy)
    initial = _surface_state()

    monkeypatch.setattr(gov_gate, "router_revision_ok", lambda *args: True)
    monkeypatch.setattr(gov_gate, "master_revision_ok", lambda *args: True)

    result = commit_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=initial,
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["admitted"] is False
    assert result["reason"] == "receipt_rejected_noop"
    assert result["applied_state"] == initial
    assert result["proposed_state"]["buyburn_bps"] == 6_100
    assert result["receipt"]["governance_surface_gate_report"]["router"] is False
    assert result["receipt"]["governance_surface_gate_report"]["master"] is False
    assert result["gate_recheck"]["router"] is False
    assert result["gate_recheck"]["master"] is False


def test_surface_q_policy_first_admissible_prefers_hold_at_fee_cap() -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()
    policy = deepcopy(policy)
    policy["selection"] = {"mode": "first_admissible"}
    policy["policy_hash"] = policy_content_hash_v1(policy)

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(fee_bps=995),
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["approved"] is True
    assert result["action_id"] == "hold"
    assert result["proposed"]["fee_bps"] == 995
    assert result["candidate_search"]["mode"] == "first_admissible"
    assert result["candidate_search"]["fallback_used"] is False
    assert result["candidate_search"]["raw_top_action_id"] == "hold"
    assert result["candidate_search"]["checked_count"] == 1


def test_surface_q_policy_uses_surface_state_bins_before_fallback() -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()
    policy = deepcopy(policy)
    policy["selection"] = {"mode": "first_admissible"}
    policy["state_bins"]["fee_bps"] = [50, 990]
    policy["q_layers"].append(
        {
            "id": "fee_cap_bias",
            "features": ["fee_bps"],
            "q_table": {"2": {"raise_fee_10_tighten_funding_5": -500, "raise_fee_10": -500, "hold": 500}},
        }
    )
    policy["policy_hash"] = policy_content_hash_v1(policy)

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(fee_bps=995),
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["approved"] is True
    assert result["action_id"] == "hold"
    assert result["state_bins"]["fee_bps"] == 2
    assert result["candidate_search"]["fallback_used"] is False
    assert result["candidate_search"]["checked_count"] == 1


def test_surface_sample_policy_matches_factory_frontier_grid() -> None:
    import tools.autonomous_governance_policy_factory as factory

    report = factory._replay_policy(  # noqa: SLF001 - factory replay is the local metric oracle.
        sample_autonomous_governance_surface_q_policy_v1(),
        label="sample_surface_policy",
    )

    assert report["scenario_count"] == 240
    assert report["safety_feasible_count"] == 160
    assert report["opportunity_miss_count"] == 0
    assert report["frontier_regret_total"] == 0
    assert report["frontier_regret_count"] == 0
    assert report["frontier_utility_completion_rate"] == 1.0
    assert report["utility_score_total"] == report["frontier_utility_total"] == 9_670
    assert report["fallback_used_count"] == 0
    assert report["candidate_checked_count_total"] == 160
    assert report["candidate_considered_count_total"] == 160
    assert report["invalid_accept_count"] == 0
    assert report["inconsistent_accept_count"] == 0


def test_surface_sample_policy_matches_edge_and_trajectory_frontiers() -> None:
    import tools.autonomous_governance_policy_factory as factory

    policy = sample_autonomous_governance_surface_q_policy_v1()
    intra_bin = factory._replay_intra_bin_stress(  # noqa: SLF001 - factory replay is the local metric oracle.
        policy,
        label="sample_surface_policy_intra_bin",
    )
    long_horizon = factory._replay_long_horizon_sequences(  # noqa: SLF001
        policy,
        label="sample_surface_policy_long_horizon",
    )
    surface_boundary = factory._replay_surface_boundary_sweep(  # noqa: SLF001
        policy,
        label="sample_surface_policy_surface_boundary",
    )

    assert intra_bin["scenario_count"] == 480
    assert intra_bin["safety_feasible_count"] == 480
    assert intra_bin["opportunity_miss_count"] == 0
    assert intra_bin["frontier_regret_total"] == 0
    assert intra_bin["frontier_regret_count"] == 0
    assert intra_bin["frontier_utility_completion_rate"] == 1.0
    assert intra_bin["utility_score_total"] == intra_bin["frontier_utility_total"] == 28_600
    assert intra_bin["fallback_used_count"] == 0
    assert intra_bin["candidate_checked_count_total"] == 480
    assert intra_bin["candidate_considered_count_total"] == 480
    assert intra_bin["invalid_accept_count"] == 0
    assert intra_bin["inconsistent_accept_count"] == 0

    assert long_horizon["step_count"] == 127
    assert long_horizon["safety_feasible_count"] == 116
    assert long_horizon["opportunity_miss_count"] == 0
    assert long_horizon["frontier_regret_total"] == 0
    assert long_horizon["frontier_regret_count"] == 0
    assert long_horizon["frontier_utility_completion_rate"] == 1.0
    assert long_horizon["utility_score_total"] == long_horizon["frontier_utility_total"] == 11_380
    assert long_horizon["fallback_used_count"] == 0
    assert long_horizon["candidate_checked_count_total"] == 116
    assert long_horizon["selection_screened_count_total"] == 12
    assert long_horizon["candidate_considered_count_total"] == 128
    assert long_horizon["cumulative_drift_failures"] == ()
    assert long_horizon["trajectory_budget_failures"] == ()
    assert long_horizon["invalid_accept_count"] == 0
    assert long_horizon["inconsistent_accept_count"] == 0

    assert surface_boundary["ok"] is True
    assert surface_boundary["scenario_count"] == 12
    assert surface_boundary["approved_count"] == 12
    assert surface_boundary["runtime_action_count"] == 5
    assert surface_boundary["candidate_action_count"] == 11
    assert surface_boundary["q_row_missing_count"] == 0
    assert surface_boundary["missing_expected_rejection_count"] == 0
    assert surface_boundary["invalid_accept_count"] == 0
    assert surface_boundary["inconsistent_accept_count"] == 0


def test_surface_sample_policy_ebr_residual_abstains_when_base_policy_is_saturated() -> None:
    import tools.autonomous_governance_policy_factory as factory

    policy = sample_autonomous_governance_surface_q_policy_v1()
    training_corpus = factory._build_training_corpus(policy)  # noqa: SLF001
    residual = factory._train_ebr_residual_lookup_model(training_corpus)  # noqa: SLF001
    candidate = factory._policy_with_trained_ebr_residual(policy, residual)  # noqa: SLF001

    assert residual["ok"] is True
    assert residual["apply_residual"] is False
    assert residual["abstained"] is True
    assert residual["abstention_reason"] == "base_policy_rank1_saturated"
    assert residual["q_table_completion"]["ok"] is True
    assert residual["abstention_checks"] == {
        "training_rows_present": True,
        "q_table_complete": True,
        "train_policy_frontier_rank1_complete": True,
        "validation_policy_frontier_rank1_complete": True,
        "train_policy_calls_are_one": True,
        "validation_policy_calls_are_one": True,
        "residual_application_not_promoted": True,
    }
    assert all(
        layer["id"] != factory.TRAINED_EBR_RESIDUAL_LAYER_ID
        for layer in candidate["q_layers"]
    )


def test_autogovnext_ebr_residual_promotes_on_coarse_policy() -> None:
    import tools.autonomous_governance_policy_factory as factory

    policy = deepcopy(sample_autonomous_governance_next_policy_v1())
    policy["policy_id"] = "coarse_autogovnext_residual_regression"
    policy["q_layers"] = [
        {
            "id": "coarse_hold_only",
            "features": ["deviation_bps"],
            "q_table": {"*": {"hold": 10}},
        }
    ]
    policy["policy_hash"] = policy_content_hash_v1(policy)

    training_corpus = factory._build_training_corpus(policy)  # noqa: SLF001
    residual = factory._train_ebr_residual_lookup_model(training_corpus)  # noqa: SLF001
    candidate = factory._policy_with_trained_ebr_residual(policy, residual)  # noqa: SLF001
    validation_policy = residual["metrics"]["validation"]["policy"]
    validation_hybrid = residual["metrics"]["validation"]["hybrid"]

    assert residual["ok"] is True
    assert residual["apply_residual"] is True
    assert residual["abstained"] is False
    assert residual["promotion_mode"] == "improves_coarse_policy"
    assert residual["q_table_completion"]["ok"] is True
    assert residual["q_table_completion"]["completion_mode"] == "neutral_wildcard"
    assert (
        residual["q_table_completion"]["materialized_key_count"]
        < residual["q_table_completion"]["effective_completed_key_count"]
    )
    assert residual["q_table_completion"]["neutral_fill_key_count"] > 0
    assert (
        residual["q_table_key_count"]
        == residual["q_table_completion"]["materialized_key_count"]
    )
    assert residual["improvement_promotion_checks"] == {
        "training_rows_present": True,
        "q_table_nonempty": True,
        "q_table_complete": True,
        "train_hybrid_frontier_rank1_improves_policy": True,
        "validation_hybrid_frontier_rank1_improves_policy": True,
        "train_hybrid_calls_improve_policy": True,
        "validation_hybrid_calls_improve_policy": True,
        "validation_hybrid_nonfrontier_p50_improves_policy": True,
        "validation_hybrid_hard_negative_min_not_worse_than_policy": True,
        "validation_hybrid_hard_negative_accuracy_not_worse_than_policy": True,
        "cross_seed_nonfrontier_p50_lift_positive": True,
    }
    assert validation_hybrid["rank1_frontier_count"] > validation_policy["rank1_frontier_count"]
    assert validation_hybrid["calls_to_frontier_max"] < validation_policy["calls_to_frontier_max"]
    assert validation_hybrid["mean_calls_to_frontier"] < validation_policy["mean_calls_to_frontier"]
    assert any(
        layer["id"] == factory.TRAINED_EBR_RESIDUAL_LAYER_ID
        for layer in candidate["q_layers"]
    )


def test_policy_factory_training_summary_scope_marks_smoke_as_diagnostic() -> None:
    import tools.autonomous_governance_policy_factory as factory

    failed_summary = {"ok": False}
    full_scope = factory._training_corpus_summary_scope(  # noqa: SLF001
        validation_profile="full",
        training_corpus_summary=failed_summary,
    )
    smoke_scope = factory._training_corpus_summary_scope(  # noqa: SLF001
        validation_profile="frontier-smoke",
        training_corpus_summary=failed_summary,
    )

    assert full_scope["ok"] is False
    assert full_scope["blocking"] is True
    assert smoke_scope["ok"] is False
    assert smoke_scope["blocking"] is False
    assert smoke_scope["profile"] == "frontier-smoke"
    assert "diagnostic" in smoke_scope["boundary"]


def test_autogovnext_fee_normalization_relaxes_funding_through_live_commit_path() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    initial = _surface_state(fee_bps=300, funding_cap_bps=150)

    result = commit_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=initial,
        observation=_next_observation(),
        current_epoch=50,
        proposal_epoch=10,
        last_update_epoch=48,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["admitted"] is True
    assert result["receipt"]["action_id"] == "lower_fee_10_relax_funding_5"
    assert result["applied_state"]["fee_bps"] == 290
    assert result["applied_state"]["funding_cap_bps"] == 155
    assert result["receipt"]["governance_surface_all_gates_ok"] is True
    assert result["gate_recheck"]["funding"] is True


def test_autogovnext_funding_relaxation_falls_back_at_cap() -> None:
    policy = sample_autonomous_governance_next_policy_v1()

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(fee_bps=300, funding_cap_bps=200),
        observation=_next_observation(),
        current_epoch=50,
        proposal_epoch=10,
        last_update_epoch=48,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["approved"] is True
    assert result["action_id"] == "lower_fee_10"
    assert result["proposed"]["fee_bps"] == 290
    assert result["proposed"]["funding_cap_bps"] == 200
    assert result["candidate_search"]["raw_top_action_id"] == "lower_fee_10_relax_funding_5"
    assert result["candidate_search"]["fallback_used"] is True
    assert result["candidate_search"]["rejected_candidates"][0] == {
        "action_id": "lower_fee_10_relax_funding_5",
        "failed_gates": ("funding",),
    }


def test_autogovnext_low_oracle_confidence_fails_closed_before_apply() -> None:
    policy = sample_autonomous_governance_next_policy_v1()

    result = commit_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(fee_bps=300, funding_cap_bps=150),
        observation=_next_observation(oracle_confidence_bps=6_999),
        current_epoch=50,
        proposal_epoch=10,
        last_update_epoch=48,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["admitted"] is False
    assert result["applied_state"] == _surface_state(fee_bps=300, funding_cap_bps=150)
    assert "oracle_confidence_bps_below_min_oracle_confidence_bps" in result["receipt"]["errors"]


def test_autogovnext_proof_market_health_rebalances_router_to_hosts() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    state = _surface_state(buyburn_bps=100, reserve_bps=9_900, hosts_bps=0)

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=state,
        observation=_next_observation(proof_market_health_bps=3_000),
        current_epoch=50,
        proposal_epoch=10,
        last_update_epoch=48,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["approved"] is True
    assert result["action_id"] == "shift_router_reserve_to_hosts_100"
    assert result["proposed"]["reserve_bps"] == 9_800
    assert result["proposed"]["hosts_bps"] == 100
    assert result["governance_surface_gate_report"]["router"] is True


def test_autogovnext_network_stress_freezes_recovery_actions() -> None:
    policy = sample_autonomous_governance_next_policy_v1()

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(fee_bps=300, funding_cap_bps=150),
        observation=_next_observation(
            observed_price_bps=10_500,
            volatility_bps=250,
            validator_stress_bps=6_000,
            network_stress_bps=6_000,
        ),
        current_epoch=50,
        proposal_epoch=10,
        last_update_epoch=48,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is True
    assert result["approved"] is True
    assert result["action_id"] == "hold"
    assert result["proposed"] == result["surface_state"]


def test_autogovnext_high_deviation_low_funding_uses_fee_only_recovery() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    current_epoch = 700

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(fee_bps=260, funding_cap_bps=5),
        observation=_next_observation(
            observed_price_bps=10_301,
            target_price_bps=10_000,
            volatility_bps=300,
            liquidity_depth_bps=4_000,
        ),
        current_epoch=current_epoch,
        proposal_epoch=current_epoch - gov_gate.MIN_DELAY,
        last_update_epoch=650,
        expected_policy_hash=policy["policy_hash"],
        previous_approved_deltas={"fee_bps": 10, "funding_cap_bps": -5},
        trajectory_used={"fee_bps": 230, "funding_cap_bps": 115},
    )

    assert result["approved"] is True
    assert result["action_id"] == "raise_fee_10"
    assert result["proposed"]["fee_bps"] == 270
    assert result["proposed"]["funding_cap_bps"] == 5


def test_autogovnext_low_liquidity_router_continues_reserve_recovery() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    current_epoch = 250

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(
            fee_bps=30,
            buyburn_bps=5_400,
            reserve_bps=2_600,
            hosts_bps=2_000,
        ),
        observation=_next_observation(
            observed_price_bps=10_000,
            target_price_bps=10_000,
            volatility_bps=100,
            liquidity_depth_bps=1_000,
        ),
        current_epoch=current_epoch,
        proposal_epoch=current_epoch - gov_gate.MIN_DELAY,
        last_update_epoch=225,
        expected_policy_hash=policy["policy_hash"],
        previous_approved_deltas={"buyburn_bps": -100, "reserve_bps": 100},
        trajectory_used={"buyburn_bps": 600, "reserve_bps": 600},
    )

    assert result["approved"] is True
    assert result["action_id"] == "shift_router_to_reserve_100"
    assert result["proposed"]["buyburn_bps"] == 5_300
    assert result["proposed"]["reserve_bps"] == 2_700


def test_autogovnext_actions_satisfy_monotonic_gate_envelope() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    state = _surface_state(fee_bps=300, funding_cap_bps=150, buyburn_bps=3_000, reserve_bps=4_000, hosts_bps=3_000)
    observation = _next_observation()

    for action in policy["actions"]:
        action_id = action["id"]
        forced = deepcopy(policy)
        forced["selection"] = {"mode": "top_scored"}
        forced["q_layers"] = [
            {
                "id": "force_one_action",
                "features": ["deviation_bps"],
                "q_table": {
                    "*": {
                        candidate["id"]: (1_000_000 if candidate["id"] == action_id else -1_000_000)
                        for candidate in policy["actions"]
                    }
                },
            }
        ]
        forced["policy_hash"] = policy_content_hash_v1(forced)
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=forced,
            surface_state=state,
            observation=observation,
            current_epoch=50,
            proposal_epoch=10,
            last_update_epoch=48,
            expected_policy_hash=forced["policy_hash"],
        )
        if result["approved"] is not True:
            continue
        proposed = result["proposed"]
        assert 0 <= proposed["fee_bps"] <= gov_gate.FEE_MAX_BPS
        assert abs(proposed["fee_bps"] - state["fee_bps"]) <= gov_gate.FEE_STEP_BPS
        assert 0 <= proposed["funding_cap_bps"] <= gov_gate.FUNDING_CAP_MAX_BPS
        assert abs(proposed["funding_cap_bps"] - state["funding_cap_bps"]) <= gov_gate.FUNDING_STEP_BPS
        assert (
            proposed["buyburn_bps"]
            + proposed["stakers_bps"]
            + proposed["reserve_bps"]
            + proposed["hosts_bps"]
            == gov_gate.SPLIT_SUM
        )
        for share in ("buyburn_bps", "stakers_bps", "reserve_bps", "hosts_bps"):
            assert 0 <= proposed[share] <= gov_gate.SPLIT_SHARE_MAX
            assert abs(proposed[share] - state[share]) <= gov_gate.SPLIT_STEP_BPS
        assert gov_gate.RATIO_MIN_BPS <= proposed["mcr_bps"] <= proposed["ccr_bps"]
        assert proposed["ccr_bps"] <= gov_gate.RATIO_MAX_BPS
        assert proposed["staker_bps"] <= gov_gate.WHALE_STAKER_BPS_MAX


def test_autogovnext_adversarial_trajectory_stays_fail_closed() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    state = _surface_state(fee_bps=300, funding_cap_bps=150, buyburn_bps=100, reserve_bps=9_900, hosts_bps=0)
    previous_deltas: dict[str, int] = {}
    trajectory_used: dict[str, int] = {}
    last_update_epoch = 48
    observed: list[dict] = []

    steps = (
        {
            "id": "slow_drip_fee_normalization",
            "observation": _next_observation(),
            "expect_admitted": True,
            "expect_action": "lower_fee_10_relax_funding_5",
        },
        {
            "id": "reversal_pressure_after_fee_decrease",
            "observation": _next_observation(observed_price_bps=10_500, volatility_bps=250),
            "expect_admitted": True,
            "forbid_actions": {"raise_fee_10", "raise_fee_10_tighten_funding_5"},
        },
        {
            "id": "correlated_oracle_network_shock",
            "observation": _next_observation(oracle_confidence_bps=6_500, network_stress_bps=8_001),
            "expect_admitted": False,
            "expected_errors": {
                "oracle_confidence_bps_below_min_oracle_confidence_bps",
                "network_stress_bps_exceeds_max_network_stress_bps",
            },
        },
        {
            "id": "proof_market_router_rebalance",
            "observation": _next_observation(proof_market_health_bps=3_000),
            "expect_admitted": True,
            "expect_action": "shift_router_reserve_to_hosts_100",
        },
    )

    for index, step in enumerate(steps):
        before = dict(state)
        result = commit_autonomous_governance_surface_q_policy_v1(
            policy=policy,
            surface_state=state,
            observation=step["observation"],
            current_epoch=50 + (25 * index),
            proposal_epoch=10,
            last_update_epoch=last_update_epoch,
            expected_policy_hash=policy["policy_hash"],
            previous_approved_deltas=previous_deltas,
            trajectory_used=trajectory_used,
        )
        observed.append(result)
        assert result["admitted"] is step["expect_admitted"]
        if "expect_action" in step:
            assert result["receipt"]["action_id"] == step["expect_action"]
        if "forbid_actions" in step:
            assert result["receipt"]["action_id"] not in step["forbid_actions"]
        if "expected_errors" in step:
            assert step["expected_errors"].issubset(set(result["receipt"]["errors"]))
        if result["admitted"]:
            state = dict(result["applied_state"])
            previous_deltas = {
                key: int(state[key]) - int(before[key])
                for key in state
                if int(state[key]) != int(before[key])
            }
            trajectory_used = dict(result["trajectory_used_after"])
            last_update_epoch = 50 + (25 * index)
        else:
            assert result["applied_state"] == before
            state = before

        assert 0 <= state["fee_bps"] <= gov_gate.FEE_MAX_BPS
        assert 0 <= state["funding_cap_bps"] <= gov_gate.FUNDING_CAP_MAX_BPS
        assert (
            state["buyburn_bps"]
            + state["stakers_bps"]
            + state["reserve_bps"]
            + state["hosts_bps"]
            == gov_gate.SPLIT_SUM
        )
        assert gov_gate.RATIO_MIN_BPS <= state["mcr_bps"] <= state["ccr_bps"] <= gov_gate.RATIO_MAX_BPS
        assert state["staker_bps"] <= gov_gate.WHALE_STAKER_BPS_MAX

    assert observed[1]["receipt"]["action_id"] == "shift_router_to_buyburn_100"
    assert observed[1]["applied_state"]["fee_bps"] == observed[1]["committed_state"]["fee_bps"]
    assert observed[2]["reason"] == "receipt_rejected_noop"
    assert observed[-1]["applied_state"]["hosts_bps"] == 100


def test_surface_q_policy_anti_oscillation_skips_reversal_candidate() -> None:
    policy = {
        "schema": "zenodex.autonomous_governance.q_policy.v1",
        "policy_id": "anti_oscillation_test_policy",
        "version": 1,
        "safety": {
            "max_freshness_lag_epochs": 2,
            "max_divergence_bps": 75,
            "max_volatility_bps": 1_000,
            "min_liquidity_depth_bps": 1_000,
            "min_cooldown_epochs": 1,
            "emergency_pause": False,
        },
        "selection": {
            "mode": "first_admissible",
            "anti_oscillation": {
                "enabled": True,
                "parameters": ["fee_bps"],
            },
        },
        "state_bins": {
            "deviation_bps": [25, 100, 300],
            "volatility_bps": [50, 200, 500],
            "liquidity_depth_bps": [1_000, 3_000],
        },
        "actions": [
            {"id": "hold", "deltas": {}},
            {"id": "lower_fee_10", "deltas": {"fee_bps": -10}},
            {"id": "raise_fee_10", "deltas": {"fee_bps": 10}},
        ],
        "q_layers": [
            {
                "id": "joint",
                "features": ["deviation_bps", "volatility_bps", "liquidity_depth_bps"],
                "q_table": {"0|0|1": {"lower_fee_10": 10, "hold": 0, "raise_fee_10": -10}},
            }
        ],
    }
    policy["policy_hash"] = policy_content_hash_v1(policy)

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(),
        observation=_observation(
            observed_price_bps=10_000,
            target_price_bps=10_000,
            volatility_bps=25,
            liquidity_depth_bps=2_000,
        ),
        current_epoch=34,
        proposal_epoch=10,
        last_update_epoch=32,
        expected_policy_hash=policy["policy_hash"],
        previous_approved_deltas={"fee_bps": 10},
    )

    assert result["ok"] is True
    assert result["approved"] is True
    assert result["action_id"] == "hold"
    assert result["candidate_search"]["checked_count"] == 1
    assert result["candidate_search"]["gate_checked_count"] == 1
    assert result["candidate_search"]["selection_screened_count"] == 1
    assert result["candidate_search"]["candidate_considered_count"] == 2
    assert result["candidate_search"]["fallback_used"] is False
    assert result["candidate_search"]["raw_top_action_id"] == "lower_fee_10"
    assert result["candidate_search"]["selection_adjusted_top_action_id"] == "hold"
    assert result["candidate_search"]["raw_top_action_selection_screened"] is True
    assert result["candidate_search"]["rejected_candidates"][0] == {
        "action_id": "lower_fee_10",
        "failed_selection": ("anti_oscillation:fee_bps",),
    }
    assert result["candidate_search"]["selection_screened_candidates"][0] == {
        "action_id": "lower_fee_10",
        "failed_selection": ("anti_oscillation:fee_bps",),
    }


def test_surface_q_policy_trajectory_budget_skips_exhausted_candidate() -> None:
    policy = {
        "schema": "zenodex.autonomous_governance.q_policy.v1",
        "policy_id": "trajectory_budget_test_policy",
        "version": 1,
        "safety": {
            "max_freshness_lag_epochs": 2,
            "max_divergence_bps": 75,
            "max_volatility_bps": 1_000,
            "min_liquidity_depth_bps": 1_000,
            "min_cooldown_epochs": 1,
            "emergency_pause": False,
        },
        "selection": {
            "mode": "first_admissible",
            "trajectory_budget": {
                "enabled": True,
                "limits": {"fee_bps": 250},
            },
        },
        "state_bins": {
            "deviation_bps": [25, 100, 300],
            "volatility_bps": [50, 200, 500],
            "liquidity_depth_bps": [1_000, 3_000],
        },
        "actions": [
            {"id": "hold", "deltas": {}},
            {"id": "raise_fee_10", "deltas": {"fee_bps": 10}},
        ],
        "q_layers": [
            {
                "id": "joint",
                "features": ["deviation_bps", "volatility_bps", "liquidity_depth_bps"],
                "q_table": {"3|2|2": {"raise_fee_10": 10, "hold": 0}},
            }
        ],
    }
    policy["policy_hash"] = policy_content_hash_v1(policy)

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(),
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        last_update_epoch=32,
        expected_policy_hash=policy["policy_hash"],
        trajectory_used={"fee_bps": 250},
    )

    assert result["ok"] is True
    assert result["approved"] is True
    assert result["action_id"] == "hold"
    assert result["candidate_search"]["checked_count"] == 1
    assert result["candidate_search"]["gate_checked_count"] == 1
    assert result["candidate_search"]["selection_screened_count"] == 1
    assert result["candidate_search"]["candidate_considered_count"] == 2
    assert result["candidate_search"]["fallback_used"] is False
    assert result["candidate_search"]["raw_top_action_id"] == "raise_fee_10"
    assert result["candidate_search"]["selection_adjusted_top_action_id"] == "hold"
    assert result["candidate_search"]["raw_top_action_selection_screened"] is True
    assert result["candidate_search"]["rejected_candidates"][0] == {
        "action_id": "raise_fee_10",
        "failed_selection": ("trajectory_budget_exceeded:fee_bps",),
    }
    assert result["candidate_search"]["selection_screened_candidates"][0] == {
        "action_id": "raise_fee_10",
        "failed_selection": ("trajectory_budget_exceeded:fee_bps",),
    }


def test_surface_q_policy_cannot_loosen_hash_bound_trajectory_budget() -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()

    def evaluate_with_override(raw_budget: dict[str, int]) -> dict:
        return evaluate_autonomous_governance_surface_q_policy_v1(
            policy=policy,
            surface_state=_surface_state(),
            observation=_observation(),
            current_epoch=34,
            proposal_epoch=10,
            last_update_epoch=32,
            expected_policy_hash=policy["policy_hash"],
            trajectory_used={"fee_bps": 250},
            trajectory_budget=raw_budget,
        )

    default = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(),
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        last_update_epoch=32,
        expected_policy_hash=policy["policy_hash"],
        trajectory_used={"fee_bps": 250},
    )
    empty_override = evaluate_with_override({})
    loose_override = evaluate_with_override({"fee_bps": 1_000_000})

    for result in (default, empty_override, loose_override):
        assert result["ok"] is True
        assert result["approved"] is True
        assert result["action_id"] == "hold"
        assert result["proposed"] == result["surface_state"]
        assert result["trajectory_budget"]["fee_bps"] == 250
        assert result["candidate_search"]["raw_top_action_id"] == "raise_fee_10_tighten_funding_5"
        assert result["candidate_search"]["selection_adjusted_top_action_id"] == "hold"


def test_surface_q_policy_blocks_unsigned_underflow_after_delta() -> None:
    policy = _surface_policy_forcing_action("raise_fee_10_tighten_funding_5")

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(funding_cap_bps=0),
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["action_id"] == "raise_fee_10_tighten_funding_5"
    assert result["proposed"]["funding_cap_bps"] == -5
    assert result["governance_surface_gate_report"]["funding"] is False
    assert result["governance_surface_gate_report"]["master"] is True
    assert result["governance_surface_all_gates_ok"] is False
    assert "governance_surface_gate_rejected:funding" in result["errors"]
    assert result["approved"] is False


def test_surface_commit_hash_binds_trajectory_used_after_admitted_step() -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()
    policy = deepcopy(policy)
    policy["selection"] = {
        "mode": "first_admissible",
        "trajectory_budget": {
            "enabled": True,
            "limits": {"fee_bps": 250, "funding_cap_bps": 125},
        },
    }
    policy["policy_hash"] = policy_content_hash_v1(policy)

    result = commit_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(),
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        last_update_epoch=32,
        expected_policy_hash=policy["policy_hash"],
        trajectory_used={"fee_bps": 20, "funding_cap_bps": 7},
    )

    assert result["admitted"] is True
    assert result["applied_state"]["fee_bps"] == 40
    assert result["applied_state"]["funding_cap_bps"] == 115
    assert result["trajectory_used_after"] == {"fee_bps": 30, "funding_cap_bps": 12}

    body = {key: value for key, value in result.items() if key != "step_hash"}
    assert result["step_hash"] == hash_v0("autonomous_governance_q_surface_step_v1", body)
    tampered = deepcopy(body)
    tampered["trajectory_used_after"]["fee_bps"] = 31
    assert result["step_hash"] != hash_v0("autonomous_governance_q_surface_step_v1", tampered)


def test_surface_malformed_policy_returns_fail_closed_receipt() -> None:
    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=[],  # type: ignore[arg-type]
        surface_state=_surface_state(),
        observation=_observation(),
        current_epoch=34,
        proposal_epoch=10,
        expected_policy_hash="0x" + "00" * 32,
    )

    assert result["ok"] is False
    assert result["approved"] is False
    assert result["policy_hash"] == ""
    assert "policy_must_be_object" in result["errors"]
    assert "policy_hash_unavailable" in result["errors"]
    assert "policy_hash_mismatch" in result["errors"]


def test_live_surface_admission_matches_commit_for_valid_policy() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    request = {
        "policy": policy,
        "expected_policy_hash": policy["policy_hash"],
        "surface_state": _surface_state(fee_bps=300, funding_cap_bps=150),
        "observation": _next_observation(
            observed_price_bps=10_000,
            target_price_bps=10_000,
            volatility_bps=10,
            liquidity_depth_bps=4_000,
        ),
        "current_epoch": 50,
        "proposal_epoch": 10,
        "last_update_epoch": 48,
    }

    admission = admit_autonomous_governance_surface_request_v1(request)
    direct = commit_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=request["surface_state"],
        observation=request["observation"],
        current_epoch=request["current_epoch"],
        proposal_epoch=request["proposal_epoch"],
        last_update_epoch=request["last_update_epoch"],
        expected_policy_hash=policy["policy_hash"],
    )

    assert admission["ok"] is True
    assert admission["admitted"] is True
    assert admission["step_hash"] == direct["step_hash"]
    assert admission["applied_state"] == direct["applied_state"]
    assert admission["receipt"]["policy_hash"] == policy["policy_hash"]


def test_live_surface_admission_reports_receipt_rejection_as_not_ok() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    initial = _surface_state(fee_bps=300, funding_cap_bps=150)

    admission = admit_autonomous_governance_surface_request_v1(
        {
            "policy": policy,
            "expected_policy_hash": policy["policy_hash"],
            "surface_state": initial,
            "observation": _next_observation(oracle_confidence_bps=6_500),
            "current_epoch": 50,
            "proposal_epoch": 10,
            "last_update_epoch": 48,
        }
    )

    assert admission["ok"] is False
    assert admission["admitted"] is False
    assert admission["reason"] == "receipt_rejected_noop"
    assert admission["applied_state"] == initial
    assert "oracle_confidence_bps_below_min_oracle_confidence_bps" in admission["errors"]
    assert "oracle_confidence_bps_below_min_oracle_confidence_bps" in admission["receipt"]["errors"]


def test_live_surface_admission_requires_pinned_expected_policy_hash() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    initial = _surface_state(fee_bps=300, funding_cap_bps=150)

    admission = admit_autonomous_governance_surface_request_v1(
        {
            "policy": policy,
            "surface_state": initial,
            "observation": _next_observation(),
            "current_epoch": 50,
            "proposal_epoch": 10,
            "last_update_epoch": 48,
        }
    )

    assert admission["ok"] is False
    assert admission["admitted"] is False
    assert admission["reason"] == "admission_rejected_noop"
    assert admission["applied_state"] == initial
    assert admission["step"] == {}
    assert "expected_policy_hash_required" in admission["errors"]


def test_live_surface_admission_rejects_direct_result_field_bypass() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    initial = _surface_state(fee_bps=300, funding_cap_bps=150)
    injected = _surface_state(fee_bps=1_000, funding_cap_bps=0)

    admission = admit_autonomous_governance_surface_request_v1(
        {
            "policy": policy,
            "expected_policy_hash": policy["policy_hash"],
            "surface_state": initial,
            "observation": _next_observation(),
            "current_epoch": 50,
            "proposal_epoch": 10,
            "last_update_epoch": 48,
            "proposed_state": injected,
        }
    )

    assert admission["ok"] is False
    assert admission["admitted"] is False
    assert admission["reason"] == "admission_rejected_noop"
    assert admission["applied_state"] == initial
    assert admission["proposed_state"] == initial
    assert admission["forbidden_fields"] == ("proposed_state",)
    assert "direct_result_field_forbidden:proposed_state" in admission["errors"]


def test_autonomous_governance_q_policy_cli_sample_and_evaluate(tmp_path: Path) -> None:
    bundle = tmp_path / "bundle.json"
    sample = subprocess.run(
        [sys.executable, "tools/autonomous_governance_q_policy.py", "sample", "--output", str(bundle)],
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    evaluate = subprocess.run(
        [sys.executable, "tools/autonomous_governance_q_policy.py", "evaluate", str(bundle)],
        check=False,
        capture_output=True,
        text=True,
    )
    assert evaluate.returncode == 0, evaluate.stderr
    result = json.loads(evaluate.stdout)
    assert result["ok"] is True
    assert result["action_id"] == "raise_fee_10"
    assert result["revision_step"]["i1"] == 1


def test_autonomous_governance_q_policy_cli_surface_sample_and_evaluate(tmp_path: Path) -> None:
    bundle = tmp_path / "surface-bundle.json"
    sample = subprocess.run(
        [sys.executable, "tools/autonomous_governance_q_policy.py", "sample", "--surface", "--output", str(bundle)],
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr
    assert sample.stdout == ""

    evaluate = subprocess.run(
        [sys.executable, "tools/autonomous_governance_q_policy.py", "evaluate", str(bundle)],
        check=False,
        capture_output=True,
        text=True,
    )
    assert evaluate.returncode == 0, evaluate.stderr
    result = json.loads(evaluate.stdout)
    assert result["ok"] is True
    assert result["action_id"] == "raise_fee_10_tighten_funding_5"
    assert result["governance_surface_gate_report"]["master"] is True

    step = subprocess.run(
        [sys.executable, "tools/autonomous_governance_q_policy.py", "step", str(bundle)],
        check=False,
        capture_output=True,
        text=True,
    )
    assert step.returncode == 0, step.stderr
    step_result = json.loads(step.stdout)
    assert step_result["ok"] is True
    assert step_result["admitted"] is True
    assert step_result["applied_state"]["fee_bps"] == 40


def test_autonomous_governance_q_policy_cli_autogovnext_sample_and_step(tmp_path: Path) -> None:
    bundle = tmp_path / "autogovnext-bundle.json"
    sample = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "sample",
            "--surface",
            "--next",
            "--output",
            str(bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr

    data = json.loads(bundle.read_text(encoding="utf-8"))
    assert data["policy"]["policy_id"] == "sample_autogovnext_governance_surface_q_policy_v1"
    assert "oracle_confidence_bps" in data["observation"]

    step = subprocess.run(
        [sys.executable, "tools/autonomous_governance_q_policy.py", "step", str(bundle)],
        check=False,
        capture_output=True,
        text=True,
    )
    assert step.returncode == 0, step.stderr
    result = json.loads(step.stdout)
    assert result["ok"] is True
    assert result["admitted"] is True
    assert result["receipt"]["policy_hash"] == data["expected_policy_hash"]


def test_autonomous_governance_q_policy_cli_admit_rejects_bypass_field(tmp_path: Path) -> None:
    bundle = tmp_path / "autogovnext-bypass-bundle.json"
    sample = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "sample",
            "--surface",
            "--next",
            "--output",
            str(bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr

    data = json.loads(bundle.read_text(encoding="utf-8"))
    data["proposed_state"] = {**data["surface_state"], "fee_bps": 1_000}
    bundle.write_text(json.dumps(data, sort_keys=True), encoding="utf-8")

    admit = subprocess.run(
        [sys.executable, "tools/autonomous_governance_q_policy.py", "admit", str(bundle)],
        check=False,
        capture_output=True,
        text=True,
    )

    assert admit.returncode == 2
    result = json.loads(admit.stdout)
    assert result["ok"] is False
    assert result["admitted"] is False
    assert result["applied_state"] == data["surface_state"]
    assert result["forbidden_fields"] == ["proposed_state"]
    assert "direct_result_field_forbidden:proposed_state" in result["errors"]


def test_autonomous_governance_q_policy_cli_admit_rejects_receipt_noop(tmp_path: Path) -> None:
    bundle = tmp_path / "autogovnext-low-confidence-bundle.json"
    sample = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "sample",
            "--surface",
            "--next",
            "--output",
            str(bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr

    data = json.loads(bundle.read_text(encoding="utf-8"))
    data["observation"]["oracle_confidence_bps"] = 6_500
    bundle.write_text(json.dumps(data, sort_keys=True), encoding="utf-8")

    admit = subprocess.run(
        [sys.executable, "tools/autonomous_governance_q_policy.py", "admit", str(bundle)],
        check=False,
        capture_output=True,
        text=True,
    )

    assert admit.returncode == 2
    result = json.loads(admit.stdout)
    assert result["ok"] is False
    assert result["admitted"] is False
    assert result["reason"] == "receipt_rejected_noop"
    assert result["applied_state"] == data["surface_state"]
    assert "oracle_confidence_bps_below_min_oracle_confidence_bps" in result["errors"]
    assert "oracle_confidence_bps_below_min_oracle_confidence_bps" in result["receipt"]["errors"]
