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
)
from src.tau_specs.governance import gov_gate
from tools.support.autonomous_governance_policy_samples import (
    sample_autonomous_governance_next_policy_v1,
    sample_autonomous_governance_q_policy_v1,
    sample_autonomous_governance_surface_q_policy_v1,
)


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
    policy = sample_autonomous_governance_surface_q_policy_v1()
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
    policy = sample_autonomous_governance_surface_q_policy_v1()

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
    policy = sample_autonomous_governance_surface_q_policy_v1()
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


def test_surface_q_policy_first_admissible_falls_back_to_hold_at_fee_cap() -> None:
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
    assert result["candidate_search"]["fallback_used"] is True
    assert result["candidate_search"]["rejected_candidates"][0]["action_id"] == "raise_fee_10_tighten_funding_5"
    assert result["candidate_search"]["rejected_candidates"][0]["failed_gates"] == ("fee", "master")


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
        observation=_observation(observed_price_bps=10_000, target_price_bps=10_000, volatility_bps=25, liquidity_depth_bps=2_000),
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
    assert result["candidate_search"]["selection_screened_count"] == 0
    assert result["candidate_search"]["selection_penalized_count"] == 1
    assert result["candidate_search"]["candidate_considered_count"] == 1
    assert result["candidate_search"]["fallback_used"] is False
    assert result["candidate_search"]["raw_top_action_id"] == "lower_fee_10"
    assert result["candidate_search"]["selection_adjusted_top_action_id"] == "hold"
    assert result["candidate_search"]["raw_top_action_selection_screened"] is True
    assert result["candidate_search"]["rejected_candidates"] == ()
    assert result["candidate_search"]["selection_screened_candidates"] == ()
    assert result["candidate_search"]["selection_penalized_candidates"][0] == {
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
    assert result["candidate_search"]["selection_screened_count"] == 0
    assert result["candidate_search"]["selection_penalized_count"] == 1
    assert result["candidate_search"]["candidate_considered_count"] == 1
    assert result["candidate_search"]["fallback_used"] is False
    assert result["candidate_search"]["raw_top_action_id"] == "raise_fee_10"
    assert result["candidate_search"]["selection_adjusted_top_action_id"] == "hold"
    assert result["candidate_search"]["raw_top_action_selection_screened"] is True
    assert result["candidate_search"]["rejected_candidates"] == ()
    assert result["candidate_search"]["selection_screened_candidates"] == ()
    assert result["candidate_search"]["selection_penalized_candidates"][0] == {
        "action_id": "raise_fee_10",
        "failed_selection": ("trajectory_budget_exceeded:fee_bps",),
    }


def test_surface_q_policy_blocks_unsigned_underflow_after_delta() -> None:
    policy = sample_autonomous_governance_surface_q_policy_v1()

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


def test_autogovnext_policy_cannot_touch_authority_parameters() -> None:
    policy = deepcopy(sample_autonomous_governance_next_policy_v1())
    policy["actions"].append(
        {
            "id": "rotate_verifier_keys",
            "deltas": {
                "verifier_image_id": 1,
                "signer_set_hash": 1,
            },
        }
    )
    policy["policy_hash"] = policy_content_hash_v1(policy)

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(fee_bps=300, funding_cap_bps=150),
        observation=_next_observation(),
        current_epoch=50,
        proposal_epoch=10,
        last_update_epoch=48,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is False
    assert result["approved"] is False
    assert "authority_action_delta_forbidden:verifier_image_id" in result["errors"]
    assert "authority_action_delta_forbidden:signer_set_hash" in result["errors"]


def test_autogovnext_policy_rejects_malformed_anti_oscillation_parameter() -> None:
    policy = deepcopy(sample_autonomous_governance_next_policy_v1())
    policy["selection"]["anti_oscillation"]["parameters"].append(["fee_bps"])
    policy["policy_hash"] = policy_content_hash_v1(policy)

    result = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=_surface_state(fee_bps=300, funding_cap_bps=150),
        observation=_next_observation(),
        current_epoch=50,
        proposal_epoch=10,
        last_update_epoch=48,
        expected_policy_hash=policy["policy_hash"],
    )

    assert result["ok"] is False
    assert result["approved"] is False
    assert "anti_oscillation_parameter_invalid:['fee_bps']" in result["errors"]


def test_autogovnext_live_admission_matches_commit_for_valid_policy() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    request = {
        "schema": "zenodex.autonomous_governance.q_surface_policy_eval_bundle.v1",
        "tx_id": "autogovnext-valid-1",
        "time_ms": 1_800_000_000_000,
        "policy": policy,
        "expected_policy_hash": policy["policy_hash"],
        "surface_state": _surface_state(fee_bps=300, funding_cap_bps=150),
        "observation": _next_observation(),
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
    assert admission["receipt"]["action_id"] == "lower_fee_10_relax_funding_5"
    assert admission["applied_state"]["fee_bps"] == 290
    assert admission["applied_state"]["funding_cap_bps"] == 155
    assert "does_not_authorize_settlement" in admission["not_claimed"]


def test_autogovnext_live_admission_reports_receipt_rejection_as_not_ok() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    initial = _surface_state(fee_bps=300, funding_cap_bps=150)

    admission = admit_autonomous_governance_surface_request_v1(
        {
            "policy": policy,
            "expected_policy_hash": policy["policy_hash"],
            "surface_state": initial,
            "observation": _next_observation(oracle_confidence_bps=6_999),
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


def test_autogovnext_live_admission_requires_canonical_expected_policy_hash() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    initial = _surface_state(fee_bps=300, funding_cap_bps=150)

    admission = admit_autonomous_governance_surface_request_v1(
        {
            "policy": policy,
            "expected_policy_hash": "not-a-root",
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
    assert "expected_policy_hash_invalid" in admission["errors"]


def test_autogovnext_live_admission_rejects_direct_result_field_bypass() -> None:
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


def test_autogovnext_live_admission_rejects_unknown_request_field() -> None:
    policy = sample_autonomous_governance_next_policy_v1()
    initial = _surface_state(fee_bps=300, funding_cap_bps=150)

    admission = admit_autonomous_governance_surface_request_v1(
        {
            "policy": policy,
            "expected_policy_hash": policy["policy_hash"],
            "surface_state": initial,
            "observation": _next_observation(),
            "current_epoch": 50,
            "proposal_epoch": 10,
            "last_update_epoch": 48,
            "model_says_approved": True,
        }
    )

    assert admission["ok"] is False
    assert admission["admitted"] is False
    assert admission["unknown_fields"] == ("model_says_approved",)
    assert "unknown_admission_request_field:model_says_approved" in admission["errors"]


def test_autogovnext_live_admission_rejects_unrenderable_unknown_field() -> None:
    class UnrenderableField:
        def __str__(self) -> str:
            raise RuntimeError("field-name-boom")

        def __repr__(self) -> str:
            raise RuntimeError("field-name-boom")

    policy = sample_autonomous_governance_next_policy_v1()
    initial = _surface_state(fee_bps=300, funding_cap_bps=150)

    admission = admit_autonomous_governance_surface_request_v1(
        {
            "policy": policy,
            "expected_policy_hash": policy["policy_hash"],
            "surface_state": initial,
            "observation": _next_observation(),
            "current_epoch": 50,
            "proposal_epoch": 10,
            "last_update_epoch": 48,
            UnrenderableField(): True,
        }
    )

    assert admission["ok"] is False
    assert admission["admitted"] is False
    assert admission["unknown_fields"] == ("<unrenderable>",)
    assert "unknown_admission_request_field:<unrenderable>" in admission["errors"]


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


def test_autonomous_governance_q_policy_cli_autogovnext_sample_and_admit(tmp_path: Path) -> None:
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
    assert sample.stdout == ""

    data = json.loads(bundle.read_text(encoding="utf-8"))
    assert data["policy"]["policy_id"] == "sample_autogovnext_governance_surface_q_policy_v1"
    assert "oracle_confidence_bps" in data["observation"]

    admit = subprocess.run(
        [sys.executable, "tools/autonomous_governance_q_policy.py", "admit", str(bundle)],
        check=False,
        capture_output=True,
        text=True,
    )
    assert admit.returncode == 0, admit.stderr
    result = json.loads(admit.stdout)
    assert result["ok"] is True
    assert result["admitted"] is True
    assert result["receipt"]["policy_hash"] == data["expected_policy_hash"]
    assert result["receipt"]["action_id"] == "raise_fee_10_tighten_funding_5"


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
