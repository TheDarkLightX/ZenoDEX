"""Deterministic autonomous-governance artifacts for tools and tests only.

These constructors deliberately live outside ``src``.  They provide example
data to the operator CLI and test suite, while the production modules retain
the authoritative normalization, hashing, evaluation, and admission logic.
"""

from __future__ import annotations

from copy import deepcopy
from typing import Any

from src.integration.autonomous_governance_ebrm_policy import (
    AUTONOMOUS_GOVERNANCE_EBRM_POLICY_SCHEMA_V1,
)
from src.integration.autonomous_governance_pi_policy import (
    AUTONOMOUS_GOVERNANCE_PI_POLICY_SCHEMA_V1,
)
from src.integration.autonomous_governance_q_policy import (
    AUTONOMOUS_GOVERNANCE_Q_POLICY_SCHEMA_V1,
    policy_content_hash_v1,
)


def sample_autonomous_governance_q_policy_v1() -> dict[str, Any]:
    """Return a small deterministic Q-policy artifact."""

    policy = {
        "schema": AUTONOMOUS_GOVERNANCE_Q_POLICY_SCHEMA_V1,
        "policy_id": "sample_fee_pressure_q_policy_v1",
        "version": 1,
        "safety": {
            "max_freshness_lag_epochs": 2,
            "max_divergence_bps": 75,
            "max_volatility_bps": 1_000,
            "min_liquidity_depth_bps": 1_000,
            "min_cooldown_epochs": 1,
            "emergency_pause": False,
        },
        "state_bins": {
            "deviation_bps": [25, 100, 300],
            "volatility_bps": [50, 200, 500],
            "liquidity_depth_bps": [1_000, 3_000],
        },
        "actions": [
            {"id": "hold", "deltas": {}},
            {"id": "lower_fee_5", "deltas": {"fee": -5}},
            {"id": "raise_fee_5", "deltas": {"fee": 5}},
            {"id": "raise_fee_10", "deltas": {"fee": 10}},
        ],
        "q_layers": [
            {
                "id": "price_deviation_pressure",
                "features": ["deviation_bps"],
                "q_table": {
                    "0": {"lower_fee_5": 3, "hold": 1},
                    "1": {"hold": 3, "raise_fee_5": 1},
                    "2": {"raise_fee_5": 6, "hold": 1},
                    "3": {"raise_fee_10": 10, "raise_fee_5": 5},
                },
            },
            {
                "id": "volatility_pressure",
                "features": ["volatility_bps"],
                "q_table": {
                    "0": {"hold": 1},
                    "1": {"raise_fee_5": 1},
                    "2": {"raise_fee_5": 3},
                    "3": {"raise_fee_10": 4},
                },
            },
            {
                "id": "liquidity_depth_bias",
                "features": ["liquidity_depth_bps"],
                "q_table": {
                    "0": {"raise_fee_10": 2},
                    "1": {"raise_fee_5": 1},
                    "2": {"hold": 1},
                },
            },
        ],
    }
    return {**policy, "policy_hash": policy_content_hash_v1(policy)}


def sample_autonomous_governance_surface_q_policy_v1() -> dict[str, Any]:
    """Return a Q-policy targeting the verified governance surfaces."""

    policy = {
        "schema": AUTONOMOUS_GOVERNANCE_Q_POLICY_SCHEMA_V1,
        "policy_id": "sample_governance_surface_q_policy_v1",
        "version": 1,
        "safety": {
            "max_freshness_lag_epochs": 2,
            "max_divergence_bps": 75,
            "max_volatility_bps": 1_000,
            "min_liquidity_depth_bps": 1_000,
            "min_cooldown_epochs": 1,
            "emergency_pause": False,
        },
        "state_bins": {
            "deviation_bps": [25, 100, 300],
            "volatility_bps": [50, 200, 500],
            "liquidity_depth_bps": [1_000, 3_000],
        },
        "actions": [
            {"id": "hold", "deltas": {}},
            {"id": "raise_fee_10", "deltas": {"fee_bps": 10}},
            {
                "id": "raise_fee_10_tighten_funding_5",
                "deltas": {"fee_bps": 10, "funding_cap_bps": -5},
            },
            {
                "id": "shift_router_to_reserve_100",
                "deltas": {"buyburn_bps": -100, "reserve_bps": 100},
            },
        ],
        "q_layers": [
            {
                "id": "price_deviation_pressure",
                "features": ["deviation_bps"],
                "q_table": {
                    "0": {"hold": 3},
                    "1": {"hold": 3, "raise_fee_10": 1},
                    "2": {"raise_fee_10": 5, "hold": 1},
                    "3": {
                        "raise_fee_10_tighten_funding_5": 9,
                        "raise_fee_10": 4,
                    },
                },
            },
            {
                "id": "volatility_pressure",
                "features": ["volatility_bps"],
                "q_table": {
                    "0": {"hold": 1},
                    "1": {"raise_fee_10": 1},
                    "2": {"raise_fee_10_tighten_funding_5": 3},
                    "3": {"raise_fee_10_tighten_funding_5": 6},
                },
            },
            {
                "id": "liquidity_depth_bias",
                "features": ["liquidity_depth_bps"],
                "q_table": {
                    "0": {"raise_fee_10_tighten_funding_5": 2},
                    "1": {"raise_fee_10": 1},
                    "2": {"hold": 1},
                },
            },
        ],
    }
    return {**policy, "policy_hash": policy_content_hash_v1(policy)}


def sample_autonomous_governance_next_policy_v1() -> dict[str, Any]:
    """Return a deterministic AutoGovNEXT policy candidate."""

    policy = deepcopy(sample_autonomous_governance_surface_q_policy_v1())
    policy.pop("policy_hash", None)
    policy["policy_id"] = "sample_autogovnext_governance_surface_q_policy_v1"
    policy["version"] = 2
    policy["safety"] = {**dict(policy["safety"]), **_autogovnext_safety()}
    policy["selection"] = _autogovnext_selection()
    policy["state_bins"] = {
        **dict(policy["state_bins"]),
        **_autogovnext_state_bins(),
    }
    policy["actions"] = [*list(policy["actions"]), *_autogovnext_actions()]
    policy["q_layers"] = [*list(policy["q_layers"]), *_autogovnext_q_layers()]
    return {**policy, "policy_hash": policy_content_hash_v1(policy)}


def _autogovnext_safety() -> dict[str, int]:
    return {
        "min_oracle_confidence_bps": 7_000,
        "max_liquidity_concentration_bps": 9_500,
        "max_recent_governance_churn_bps": 8,
        "min_proof_market_health_bps": 1_000,
        "max_validator_stress_bps": 8_000,
        "max_network_stress_bps": 8_000,
    }


def _autogovnext_selection() -> dict[str, Any]:
    return {
        "mode": "first_admissible",
        "anti_oscillation": {
            "enabled": True,
            "parameters": [
                "fee_bps",
                "funding_cap_bps",
                "buyburn_bps",
                "reserve_bps",
                "hosts_bps",
            ],
        },
        "trajectory_budget": {
            "enabled": True,
            "limits": {
                "fee_bps": 250,
                "funding_cap_bps": 125,
                "buyburn_bps": 1_000,
                "reserve_bps": 1_000,
                "hosts_bps": 1_000,
            },
        },
    }


def _autogovnext_state_bins() -> dict[str, list[int]]:
    return {
        "fee_bps": [50, 200, 500, 990, 1_000],
        "funding_cap_bps": [0, 5, 120, 190, 200],
        "reserve_bps": [0, 2_500, 7_500, 9_000, 9_900, 10_000],
        "hosts_bps": [0, 500, 2_500, 5_000, 10_000],
        "oracle_confidence_bps": [7_000, 9_000, 9_800],
        "liquidity_concentration_bps": [2_500, 5_000, 7_500, 9_500],
        "recent_governance_churn_bps": [0, 2, 5, 8],
        "proof_market_health_bps": [1_000, 5_000, 8_000, 9_500],
        "validator_stress_bps": [500, 2_000, 5_000, 8_000],
        "network_stress_bps": [500, 2_000, 5_000, 8_000],
    }


def _autogovnext_actions() -> list[dict[str, Any]]:
    return [
        {"id": "lower_fee_10", "deltas": {"fee_bps": -10}},
        {
            "id": "lower_fee_10_relax_funding_5",
            "deltas": {"fee_bps": -10, "funding_cap_bps": 5},
        },
        {"id": "relax_funding_5", "deltas": {"funding_cap_bps": 5}},
        {
            "id": "shift_router_reserve_to_hosts_100",
            "deltas": {"reserve_bps": -100, "hosts_bps": 100},
        },
        {
            "id": "shift_router_hosts_to_reserve_100",
            "deltas": {"hosts_bps": -100, "reserve_bps": 100},
        },
        {
            "id": "shift_router_reserve_to_buyburn_100",
            "deltas": {"reserve_bps": -100, "buyburn_bps": 100},
        },
    ]


def _autogovnext_q_layers() -> list[dict[str, Any]]:
    return [
        _autogovnext_calm_fee_layer(),
        _autogovnext_proof_market_layer(),
        _autogovnext_concentration_layer(),
        _autogovnext_stress_freeze_layer(),
    ]


def _autogovnext_calm_fee_layer() -> dict[str, Any]:
    return {
        "id": "autogovnext_calm_fee_normalization_v1",
        "features": [
            "deviation_bps",
            "volatility_bps",
            "liquidity_depth_bps",
            "oracle_confidence_bps",
            "proof_market_health_bps",
            "validator_stress_bps",
            "network_stress_bps",
            "recent_governance_churn_bps",
            "fee_bps",
            "funding_cap_bps",
        ],
        "q_table": {
            "*": {},
            "0|0|2|3|4|0|0|0|2|3": {
                "lower_fee_10_relax_funding_5": 120,
                "lower_fee_10": 80,
                "relax_funding_5": 35,
                "hold": -20,
            },
            "0|0|2|3|4|0|0|0|2|4": {
                "lower_fee_10_relax_funding_5": 120,
                "lower_fee_10": 80,
                "relax_funding_5": 35,
                "hold": -20,
            },
        },
    }


def _autogovnext_proof_market_layer() -> dict[str, Any]:
    return {
        "id": "autogovnext_proof_market_router_rebalance_v1",
        "features": ["proof_market_health_bps", "reserve_bps", "hosts_bps"],
        "q_table": {
            "*": {},
            "0|4|0": {"shift_router_reserve_to_hosts_100": 140, "hold": -20},
            "1|4|0": {"shift_router_reserve_to_hosts_100": 120, "hold": -10},
            "4|4|0": {"shift_router_reserve_to_buyburn_100": 90, "hold": 10},
            "4|1|3": {"shift_router_hosts_to_reserve_100": 70, "hold": 10},
        },
    }


def _autogovnext_concentration_layer() -> dict[str, Any]:
    return {
        "id": "autogovnext_concentration_reserve_bias_v1",
        "features": ["liquidity_concentration_bps", "liquidity_depth_bps"],
        "q_table": {
            "*": {},
            "3|0": {"shift_router_to_reserve_100": 80, "hold": -10},
            "4|0": {"shift_router_to_reserve_100": 100, "hold": -20},
        },
    }


def _autogovnext_stress_freeze_layer() -> dict[str, Any]:
    return {
        "id": "autogovnext_stress_freeze_v1",
        "features": [
            "validator_stress_bps",
            "network_stress_bps",
            "recent_governance_churn_bps",
        ],
        "q_table": {
            "*": {},
            **{
                f"{validator_bin}|{network_bin}|{churn_bin}": {
                    "hold": 220,
                    "raise_fee_10": -40,
                    "raise_fee_10_tighten_funding_5": -60,
                    "lower_fee_10": -60,
                    "lower_fee_10_relax_funding_5": -80,
                    "relax_funding_5": -80,
                }
                for validator_bin in (2, 3)
                for network_bin in (2, 3)
                for churn_bin in range(5)
            },
        },
    }


def sample_autonomous_governance_pi_policy_v1() -> dict[str, Any]:
    """Return a deterministic PI-policy artifact."""

    return {
        "schema": AUTONOMOUS_GOVERNANCE_PI_POLICY_SCHEMA_V1,
        "surface": "fee_bps",
        "setpoint": 0,
        "kp_num": 1,
        "kp_den": 4,
        "ki_num": 1,
        "ki_den": 8,
        "deadband": 2,
        "out_lo": 0,
        "out_hi": 1000,
    }


def sample_autonomous_governance_ebrm_policy_v1() -> dict[str, Any]:
    """Return a deterministic EBRM-policy artifact."""

    return {
        "schema": AUTONOMOUS_GOVERNANCE_EBRM_POLICY_SCHEMA_V1,
        "policy_id": "sample_fee_deviation_ebrm_policy_v1",
        "version": 1,
        "surface": "fee_bps",
        "features": ["deviation_bps"],
        "feature_bounds": {"deviation_bps": {"min": 0, "max": 1_000}},
        "state_bins": {"deviation_bps": [25, 100, 300]},
        "energy_model": {
            "targets": {"0": 30, "1": 35, "2": 50, "3": 67},
            "w_track": 1,
            "w_move": 0,
        },
    }
