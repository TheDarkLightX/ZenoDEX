#!/usr/bin/env python3
"""Generate and replay an autonomous-governance Q-policy artifact.

The factory is offline tooling. It may call Julia and EBRM-style optimizers, but
the runtime governance path consumes only the frozen policy JSON and rechecks it
with deterministic Python/Tau governance gates.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import shutil
import subprocess
import sys
from collections import Counter
from datetime import datetime, timezone
from itertools import product
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.autonomous_governance_q_policy import (  # noqa: E402
    evaluate_autonomous_governance_surface_q_policy_v1,
    policy_content_hash_v1,
)
from src.tau_specs.governance import gov_gate  # noqa: E402


FACTORY_SCHEMA = "zenodex.autonomous_governance.policy_factory_report.v1"
FACTORY_COVERAGE_SCHEMA = "zenodex.autonomous_governance.policy_factory_coverage_profile.v1"
ARTIFACT_CHECK_SCHEMA = "zenodex.autonomous_governance.policy_artifact_check.v1"
EBR_TRAINING_CORPUS_SCHEMA = "zenodex.autonomous_governance.ebr_training_corpus.v1"
EBR_TRAINING_RANKING_SCHEMA = "zenodex.autonomous_governance.ebr_training_ranking_diagnostics.v1"
EBR_TRAINING_PAIRWISE_SCHEMA = "zenodex.autonomous_governance.ebr_training_pairwise_diagnostics.v1"
EBR_TRAINING_SUPERVISION_SCHEMA = "zenodex.autonomous_governance.ebr_training_supervision_targets.v1"
EBR_TRAINING_ENTROPY_SCHEMA = "zenodex.autonomous_governance.ebr_training_entropy_diagnostics.v1"
EBR_TRAINING_SPLIT_SCHEMA = "zenodex.autonomous_governance.ebr_training_split_diagnostics.v1"
EBR_TRAINING_FEATURE_SCHEMA = "zenodex.autonomous_governance.ebr_training_feature_contract.v1"
EBR_TRAINING_DIVERSITY_SCHEMA = "zenodex.autonomous_governance.ebr_training_diversity_diagnostics.v1"
EBR_RESIDUAL_MODEL_SCHEMA = "zenodex.autonomous_governance.ebr_residual_lookup_model.v1"
ACTION_GATE_DIAGNOSTICS_SCHEMA = "zenodex.autonomous_governance.action_gate_diagnostics.v1"
ENVIRONMENT_CURRICULUM_SCHEMA = "zenodex.autonomous_governance.environment_curriculum_diagnostics.v1"
SAFETY_BOUNDARY_SWEEP_SCHEMA = "zenodex.autonomous_governance.safety_boundary_sweep.v1"
SAFETY_INTERACTION_SWEEP_SCHEMA = "zenodex.autonomous_governance.safety_interaction_sweep.v1"
SURFACE_BOUNDARY_SWEEP_SCHEMA = "zenodex.autonomous_governance.surface_boundary_sweep.v1"
MAX_JSON_BYTES = 20_000_000
ENTROPY_TEMPERATURE_SCORE = 100
VALIDATION_STRIDE_CANDIDATE_GROUPS = 5
VALIDATION_STRIDE_SINGLETON_GROUPS = 2
TRAINED_EBR_RESIDUAL_LAYER_ID = "trained_ebr_residual_train_split_v1"
TRAINED_EBR_RESIDUAL_LAYER_FEATURES = (
    "deviation_bps",
    "volatility_bps",
    "liquidity_depth_bps",
    "fee_bps",
    "funding_cap_bps",
    "buyburn_bps",
    "reserve_bps",
)
TRAINED_EBR_RESIDUAL_LAYER_BIN_COUNTS = {
    "deviation_bps": 4,
    "volatility_bps": 4,
    "liquidity_depth_bps": 3,
    "fee_bps": 4,
    "funding_cap_bps": 3,
    "buyburn_bps": 4,
    "reserve_bps": 4,
}
TRAINED_EBR_RESIDUAL_SCORE_CLAMP = 320
TRAINED_EBR_RESIDUAL_SCORE_SCALE = 2
TRAINED_EBR_RESIDUAL_NEUTRAL_EDGE_PRIOR_PENALTY = 320
TRAINED_EBR_RESIDUAL_CROSS_SEED_STRIDE = 5
TRAINED_EBR_RESIDUAL_CROSS_SEED_SALTS = (
    "seed0",
    "seed1",
    "seed2",
    "seed3",
    "seed4",
    "seed5",
    "seed6",
)

REQUIRED_SURFACE_VARIANTS = (
    "base",
    "fee_cap_edge",
    "funding_floor_edge",
    "router_reserve_edge",
    "combined_edge",
)

REQUIRED_SAFETY_LANES = (
    "stale_oracle",
    "high_divergence",
    "high_volatility",
    "cooldown_not_elapsed",
    "timelock_not_met",
    "policy_hash_mismatch",
)

REQUIRED_NEGATIVE_CONTROLS = (
    "fee_step_over_50",
    "fee_cap_over_1000",
    "funding_underflow",
    "router_sum_break",
    "collateral_order_break",
    "whale_step_over_500",
)

REQUIRED_SEQUENCE_CASES = (
    "persistent_high_deviation",
    "calm_fee_floor",
    "router_edge_pressure",
    "alternating_pressure",
    "funding_floor_pressure",
    "safety_interrupt",
    "trajectory_safety_interrupt",
    "trajectory_budget_walk",
    "router_budget_walk",
    "router_recovery_walk",
)

REQUIRED_INTRABIN_PROBES = (
    "bin_floor",
    "bin_ceiling",
)

REQUIRED_SAFETY_BOUNDARY_PROBES = (
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
)

SAFETY_BOUNDARY_BIN_ANCHORS = (
    (0, 0, 0),
    (0, 3, 2),
    (1, 1, 1),
    (1, 3, 0),
    (2, 0, 2),
    (2, 2, 1),
    (3, 1, 0),
    (3, 3, 2),
)

SAFETY_INTERACTION_CONTROLS = (
    "freshness",
    "divergence",
    "volatility",
    "liquidity",
    "cooldown",
)

SAFETY_INTERACTION_PROFILES = (
    "both_inside",
    "first_outside",
    "second_outside",
    "both_outside",
)

SAFETY_INTERACTION_BIN_ANCHORS = (
    (0, 0, 0),
    (1, 3, 0),
    (2, 2, 1),
    (3, 3, 2),
)

REQUIRED_SURFACE_BOUNDARY_PROFILES = (
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
)

CANDIDATE_TRAINING_SOURCES = (
    "normal_grid",
    "intra_bin_stress",
    "sequence_step",
    "safety_boundary_sweep",
    "safety_interaction_sweep",
    "surface_boundary_sweep",
)

SEQUENCE_DRIFT_LIMITS = {
    "fee_bps": 250,
    "buyburn_bps": 1_000,
    "stakers_bps": 1_000,
    "reserve_bps": 1_000,
    "hosts_bps": 1_000,
    "mcr_bps": 2_000,
    "ccr_bps": 2_000,
    "staker_bps": 1_000,
    "funding_cap_bps": 125,
}
SURFACE_FEATURE_FIELDS = tuple(SEQUENCE_DRIFT_LIMITS)
OBSERVATION_FEATURE_FIELDS = (
    "observed_price_bps",
    "target_price_bps",
    "deviation_bps",
    "volatility_bps",
    "divergence_bps",
    "freshness_lag_epochs",
    "liquidity_depth_bps",
)
STATE_BIN_FEATURE_FIELDS = (
    "deviation_bps",
    "volatility_bps",
    "liquidity_depth_bps",
    "fee_bps",
    "funding_cap_bps",
    "buyburn_bps",
    "reserve_bps",
)
EBR_FEATURE_NAMES = (
    ("source_code", "action_code", "probe_code")
    + tuple(f"bin:{field}" for field in STATE_BIN_FEATURE_FIELDS)
    + tuple(f"obs:{field}" for field in OBSERVATION_FEATURE_FIELDS)
    + tuple(f"surface:{field}" for field in SURFACE_FEATURE_FIELDS)
    + tuple(f"delta:{field}" for field in SURFACE_FEATURE_FIELDS)
    + ("policy_score", "policy_rank")
)
FORBIDDEN_FEATURE_NAME_TOKENS = (
    "accepted",
    "approved",
    "error",
    "failure",
    "frontier",
    "gate",
    "label",
    "regret",
    "split",
    "target",
    "utility",
)
ALLOWED_FEATURE_NAME_TOKEN_EXCEPTIONS = (
    "obs:target_price_bps",
)
FEATURE_CONTRACT_ALLOWED_SOURCES = (
    "source",
    "action_id",
    "probe",
    "state_bins",
    "observation",
    "surface_state",
    "deltas",
    "policy_score",
    "policy_rank",
)
FEATURE_CONTRACT_FORBIDDEN_SOURCES = (
    "label",
    "approved",
    "all_gates_ok",
    "utility",
    "failure_family",
    "errors",
    "gate_report",
    "target_class",
    "frontier_action_id",
    "frontier_utility",
    "is_frontier",
    "utility_regret_to_frontier",
    "score_gap_to_frontier",
    "rank_gap_to_frontier",
    "split",
)

REQUIRED_REJECTION_ERRORS = (
    "governance_surface_gate_rejected:fee",
    "governance_surface_gate_rejected:router",
    "governance_surface_gate_rejected:collateral",
    "governance_surface_gate_rejected:whale",
    "governance_surface_gate_rejected:funding",
    "governance_surface_gate_rejected:master",
    "freshness_lag_epochs_exceeds_max_freshness_lag_epochs",
    "divergence_bps_exceeds_max_divergence_bps",
    "volatility_bps_exceeds_max_volatility_bps",
    "liquidity_depth_below_minimum",
    "cooldown_not_elapsed",
    "policy_hash_mismatch",
)
SOFT_FUNDING_RETAINED_FLOOR_BPS = 10

GENERATOR_FILES = (
    "tools/autonomous_governance_policy_factory.py",
    "tools/autonomous_governance_q_table_optimize.jl",
    "src/integration/autonomous_governance_q_policy.py",
    "src/integration/autonomous_governance_trajectory.py",
    "src/integration/autonomous_governance_session.py",
    "src/integration/autonomous_governance_policy_pin.py",
    "src/integration/autonomous_governance_session_pin.py",
    "src/integration/autonomous_governance_session_store.py",
    "src/integration/autonomous_governance_session_store_file.py",
    "src/integration/autonomous_governance_live_apply.py",
    "src/integration/zeno_governance_authority.py",
    "src/integration/zenodex_external_threshold_bls.py",
    "src/integration/autonomous_governance_hostile_input.py",
    "src/tau_specs/governance/gov_gate.py",
)


def _utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat()


def _load_json(path: Path) -> dict[str, Any]:
    if path.stat().st_size > MAX_JSON_BYTES:
        raise ValueError(f"json_input_too_large:{path}:{path.stat().st_size}>{MAX_JSON_BYTES}")
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"json_input_must_be_object:{path}")
    return data


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _json_normalized(value: Any) -> Any:
    return json.loads(json.dumps(value, sort_keys=True))


def _sha256_json(value: Any) -> str:
    body = json.dumps(_json_normalized(value), separators=(",", ":"), sort_keys=True).encode("utf-8")
    return "0x" + hashlib.sha256(body).hexdigest()


def _sha256_file(path: Path) -> str:
    return "0x" + hashlib.sha256(path.read_bytes()).hexdigest()


def _source_manifest() -> list[dict[str, Any]]:
    manifest: list[dict[str, Any]] = []
    for rel in GENERATOR_FILES:
        path = ROOT / rel
        manifest.append(
            {
                "path": rel,
                "exists": path.exists(),
                "sha256": _sha256_file(path) if path.exists() else "",
                "bytes": path.stat().st_size if path.exists() else 0,
            }
        )
    return manifest


def _run_julia_optimizer(*, julia_bin: str, policy_path: Path, report_path: Path) -> dict[str, Any]:
    if shutil.which(julia_bin) is None:
        raise RuntimeError(f"julia_not_found:{julia_bin}")
    cmd = [
        julia_bin,
        str(ROOT / "tools" / "autonomous_governance_q_table_optimize.jl"),
        "--policy-output",
        str(policy_path),
        "--report-output",
        str(report_path),
        "--quiet",
    ]
    proc = subprocess.run(cmd, check=False, capture_output=True, text=True, timeout=180)
    return {
        "command": cmd,
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "ok": proc.returncode == 0 and policy_path.exists() and report_path.exists(),
    }


def _freeze_policy(policy: Mapping[str, Any]) -> dict[str, Any]:
    frozen = copy.deepcopy(dict(policy))
    frozen["policy_hash"] = policy_content_hash_v1(frozen)
    return frozen


def _hold_only_policy(policy: Mapping[str, Any]) -> dict[str, Any]:
    hold = copy.deepcopy(dict(policy))
    hold["policy_id"] = f"{policy.get('policy_id', 'policy')}.hold_only_baseline"
    action_ids = [str(action.get("id", "")) for action in hold.get("actions", [])]
    for layer in hold.get("q_layers", []):
        table = layer.get("q_table", {})
        if not isinstance(table, dict):
            continue
        for key in list(table):
            table[key] = {action_id: (0 if action_id == "hold" else -1_000_000) for action_id in action_ids}
    return _freeze_policy(hold)


def _pid_like_policy(policy: Mapping[str, Any]) -> dict[str, Any]:
    """Return a deterministic PID-shaped baseline encoded as the same Q schema."""

    pid = copy.deepcopy(dict(policy))
    pid["policy_id"] = f"{policy.get('policy_id', 'policy')}.pid_like_baseline"
    action_ids = [str(action.get("id", "")) for action in pid.get("actions", [])]
    action_set = set(action_ids)

    def available(preferred: str) -> str:
        if preferred in action_set:
            return preferred
        return "hold" if "hold" in action_set else action_ids[0]

    def choose_joint_action(key: str) -> str:
        try:
            deviation_bin, volatility_bin, liquidity_bin = (int(part) for part in key.split("|"))
        except ValueError:
            return available("hold")
        if (
            deviation_bin >= 3
            and volatility_bin >= 2
            and liquidity_bin == 0
            and "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100" in action_set
        ):
            return "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100"
        if (
            deviation_bin >= 2
            and volatility_bin <= 1
            and liquidity_bin == 0
            and "raise_fee_10_shift_router_to_reserve_100" in action_set
        ):
            return "raise_fee_10_shift_router_to_reserve_100"
        if (
            deviation_bin == 0
            and volatility_bin == 0
            and liquidity_bin == 0
            and "lower_fee_10_relax_funding_5_shift_router_to_reserve_100" in action_set
        ):
            return "lower_fee_10_relax_funding_5_shift_router_to_reserve_100"
        if deviation_bin >= 3 and volatility_bin >= 2 and "raise_fee_10_tighten_funding_5" in action_set:
            return "raise_fee_10_tighten_funding_5"
        if deviation_bin >= 2 and "raise_fee_10" in action_set:
            return "raise_fee_10"
        if deviation_bin == 0 and volatility_bin == 0 and "lower_fee_10_relax_funding_5" in action_set:
            return "lower_fee_10_relax_funding_5"
        if liquidity_bin == 0 and "shift_router_to_reserve_100" in action_set:
            return "shift_router_to_reserve_100"
        return available("hold")

    def choose_single_feature_action(feature: str, key: str) -> str:
        try:
            bin_index = int(key)
        except ValueError:
            return available("hold")
        if feature == "deviation_bps":
            if bin_index >= 2:
                return available("raise_fee_10")
            if bin_index == 0:
                return available("lower_fee_10_relax_funding_5")
        if feature == "volatility_bps":
            if bin_index >= 2:
                return available("raise_fee_10_tighten_funding_5")
            if bin_index == 0:
                return available("lower_fee_10_relax_funding_5")
        if feature == "liquidity_depth_bps" and bin_index == 0:
            return available("shift_router_to_reserve_100")
        return available("hold")

    def forced_row(selected: str) -> dict[str, int]:
        return {action_id: (-1_000 if action_id != selected else 1_000) for action_id in action_ids}

    for layer in pid.get("q_layers", []):
        features = tuple(str(feature) for feature in layer.get("features", ()))
        table = layer.get("q_table", {})
        if not isinstance(table, dict):
            continue
        if features == ("deviation_bps", "volatility_bps", "liquidity_depth_bps"):
            for key in list(table):
                table[key] = forced_row(choose_joint_action(str(key)))
            continue
        if len(features) == 1 and features[0] in {
            "deviation_bps",
            "volatility_bps",
            "liquidity_depth_bps",
        }:
            for key in list(table):
                table[key] = forced_row(choose_single_feature_action(features[0], str(key)))
            continue
        # Preserve state-edge guard layers so the baseline remains bounded by
        # the same deterministic envelope near fee, funding, and router limits.
        for key in list(table):
            if table[key] is None:
                table[key] = {}
    return _freeze_policy(pid)


def _forced_delta_policy(
    policy: Mapping[str, Any],
    *,
    policy_id_suffix: str,
    action_id: str,
    deltas: Mapping[str, int],
    replace_actions: bool = False,
) -> dict[str, Any]:
    forced = copy.deepcopy(dict(policy))
    forced["policy_id"] = f"{policy.get('policy_id', 'policy')}.{policy_id_suffix}"
    forced["selection"] = {"mode": "top_scored"}
    actions = [] if replace_actions else list(forced.get("actions", []))
    actions.append({"id": action_id, "deltas": dict(deltas)})
    forced["actions"] = actions
    action_ids = [str(action.get("id", "")) for action in actions]
    for layer in forced.get("q_layers", []):
        table = layer.get("q_table", {})
        if not isinstance(table, dict):
            continue
        for key in list(table):
            table[key] = {candidate_id: (-1_000_000 if candidate_id != action_id else 1_000_000) for candidate_id in action_ids}
    return _freeze_policy(forced)


def _forced_existing_action_policy(policy: Mapping[str, Any], *, action_id: str) -> dict[str, Any]:
    forced = copy.deepcopy(dict(policy))
    forced["policy_id"] = f"{policy.get('policy_id', 'policy')}.candidate_{action_id}"
    forced["selection"] = {"mode": "top_scored"}
    action_ids = [str(action.get("id", "")) for action in forced.get("actions", [])]
    if action_id not in action_ids:
        raise ValueError(f"unknown_action_id:{action_id}")
    for layer in forced.get("q_layers", []):
        table = layer.get("q_table", {})
        if not isinstance(table, dict):
            continue
        for key in list(table):
            table[key] = {candidate_id: (-1_000_000 if candidate_id != action_id else 1_000_000) for candidate_id in action_ids}
    return _freeze_policy(forced)


def _surface_state_variants() -> list[dict[str, Any]]:
    base = _base_surface_state()
    variants = [
        ("base", {}),
        ("fee_cap_edge", {"fee_bps": 995}),
        ("funding_floor_edge", {"funding_cap_bps": 0}),
        ("router_reserve_edge", {"buyburn_bps": 0, "reserve_bps": 10_000, "hosts_bps": 0}),
        (
            "combined_edge",
            {
                "fee_bps": 995,
                "funding_cap_bps": 0,
                "buyburn_bps": 0,
                "reserve_bps": 10_000,
                "hosts_bps": 0,
            },
        ),
    ]
    out: list[dict[str, Any]] = []
    for name, overrides in variants:
        state = dict(base)
        state.update(overrides)
        out.append({"id": name, "state": state})
    return out


def _base_surface_state() -> dict[str, int]:
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


def _observation_for_bins(deviation_bin: int, volatility_bin: int, liquidity_bin: int) -> dict[str, int]:
    deviation_reps = (0, 50, 200, 500)
    volatility_reps = (25, 100, 250, 750)
    liquidity_reps = (500, 2_000, 5_000)
    return _observation_for_values(
        deviation_bps=deviation_reps[deviation_bin],
        volatility_bps=volatility_reps[volatility_bin],
        liquidity_depth_bps=liquidity_reps[liquidity_bin],
    )


def _observation_for_values(
    *,
    deviation_bps: int,
    volatility_bps: int,
    liquidity_depth_bps: int,
) -> dict[str, int]:
    target = 10_000
    return {
        "observed_price_bps": target + deviation_bps,
        "target_price_bps": target,
        "volatility_bps": volatility_bps,
        "divergence_bps": 10,
        "freshness_lag_epochs": 0,
        "liquidity_depth_bps": liquidity_depth_bps,
    }


def _bin_bounds(thresholds: tuple[int, ...], bin_index: int, *, top_value: int) -> tuple[int, int]:
    lower = 0 if bin_index == 0 else thresholds[bin_index - 1] + 1
    upper = thresholds[bin_index] if bin_index < len(thresholds) else top_value
    return lower, upper


def _intra_bin_probe_values(
    *,
    deviation_bin: int,
    volatility_bin: int,
    liquidity_bin: int,
    probe: str,
) -> dict[str, int]:
    deviation_lower, deviation_upper = _bin_bounds((25, 100, 300), deviation_bin, top_value=1_000)
    volatility_lower, volatility_upper = _bin_bounds((50, 200, 500), volatility_bin, top_value=1_000)
    liquidity_lower, liquidity_upper = _bin_bounds((1_000, 3_000), liquidity_bin, top_value=6_000)
    liquidity_lower = max(1_000, liquidity_lower)
    liquidity_upper = max(1_000, liquidity_upper)

    if probe == "bin_floor":
        return {
            "deviation_bps": deviation_lower,
            "volatility_bps": volatility_lower,
            "liquidity_depth_bps": liquidity_lower,
        }
    if probe == "bin_ceiling":
        return {
            "deviation_bps": deviation_upper,
            "volatility_bps": volatility_upper,
            "liquidity_depth_bps": liquidity_upper,
        }
    raise ValueError(f"unknown_intra_bin_probe:{probe}")


def _scenarios() -> list[dict[str, Any]]:
    scenarios: list[dict[str, Any]] = []
    for deviation_bin in range(4):
        for volatility_bin in range(4):
            for liquidity_bin in range(3):
                bin_key = f"{deviation_bin}|{volatility_bin}|{liquidity_bin}"
                observation = _observation_for_bins(deviation_bin, volatility_bin, liquidity_bin)
                for variant in _surface_state_variants():
                    scenarios.append(
                        {
                            "id": f"{bin_key}:{variant['id']}",
                            "bin_key": bin_key,
                            "deviation_bin": deviation_bin,
                            "volatility_bin": volatility_bin,
                            "liquidity_bin": liquidity_bin,
                            "surface_variant": variant["id"],
                            "surface_state": variant["state"],
                            "observation": observation,
                        }
                    )
    return scenarios


def _intra_bin_stress_scenarios() -> list[dict[str, Any]]:
    scenarios: list[dict[str, Any]] = []
    for deviation_bin in range(4):
        for volatility_bin in range(4):
            for liquidity_bin in range(3):
                bin_key = f"{deviation_bin}|{volatility_bin}|{liquidity_bin}"
                for probe in REQUIRED_INTRABIN_PROBES:
                    values = _intra_bin_probe_values(
                        deviation_bin=deviation_bin,
                        volatility_bin=volatility_bin,
                        liquidity_bin=liquidity_bin,
                        probe=probe,
                    )
                    observation = _observation_for_values(**values)
                    for variant in _surface_state_variants():
                        scenarios.append(
                            {
                                "id": f"{bin_key}:{probe}:{variant['id']}",
                                "bin_key": bin_key,
                                "expected_bins": {
                                    "deviation_bps": deviation_bin,
                                    "volatility_bps": volatility_bin,
                                    "liquidity_depth_bps": liquidity_bin,
                                },
                                "deviation_bin": deviation_bin,
                                "volatility_bin": volatility_bin,
                                "liquidity_bin": liquidity_bin,
                                "probe": probe,
                                "probe_values": values,
                                "surface_variant": variant["id"],
                                "surface_state": variant["state"],
                                "observation": observation,
                            }
                        )
    return scenarios


def _safety_lanes() -> list[dict[str, Any]]:
    base_observation = _observation_for_bins(3, 2, 2)
    base_state = _base_surface_state()

    def lane(
        lane_id: str,
        *,
        observation_overrides: Mapping[str, int] | None = None,
        current_epoch: int = 34,
        proposal_epoch: int = 10,
        last_update_epoch: int | None = 32,
        expected_policy_hash: str = "policy",
        expected_error: str,
    ) -> dict[str, Any]:
        observation = dict(base_observation)
        observation.update(observation_overrides or {})
        return {
            "id": lane_id,
            "surface_state": dict(base_state),
            "observation": observation,
            "current_epoch": current_epoch,
            "proposal_epoch": proposal_epoch,
            "last_update_epoch": last_update_epoch,
            "expected_policy_hash": expected_policy_hash,
            "expected_error": expected_error,
        }

    return [
        lane(
            "stale_oracle",
            observation_overrides={"freshness_lag_epochs": 3},
            expected_error="freshness_lag_epochs_exceeds_max_freshness_lag_epochs",
        ),
        lane(
            "high_divergence",
            observation_overrides={"divergence_bps": 76},
            expected_error="divergence_bps_exceeds_max_divergence_bps",
        ),
        lane(
            "high_volatility",
            observation_overrides={"volatility_bps": 1_001},
            expected_error="volatility_bps_exceeds_max_volatility_bps",
        ),
        lane(
            "cooldown_not_elapsed",
            last_update_epoch=34,
            expected_error="cooldown_not_elapsed",
        ),
        lane(
            "timelock_not_met",
            current_epoch=20,
            proposal_epoch=10,
            last_update_epoch=18,
            expected_error="governance_surface_gate_rejected:fee",
        ),
        lane(
            "policy_hash_mismatch",
            expected_policy_hash="0x" + "00" * 32,
            expected_error="policy_hash_mismatch",
        ),
    ]


def _policy_bin_index(value: int, thresholds: tuple[int, ...]) -> int:
    index = 0
    for threshold in thresholds:
        if value > threshold:
            index += 1
    return index


def _observation_bin_fields(observation: Mapping[str, int]) -> dict[str, int]:
    deviation = abs(int(observation["observed_price_bps"]) - int(observation["target_price_bps"]))
    return {
        "deviation_bps": _policy_bin_index(deviation, (25, 100, 300)),
        "volatility_bps": _policy_bin_index(int(observation["volatility_bps"]), (50, 200, 500)),
        "liquidity_depth_bps": _policy_bin_index(int(observation["liquidity_depth_bps"]), (1_000, 3_000)),
    }


def _safety_boundary_scenarios() -> list[dict[str, Any]]:
    """Return stratified just-inside/just-outside safety-boundary scenarios."""

    base_state = _base_surface_state()
    scenarios: list[dict[str, Any]] = []
    for deviation_bin, volatility_bin, liquidity_bin in SAFETY_BOUNDARY_BIN_ANCHORS:
        anchor_key = f"{deviation_bin}|{volatility_bin}|{liquidity_bin}"
        base_observation = _observation_for_bins(deviation_bin, volatility_bin, liquidity_bin)
        for probe in REQUIRED_SAFETY_BOUNDARY_PROBES:
            observation = dict(base_observation)
            if probe != "liquidity_below_floor":
                observation["liquidity_depth_bps"] = max(1_000, observation["liquidity_depth_bps"])
            current_epoch = 34
            proposal_epoch = 10
            last_update_epoch: int | None = 32
            expected_error = ""
            status = "inside"
            if probe == "freshness_at_limit":
                observation["freshness_lag_epochs"] = 2
            elif probe == "freshness_over_limit":
                observation["freshness_lag_epochs"] = 3
                expected_error = "freshness_lag_epochs_exceeds_max_freshness_lag_epochs"
                status = "outside"
            elif probe == "divergence_at_limit":
                observation["divergence_bps"] = 75
            elif probe == "divergence_over_limit":
                observation["divergence_bps"] = 76
                expected_error = "divergence_bps_exceeds_max_divergence_bps"
                status = "outside"
            elif probe == "volatility_at_limit":
                observation["volatility_bps"] = 1_000
            elif probe == "volatility_over_limit":
                observation["volatility_bps"] = 1_001
                expected_error = "volatility_bps_exceeds_max_volatility_bps"
                status = "outside"
            elif probe == "liquidity_at_floor":
                observation["liquidity_depth_bps"] = 1_000
            elif probe == "liquidity_below_floor":
                observation["liquidity_depth_bps"] = 999
                expected_error = "liquidity_depth_below_minimum"
                status = "outside"
            elif probe == "cooldown_at_limit":
                last_update_epoch = 33
            elif probe == "cooldown_under_limit":
                last_update_epoch = 34
                expected_error = "cooldown_not_elapsed"
                status = "outside"
            else:
                raise ValueError(f"unknown_safety_boundary_probe:{probe}")

            bins = _observation_bin_fields(observation)
            scenarios.append(
                {
                    "id": f"{anchor_key}:{probe}",
                    "anchor_bin_key": anchor_key,
                    "bin_key": (
                        f"{bins['deviation_bps']}|"
                        f"{bins['volatility_bps']}|"
                        f"{bins['liquidity_depth_bps']}"
                    ),
                    "deviation_bin": bins["deviation_bps"],
                    "volatility_bin": bins["volatility_bps"],
                    "liquidity_bin": bins["liquidity_depth_bps"],
                    "probe": probe,
                    "status": status,
                    "surface_state": dict(base_state),
                    "observation": observation,
                    "current_epoch": current_epoch,
                    "proposal_epoch": proposal_epoch,
                    "last_update_epoch": last_update_epoch,
                    "expected_error": expected_error,
                }
            )
    return scenarios


def _safety_interaction_error(control: str) -> str:
    return {
        "freshness": "freshness_lag_epochs_exceeds_max_freshness_lag_epochs",
        "divergence": "divergence_bps_exceeds_max_divergence_bps",
        "volatility": "volatility_bps_exceeds_max_volatility_bps",
        "liquidity": "liquidity_depth_below_minimum",
        "cooldown": "cooldown_not_elapsed",
    }[control]


def _apply_safety_interaction_control(
    *,
    control: str,
    outside: bool,
    observation: dict[str, int],
    timing: dict[str, int | None],
) -> None:
    if control == "freshness":
        observation["freshness_lag_epochs"] = 3 if outside else 2
    elif control == "divergence":
        observation["divergence_bps"] = 76 if outside else 75
    elif control == "volatility":
        observation["volatility_bps"] = 1_001 if outside else 1_000
    elif control == "liquidity":
        observation["liquidity_depth_bps"] = 999 if outside else 1_000
    elif control == "cooldown":
        timing["last_update_epoch"] = 34 if outside else 33
    else:
        raise ValueError(f"unknown_safety_interaction_control:{control}")


def _safety_interaction_scenarios() -> list[dict[str, Any]]:
    """Return paired just-inside/just-outside safety interaction scenarios."""

    base_state = _base_surface_state()
    control_pairs = tuple(
        (first, second)
        for index, first in enumerate(SAFETY_INTERACTION_CONTROLS)
        for second in SAFETY_INTERACTION_CONTROLS[index + 1 :]
    )
    scenarios: list[dict[str, Any]] = []
    for deviation_bin, volatility_bin, liquidity_bin in SAFETY_INTERACTION_BIN_ANCHORS:
        anchor_key = f"{deviation_bin}|{volatility_bin}|{liquidity_bin}"
        base_observation = _observation_for_bins(deviation_bin, volatility_bin, liquidity_bin)
        for first, second in control_pairs:
            for profile in SAFETY_INTERACTION_PROFILES:
                observation = dict(base_observation)
                if first != "liquidity" and second != "liquidity":
                    observation["liquidity_depth_bps"] = max(1_000, observation["liquidity_depth_bps"])
                timing: dict[str, int | None] = {
                    "current_epoch": 34,
                    "proposal_epoch": 10,
                    "last_update_epoch": 32,
                }
                first_outside = profile in {"first_outside", "both_outside"}
                second_outside = profile in {"second_outside", "both_outside"}
                _apply_safety_interaction_control(
                    control=first,
                    outside=first_outside,
                    observation=observation,
                    timing=timing,
                )
                _apply_safety_interaction_control(
                    control=second,
                    outside=second_outside,
                    observation=observation,
                    timing=timing,
                )
                expected_errors: list[str] = []
                if first_outside:
                    expected_errors.append(_safety_interaction_error(first))
                if second_outside:
                    expected_errors.append(_safety_interaction_error(second))
                bins = _observation_bin_fields(observation)
                pair_id = f"{first}+{second}"
                scenarios.append(
                    {
                        "id": f"{anchor_key}:{pair_id}:{profile}",
                        "anchor_bin_key": anchor_key,
                        "bin_key": (
                            f"{bins['deviation_bps']}|"
                            f"{bins['volatility_bps']}|"
                            f"{bins['liquidity_depth_bps']}"
                        ),
                        "deviation_bin": bins["deviation_bps"],
                        "volatility_bin": bins["volatility_bps"],
                        "liquidity_bin": bins["liquidity_depth_bps"],
                        "control_pair": pair_id,
                        "first_control": first,
                        "second_control": second,
                        "profile": profile,
                        "probe": f"{pair_id}:{profile}",
                        "status": "inside" if not expected_errors else "outside",
                        "surface_state": dict(base_state),
                        "observation": observation,
                        "current_epoch": int(timing["current_epoch"] or 0),
                        "proposal_epoch": int(timing["proposal_epoch"] or 0),
                        "last_update_epoch": timing["last_update_epoch"],
                        "expected_errors": tuple(expected_errors),
                    }
                )
    return scenarios


def _surface_boundary_scenarios() -> list[dict[str, Any]]:
    """Return just-inside and exact-limit governance-surface scenarios."""

    base_state = _base_surface_state()

    def state_with(**overrides: int) -> dict[str, int]:
        state = dict(base_state)
        state.update(overrides)
        return state

    specs = (
        {
            "id": "fee_floor_inside",
            "surface_state": state_with(fee_bps=10),
            "bin_tuple": (0, 0, 2),
            "boundary_family": "fee",
            "expected_rejection_error": "",
            "limit_status": "inside",
        },
        {
            "id": "fee_floor_at_limit",
            "surface_state": state_with(fee_bps=0),
            "bin_tuple": (0, 0, 2),
            "boundary_family": "fee",
            "expected_rejection_error": "governance_surface_gate_rejected:fee",
            "limit_status": "at_limit",
        },
        {
            "id": "fee_cap_inside",
            "surface_state": state_with(fee_bps=990),
            "bin_tuple": (3, 2, 2),
            "boundary_family": "fee",
            "expected_rejection_error": "",
            "limit_status": "inside",
        },
        {
            "id": "fee_cap_at_limit",
            "surface_state": state_with(fee_bps=1_000),
            "bin_tuple": (3, 2, 2),
            "boundary_family": "fee",
            "expected_rejection_error": "governance_surface_gate_rejected:fee",
            "limit_status": "at_limit",
        },
        {
            "id": "funding_floor_inside",
            "surface_state": state_with(funding_cap_bps=5),
            "bin_tuple": (3, 2, 2),
            "boundary_family": "funding",
            "expected_rejection_error": "",
            "limit_status": "inside",
        },
        {
            "id": "funding_floor_at_limit",
            "surface_state": state_with(funding_cap_bps=0),
            "bin_tuple": (3, 2, 2),
            "boundary_family": "funding",
            "expected_rejection_error": "governance_surface_gate_rejected:funding",
            "limit_status": "at_limit",
        },
        {
            "id": "funding_cap_inside",
            "surface_state": state_with(funding_cap_bps=195),
            "bin_tuple": (0, 0, 2),
            "boundary_family": "funding",
            "expected_rejection_error": "",
            "limit_status": "inside",
        },
        {
            "id": "funding_cap_at_limit",
            "surface_state": state_with(funding_cap_bps=200),
            "bin_tuple": (0, 0, 2),
            "boundary_family": "funding",
            "expected_rejection_error": "governance_surface_gate_rejected:funding",
            "limit_status": "at_limit",
        },
        {
            "id": "reserve_cap_inside",
            "surface_state": state_with(buyburn_bps=100, reserve_bps=9_900, hosts_bps=0),
            "bin_tuple": (3, 2, 2),
            "boundary_family": "router",
            "expected_rejection_error": "",
            "limit_status": "inside",
        },
        {
            "id": "reserve_cap_at_limit",
            "surface_state": state_with(buyburn_bps=0, reserve_bps=10_000, hosts_bps=0),
            "bin_tuple": (3, 2, 2),
            "boundary_family": "router",
            "expected_rejection_error": "governance_surface_gate_rejected:router",
            "limit_status": "at_limit",
        },
        {
            "id": "buyburn_cap_inside",
            "surface_state": state_with(buyburn_bps=9_900, reserve_bps=100, hosts_bps=0),
            "bin_tuple": (0, 0, 2),
            "boundary_family": "router",
            "expected_rejection_error": "",
            "limit_status": "inside",
        },
        {
            "id": "buyburn_cap_at_limit",
            "surface_state": state_with(buyburn_bps=10_000, reserve_bps=0, hosts_bps=0),
            "bin_tuple": (0, 0, 2),
            "boundary_family": "router",
            "expected_rejection_error": "governance_surface_gate_rejected:router",
            "limit_status": "at_limit",
        },
    )

    scenarios: list[dict[str, Any]] = []
    for spec in specs:
        deviation_bin, volatility_bin, liquidity_bin = spec["bin_tuple"]
        observation = _observation_for_bins(deviation_bin, volatility_bin, liquidity_bin)
        observation["liquidity_depth_bps"] = max(3_001, observation["liquidity_depth_bps"])
        bins = _observation_bin_fields(observation)
        scenarios.append(
            {
                "id": str(spec["id"]),
                "profile": str(spec["id"]),
                "probe": str(spec["id"]),
                "boundary_family": str(spec["boundary_family"]),
                "limit_status": str(spec["limit_status"]),
                "bin_key": (
                    f"{bins['deviation_bps']}|"
                    f"{bins['volatility_bps']}|"
                    f"{bins['liquidity_depth_bps']}"
                ),
                "deviation_bin": bins["deviation_bps"],
                "volatility_bin": bins["volatility_bps"],
                "liquidity_bin": bins["liquidity_depth_bps"],
                "surface_state": dict(spec["surface_state"]),
                "observation": observation,
                "current_epoch": 34,
                "proposal_epoch": 10,
                "last_update_epoch": 32,
                "expected_rejection_error": str(spec["expected_rejection_error"]),
            }
        )
    return scenarios


def _expected_candidate_group_count() -> int:
    return (
        len(_scenarios())
        + len(_intra_bin_stress_scenarios())
        + sum(len(case["bin_path"]) for case in _sequence_cases())
        + len(_safety_boundary_scenarios())
        + len(_safety_interaction_scenarios())
        + len(_surface_boundary_scenarios())
    )


def _expected_total_group_count() -> int:
    return (
        _expected_candidate_group_count()
        + len(REQUIRED_NEGATIVE_CONTROLS)
        + len(REQUIRED_SAFETY_LANES)
    )


def _negative_controls(policy: Mapping[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "id": "fee_step_over_50",
            "policy": _forced_delta_policy(
                policy,
                policy_id_suffix="negative_fee_step_over_50",
                action_id="negative_fee_step_over_50",
                deltas={"fee_bps": 100},
                replace_actions=True,
            ),
            "expected_error": "governance_surface_gate_rejected:fee",
        },
        {
            "id": "fee_cap_over_1000",
            "policy": _forced_delta_policy(
                policy,
                policy_id_suffix="negative_fee_cap_over_1000",
                action_id="negative_fee_cap_over_1000",
                deltas={"fee_bps": 1_000},
                replace_actions=True,
            ),
            "expected_error": "governance_surface_gate_rejected:fee",
        },
        {
            "id": "funding_underflow",
            "policy": _forced_delta_policy(
                policy,
                policy_id_suffix="negative_funding_underflow",
                action_id="negative_funding_underflow",
                deltas={"funding_cap_bps": -500},
                replace_actions=True,
            ),
            "expected_error": "governance_surface_gate_rejected:funding",
        },
        {
            "id": "router_sum_break",
            "policy": _forced_delta_policy(
                policy,
                policy_id_suffix="negative_router_sum_break",
                action_id="negative_router_sum_break",
                deltas={"reserve_bps": 100},
                replace_actions=True,
            ),
            "expected_error": "governance_surface_gate_rejected:router",
        },
        {
            "id": "collateral_order_break",
            "policy": _forced_delta_policy(
                policy,
                policy_id_suffix="negative_collateral_order_break",
                action_id="negative_collateral_order_break",
                deltas={"mcr_bps": 5_000},
                replace_actions=True,
            ),
            "expected_error": "governance_surface_gate_rejected:collateral",
        },
        {
            "id": "whale_step_over_500",
            "policy": _forced_delta_policy(
                policy,
                policy_id_suffix="negative_whale_step_over_500",
                action_id="negative_whale_step_over_500",
                deltas={"staker_bps": 1_000},
                replace_actions=True,
            ),
            "expected_error": "governance_surface_gate_rejected:whale",
        },
    ]


def _sequence_cases() -> list[dict[str, Any]]:
    base = _base_surface_state()
    calm_edge = dict(base)
    calm_edge.update({"fee_bps": 20, "funding_cap_bps": 190})
    router_edge = dict(base)
    router_edge.update({"buyburn_bps": 100, "reserve_bps": 9_900, "hosts_bps": 0})
    funding_edge = dict(base)
    funding_edge.update({"funding_cap_bps": 15})

    return [
        {
            "id": "persistent_high_deviation",
            "surface_state": dict(base),
            "bin_path": [(3, 2, 2)] * 8,
        },
        {
            "id": "calm_fee_floor",
            "surface_state": calm_edge,
            "bin_path": [(0, 0, 1)] * 6,
        },
        {
            "id": "router_edge_pressure",
            "surface_state": router_edge,
            "bin_path": [(0, 1, 0)] * 5,
        },
        {
            "id": "alternating_pressure",
            "surface_state": dict(base),
            "bin_path": [(3, 2, 2), (0, 0, 1)] * 4,
        },
        {
            "id": "funding_floor_pressure",
            "surface_state": funding_edge,
            "bin_path": [(3, 2, 2)] * 6,
        },
        {
            "id": "safety_interrupt",
            "surface_state": dict(base),
            "bin_path": [(3, 2, 2), (3, 2, 2), (3, 2, 2), (3, 2, 2)],
            "observation_overrides_by_step": {
                1: {"freshness_lag_epochs": 3},
                2: {"divergence_bps": 76},
            },
        },
        {
            "id": "trajectory_budget_walk",
            "surface_state": dict(base),
            "bin_path": [(3, 2, 2)] * 30,
        },
        {
            "id": "trajectory_safety_interrupt",
            "surface_state": dict(base),
            "bin_path": [(3, 2, 2)] * 32,
            "observation_overrides_by_step": {
                6: {"liquidity_depth_bps": 999},
                7: {"freshness_lag_epochs": 3},
                13: {"divergence_bps": 76},
                19: {"volatility_bps": 1_001},
            },
        },
        {
            "id": "router_budget_walk",
            "surface_state": dict(base),
            "bin_path": [(0, 1, 0)] * 14,
            "observation_overrides_by_step": {
                index: {"liquidity_depth_bps": 1_000}
                for index in range(14)
            },
        },
        {
            "id": "router_recovery_walk",
            "surface_state": {
                **dict(base),
                "buyburn_bps": 0,
                "reserve_bps": 10_000,
                "hosts_bps": 0,
            },
            "bin_path": [(0, 0, 2)] * 14,
        },
    ]


def _surface_state_safety_errors(state: Mapping[str, Any]) -> tuple[str, ...]:
    errors: list[str] = []
    for key in (
        "fee_bps",
        "buyburn_bps",
        "stakers_bps",
        "reserve_bps",
        "hosts_bps",
        "mcr_bps",
        "ccr_bps",
        "staker_bps",
        "funding_cap_bps",
    ):
        value = state.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0 or value > gov_gate.U16_MAX:
            errors.append(f"surface_state_domain_invalid:{key}")
    if not errors:
        if not 0 <= int(state["fee_bps"]) <= gov_gate.FEE_MAX_BPS:
            errors.append("surface_state_fee_out_of_bounds")
        router_values = (
            int(state["buyburn_bps"]),
            int(state["stakers_bps"]),
            int(state["reserve_bps"]),
            int(state["hosts_bps"]),
        )
        if any(value > gov_gate.SPLIT_SHARE_MAX for value in router_values):
            errors.append("surface_state_router_share_out_of_bounds")
        if sum(router_values) != gov_gate.SPLIT_SUM:
            errors.append("surface_state_router_sum_invalid")
        if not gov_gate.RATIO_MIN_BPS <= int(state["mcr_bps"]) <= int(state["ccr_bps"]):
            errors.append("surface_state_collateral_order_invalid")
        if int(state["ccr_bps"]) > gov_gate.RATIO_MAX_BPS:
            errors.append("surface_state_ccr_out_of_bounds")
        if int(state["staker_bps"]) > gov_gate.WHALE_STAKER_BPS_MAX:
            errors.append("surface_state_staker_bps_out_of_bounds")
        if int(state["funding_cap_bps"]) > gov_gate.FUNDING_CAP_MAX_BPS:
            errors.append("surface_state_funding_cap_out_of_bounds")
    return tuple(errors)


def _governance_gate_report_for_states(
    *,
    current: Mapping[str, int],
    proposed: Mapping[str, int],
    proposal_epoch: int,
    current_epoch: int,
) -> dict[str, bool]:
    """Mirror the runtime governance surface gate report for artifact diagnostics."""

    required = (
        "fee_bps",
        "buyburn_bps",
        "stakers_bps",
        "reserve_bps",
        "hosts_bps",
        "mcr_bps",
        "ccr_bps",
        "staker_bps",
        "funding_cap_bps",
    )
    if any(name not in current or name not in proposed for name in required):
        return {
            "fee": False,
            "router": False,
            "collateral": False,
            "whale": False,
            "funding": False,
            "master": False,
        }
    master = gov_gate.MasterRevision(
        approved=True,
        exec_req=True,
        proposal_ts=proposal_epoch,
        current_ts=current_epoch,
        fee_curr_bps=current["fee_bps"],
        fee_next_bps=proposed["fee_bps"],
        buyburn_next_bps=proposed["buyburn_bps"],
        stakers_next_bps=proposed["stakers_bps"],
        reserve_next_bps=proposed["reserve_bps"],
        hosts_next_bps=proposed["hosts_bps"],
        buyburn_curr_bps=current["buyburn_bps"],
        stakers_curr_bps=current["stakers_bps"],
        reserve_curr_bps=current["reserve_bps"],
        hosts_curr_bps=current["hosts_bps"],
        mcr_curr_bps=current["mcr_bps"],
        mcr_next_bps=proposed["mcr_bps"],
        ccr_curr_bps=current["ccr_bps"],
        ccr_next_bps=proposed["ccr_bps"],
        staker_bps_curr=current["staker_bps"],
        staker_bps_next=proposed["staker_bps"],
    )
    return {
        "fee": gov_gate.fee_revision_ok(
            True, True, proposal_epoch, current_epoch, current["fee_bps"], proposed["fee_bps"]
        ),
        "router": gov_gate.router_revision_ok(
            True,
            True,
            proposal_epoch,
            current_epoch,
            proposed["buyburn_bps"],
            proposed["stakers_bps"],
            proposed["reserve_bps"],
            proposed["hosts_bps"],
            current["buyburn_bps"],
            current["stakers_bps"],
            current["reserve_bps"],
            current["hosts_bps"],
        ),
        "collateral": gov_gate.collateral_ratio_revision_ok(
            True,
            True,
            proposal_epoch,
            current_epoch,
            current["mcr_bps"],
            proposed["mcr_bps"],
            current["ccr_bps"],
            proposed["ccr_bps"],
        ),
        "whale": gov_gate.whale_defense_revision_ok(
            True, True, proposal_epoch, current_epoch, current["staker_bps"], proposed["staker_bps"]
        ),
        "funding": gov_gate.funding_rate_revision_ok(
            True,
            True,
            proposal_epoch,
            current_epoch,
            current["funding_cap_bps"],
            proposed["funding_cap_bps"],
        ),
        "master": gov_gate.master_revision_ok(master),
    }


def _action_gate_diagnostics(policy: Mapping[str, Any]) -> dict[str, Any]:
    """Check every frozen action against the canonical committed governance envelope."""

    base_state = _base_surface_state()
    base_state_errors = _surface_state_safety_errors(base_state)
    action_deltas = _action_map(policy)
    action_ids = _action_ids(policy)
    action_reports: list[dict[str, Any]] = []
    failing_actions: list[str] = []
    proposal_epoch = 10
    current_epoch = proposal_epoch + gov_gate.MIN_DELAY

    for action_id in action_ids:
        deltas = action_deltas.get(action_id, {})
        proposed = dict(base_state)
        for surface, delta in deltas.items():
            proposed[surface] = int(proposed.get(surface, 0)) + int(delta)
        proposed_state_errors = _surface_state_safety_errors(proposed)
        gate_report = _governance_gate_report_for_states(
            current=base_state,
            proposed=proposed,
            proposal_epoch=proposal_epoch,
            current_epoch=current_epoch,
        )
        accepted = not proposed_state_errors and all(gate_report.values())
        if not accepted:
            failing_actions.append(action_id)
        action_reports.append(
            {
                "action_id": action_id,
                "deltas": dict(sorted(deltas.items())),
                "proposed": dict(sorted(proposed.items())),
                "proposed_state_errors": proposed_state_errors,
                "gate_report": gate_report,
                "accepted": accepted,
            }
        )

    checks = {
        "base_state_safe": not base_state_errors,
        "policy_actions_present": bool(action_ids),
        "action_map_complete": set(action_ids) == set(action_deltas),
        "all_actions_gate_admissible": not failing_actions,
    }
    return {
        "schema": ACTION_GATE_DIAGNOSTICS_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "boundary": (
            "Every frozen action is checked as an advisory proposal against the deterministic "
            "governance gates from a canonical committed state; runtime gates still decide execution."
        ),
        "base_state": base_state,
        "base_state_errors": base_state_errors,
        "proposal_epoch": proposal_epoch,
        "current_epoch": current_epoch,
        "action_count": len(action_ids),
        "failing_actions": tuple(failing_actions),
        "actions": action_reports,
    }


def _policy_safety_blockers(
    policy: Mapping[str, Any],
    observation: Mapping[str, Any],
    *,
    current_epoch: int,
    last_update_epoch: int | None,
) -> tuple[str, ...]:
    safety = policy.get("safety", {})
    if not isinstance(safety, Mapping):
        return ("safety_must_be_object",)
    errors: list[str] = []
    if safety.get("emergency_pause") is True:
        errors.append("emergency_pause")
    for field, setting in (
        ("freshness_lag_epochs", "max_freshness_lag_epochs"),
        ("divergence_bps", "max_divergence_bps"),
        ("volatility_bps", "max_volatility_bps"),
    ):
        if setting in safety and int(observation.get(field, 0)) > int(safety.get(setting, 0)):
            errors.append(f"{field}_exceeds_{setting}")
    if int(observation.get("liquidity_depth_bps", 0)) < int(safety.get("min_liquidity_depth_bps", 0)):
        errors.append("liquidity_depth_below_minimum")
    if last_update_epoch is not None:
        cooldown = int(safety.get("min_cooldown_epochs", 0))
        if current_epoch < int(last_update_epoch) + cooldown:
            errors.append("cooldown_not_elapsed")
    return tuple(errors)


def _selection_blockers(
    *,
    policy: Mapping[str, Any],
    deltas: Mapping[str, int],
    previous_approved_deltas: Mapping[str, int],
    trajectory_used: Mapping[str, int] | None = None,
    trajectory_budget: Mapping[str, int] | None = None,
) -> tuple[str, ...]:
    selection = policy.get("selection", {})
    if not isinstance(selection, Mapping):
        return ()
    blockers: list[str] = []
    anti = selection.get("anti_oscillation", {})
    if isinstance(anti, Mapping) and anti.get("enabled") is True:
        parameters = anti.get("parameters", ())
        if isinstance(parameters, (list, tuple)):
            for parameter in parameters:
                previous_direction = _sign(int(previous_approved_deltas.get(str(parameter), 0)))
                candidate_direction = _sign(int(deltas.get(str(parameter), 0)))
                if previous_direction != 0 and candidate_direction != 0 and candidate_direction != previous_direction:
                    blockers.append(f"anti_oscillation:{parameter}")
    used = trajectory_used or {}
    budget = trajectory_budget if trajectory_budget is not None else _policy_trajectory_budget(policy)
    for parameter, limit in budget.items():
        delta = int(deltas.get(str(parameter), 0))
        already_used = int(used.get(str(parameter), 0))
        if already_used + abs(delta) > int(limit):
            blockers.append(f"trajectory_budget_exceeded:{parameter}")
    return tuple(blockers)


def _policy_trajectory_budget(policy: Mapping[str, Any]) -> dict[str, int]:
    selection = policy.get("selection", {})
    if not isinstance(selection, Mapping):
        return {}
    trajectory = selection.get("trajectory_budget", {})
    if not isinstance(trajectory, Mapping) or trajectory.get("enabled") is not True:
        return {}
    limits = trajectory.get("limits", {})
    if not isinstance(limits, Mapping):
        return {}
    out: dict[str, int] = {}
    for key, value in limits.items():
        if key in SEQUENCE_DRIFT_LIMITS and isinstance(value, int) and not isinstance(value, bool):
            out[str(key)] = int(value)
    return out


def _candidate_search_count_fields(candidate_search: Mapping[str, Any]) -> tuple[int, int, int, int]:
    checked = candidate_search.get("checked_count", 0)
    screened = candidate_search.get("selection_screened_count", 0)
    penalized = candidate_search.get("selection_penalized_count", 0)
    considered = candidate_search.get("candidate_considered_count", 0)
    checked_count = int(checked) if isinstance(checked, int) and not isinstance(checked, bool) else 0
    screened_count = int(screened) if isinstance(screened, int) and not isinstance(screened, bool) else 0
    penalized_count = int(penalized) if isinstance(penalized, int) and not isinstance(penalized, bool) else 0
    considered_count = (
        int(considered)
        if isinstance(considered, int) and not isinstance(considered, bool)
        else checked_count + screened_count
    )
    return checked_count, screened_count, penalized_count, considered_count


def _sequence_step_frontier(
    *,
    policy: Mapping[str, Any],
    forced_action_policies: Mapping[str, Mapping[str, Any]],
    action_deltas: Mapping[str, Mapping[str, int]],
    scenario: Mapping[str, Any],
    state: Mapping[str, int],
    observation: Mapping[str, int],
    current_epoch: int,
    proposal_epoch: int,
    last_update_epoch: int | None,
    previous_approved_deltas: Mapping[str, int],
    trajectory_used: Mapping[str, int],
) -> dict[str, Any]:
    best_action_id = ""
    best_utility = 0
    approved_count = 0
    selection_blocked_count = 0
    action_utilities: dict[str, int] = {}
    action_approved: dict[str, bool] = {}
    action_selection_blockers: dict[str, tuple[str, ...]] = {}

    for action_id, action_policy in forced_action_policies.items():
        blockers = _selection_blockers(
            policy=policy,
            deltas=action_deltas.get(action_id, {}),
            previous_approved_deltas=previous_approved_deltas,
            trajectory_used=trajectory_used,
        )
        action_selection_blockers[action_id] = blockers
        if blockers:
            selection_blocked_count += 1
            action_utilities[action_id] = 0
            action_approved[action_id] = False
            continue
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=action_policy,
            surface_state=state,
            observation=observation,
            current_epoch=current_epoch,
            proposal_epoch=proposal_epoch,
            last_update_epoch=last_update_epoch,
            expected_policy_hash=action_policy["policy_hash"],
        )
        approved = result.get("approved") is True
        utility = _scenario_utility(scenario, result)
        action_approved[action_id] = approved
        action_utilities[action_id] = utility
        if approved:
            approved_count += 1
        if utility > best_utility:
            best_action_id = action_id
            best_utility = utility

    return {
        "best_action_id": best_action_id,
        "best_utility": best_utility,
        "approved_action_count": approved_count,
        "selection_blocked_action_count": selection_blocked_count,
        "action_utilities": action_utilities,
        "action_approved": action_approved,
        "action_selection_blockers": action_selection_blockers,
    }


def _sign(value: int) -> int:
    if value < 0:
        return -1
    if value > 0:
        return 1
    return 0


def _replay_long_horizon_sequences(policy: Mapping[str, Any], *, label: str) -> dict[str, Any]:
    frozen = _freeze_policy(policy)
    cases = _sequence_cases()
    action_deltas = _action_map(frozen)
    forced_action_policies = {
        action_id: _forced_existing_action_policy(frozen, action_id=action_id)
        for action_id in sorted(action_deltas)
    }
    action_histogram: Counter[str] = Counter()
    error_histogram: Counter[str] = Counter()
    approved_count = 0
    rejected_count = 0
    adaptive_approved_count = 0
    invalid_accept_count = 0
    inconsistent_accept_count = 0
    fallback_used_count = 0
    candidate_checked_count_total = 0
    selection_screened_count_total = 0
    selection_penalized_count_total = 0
    candidate_considered_count_total = 0
    safety_blocked_count = 0
    safety_feasible_count = 0
    opportunity_miss_count = 0
    utility_score_total = 0
    frontier_utility_total = 0
    frontier_regret_total = 0
    frontier_regret_count = 0
    frontier_regret_max = 0
    frontier_action_match_count = 0
    frontier_utility_match_count = 0
    frontier_selection_blocked_count = 0
    frontier_sample_misses: list[dict[str, Any]] = []
    oscillation_count = 0
    max_consecutive_rejected_steps = 0
    final_state_error_counter: Counter[str] = Counter()
    cumulative_drift_failures: list[str] = []
    max_abs_cumulative_drift = {key: 0 for key in SEQUENCE_DRIFT_LIMITS}
    trajectory_budget_failures: list[str] = []
    max_trajectory_budget_used = {key: 0 for key in SEQUENCE_DRIFT_LIMITS}
    sequence_results: list[dict[str, Any]] = []
    step_count = 0

    for case in cases:
        sequence_id = str(case["id"])
        state = dict(case["surface_state"])
        initial_state = dict(state)
        previous_signs: dict[str, int] = {}
        previous_approved_deltas: dict[str, int] = {}
        trajectory_used: dict[str, int] = {key: 0 for key in SEQUENCE_DRIFT_LIMITS}
        consecutive_rejections = 0
        last_update_epoch: int | None = 75
        steps: list[dict[str, Any]] = []
        case_oscillations = 0
        case_approved = 0
        case_rejected = 0
        case_invalid_accepts = 0
        case_inconsistent_accepts = 0
        case_fallbacks = 0
        case_selection_screened_count = 0
        case_selection_penalized_count = 0
        case_candidate_considered_count = 0
        case_safety_feasible = 0
        case_safety_blocked = 0
        case_opportunity_misses = 0
        case_utility_total = 0
        case_frontier_utility_total = 0
        case_frontier_regret_total = 0
        case_frontier_regret_count = 0

        for index, bins in enumerate(case["bin_path"]):
            step_count += 1
            deviation_bin, volatility_bin, liquidity_bin = (int(part) for part in bins)
            observation = _observation_for_bins(deviation_bin, volatility_bin, liquidity_bin)
            overrides = case.get("observation_overrides_by_step", {})
            if isinstance(overrides, Mapping):
                observation.update(overrides.get(index, {}))
            step_scenario = {
                "id": f"{sequence_id}:step_{index}",
                "deviation_bin": deviation_bin,
                "volatility_bin": volatility_bin,
                "liquidity_bin": liquidity_bin,
                "bin_key": f"{deviation_bin}|{volatility_bin}|{liquidity_bin}",
            }
            current_epoch = 100 + (25 * index)
            proposal_epoch = current_epoch - gov_gate.MIN_DELAY
            opportunity_errors = _policy_safety_blockers(
                frozen,
                observation,
                current_epoch=current_epoch,
                last_update_epoch=last_update_epoch,
            ) + _surface_state_safety_errors(state)
            safety_feasible = not opportunity_errors
            if safety_feasible:
                safety_feasible_count += 1
                case_safety_feasible += 1
            else:
                safety_blocked_count += 1
                case_safety_blocked += 1
            result = evaluate_autonomous_governance_surface_q_policy_v1(
                policy=frozen,
                surface_state=state,
                observation=observation,
                current_epoch=current_epoch,
                proposal_epoch=proposal_epoch,
                last_update_epoch=last_update_epoch,
                expected_policy_hash=frozen["policy_hash"],
                previous_approved_deltas=previous_approved_deltas,
                trajectory_used=trajectory_used,
            )
            frontier = _sequence_step_frontier(
                policy=frozen,
                forced_action_policies=forced_action_policies,
                action_deltas=action_deltas,
                scenario=step_scenario,
                state=state,
                observation=observation,
                current_epoch=current_epoch,
                proposal_epoch=proposal_epoch,
                last_update_epoch=last_update_epoch,
                previous_approved_deltas=previous_approved_deltas,
                trajectory_used=trajectory_used,
            )
            action_id = str(result.get("action_id", ""))
            action_histogram[action_id] += 1
            candidate_search = result.get("candidate_search", {})
            if isinstance(candidate_search, Mapping):
                if candidate_search.get("fallback_used") is True:
                    fallback_used_count += 1
                    case_fallbacks += 1
                checked_count, screened_count, penalized_count, considered_count = _candidate_search_count_fields(candidate_search)
                candidate_checked_count_total += checked_count
                selection_screened_count_total += screened_count
                selection_penalized_count_total += penalized_count
                candidate_considered_count_total += considered_count
                case_selection_screened_count += screened_count
                case_selection_penalized_count += penalized_count
                case_candidate_considered_count += considered_count
            errors = tuple(str(error) for error in result.get("errors", ()))
            for error in errors:
                error_histogram[error] += 1
            utility = _scenario_utility(step_scenario, result)
            utility_score_total += utility
            case_utility_total += utility
            best_utility = int(frontier["best_utility"])
            frontier_utility_total += best_utility
            case_frontier_utility_total += best_utility
            selection_blocked_count = int(frontier.get("selection_blocked_action_count", 0))
            frontier_selection_blocked_count += selection_blocked_count
            regret = max(0, best_utility - utility)
            if regret > 0:
                frontier_regret_total += regret
                case_frontier_regret_total += regret
                frontier_regret_count += 1
                case_frontier_regret_count += 1
                frontier_regret_max = max(frontier_regret_max, regret)
                if len(frontier_sample_misses) < 12:
                    frontier_sample_misses.append(
                        {
                            "sequence": sequence_id,
                            "step_index": index,
                            "selected_action_id": action_id,
                            "selected_utility": utility,
                            "best_action_id": frontier["best_action_id"],
                            "best_utility": best_utility,
                            "regret": regret,
                            "approved_action_count": frontier["approved_action_count"],
                            "selection_blocked_action_count": selection_blocked_count,
                        }
                    )
            if action_id == frontier["best_action_id"]:
                frontier_action_match_count += 1
            if utility == best_utility:
                frontier_utility_match_count += 1
            approved = result.get("approved") is True
            if approved:
                approved_count += 1
                case_approved += 1
                consecutive_rejections = 0
                proposed = result.get("proposed", {})
                deltas = {
                    key: int(proposed.get(key, state.get(key, 0))) - int(state.get(key, 0))
                    for key in SEQUENCE_DRIFT_LIMITS
                }
                if any(value != 0 for value in deltas.values()):
                    adaptive_approved_count += 1
                    last_update_epoch = current_epoch
                    previous_approved_deltas = dict(deltas)
                    for key, delta in deltas.items():
                        trajectory_used[key] = int(trajectory_used.get(key, 0)) + abs(int(delta))
                for key, delta in deltas.items():
                    direction = _sign(delta)
                    previous = previous_signs.get(key, 0)
                    if direction != 0 and previous != 0 and direction != previous:
                        oscillation_count += 1
                        case_oscillations += 1
                    if direction != 0:
                        previous_signs[key] = direction
                if result.get("governance_surface_all_gates_ok") is not True:
                    invalid_accept_count += 1
                    case_invalid_accepts += 1
                if errors:
                    inconsistent_accept_count += 1
                    case_inconsistent_accepts += 1
                state = {key: int(value) for key, value in proposed.items()}
            else:
                rejected_count += 1
                case_rejected += 1
                if safety_feasible:
                    opportunity_miss_count += 1
                    case_opportunity_misses += 1
                consecutive_rejections += 1
                max_consecutive_rejected_steps = max(max_consecutive_rejected_steps, consecutive_rejections)
                deltas = {key: 0 for key in SEQUENCE_DRIFT_LIMITS}

            steps.append(
                {
                    "index": index,
                    "bin_key": f"{deviation_bin}|{volatility_bin}|{liquidity_bin}",
                    "action_id": action_id,
                    "approved": approved,
                    "safety_feasible": safety_feasible,
                    "opportunity_errors": list(opportunity_errors),
                    "utility": utility,
                    "frontier": {
                        "best_action_id": frontier["best_action_id"],
                        "best_utility": best_utility,
                        "regret": regret,
                        "approved_action_count": frontier["approved_action_count"],
                        "selection_blocked_action_count": selection_blocked_count,
                    },
                    "deltas": deltas,
                    "trajectory_used": dict(trajectory_used),
                    "errors": list(errors),
                    "gate_report": result.get("governance_surface_gate_report", {}),
                    "state_before": dict(result.get("surface_state", state)),
                    "state_after": dict(state),
                }
            )

        final_errors = _surface_state_safety_errors(state)
        for error in final_errors:
            final_state_error_counter[error] += 1
        case_drift = {
            key: int(state.get(key, 0)) - int(initial_state.get(key, 0))
            for key in SEQUENCE_DRIFT_LIMITS
        }
        for key, drift in case_drift.items():
            abs_drift = abs(drift)
            max_abs_cumulative_drift[key] = max(max_abs_cumulative_drift[key], abs_drift)
            limit = SEQUENCE_DRIFT_LIMITS[key]
            if abs_drift > limit:
                cumulative_drift_failures.append(f"{sequence_id}:{key}:{abs_drift}>{limit}")
        for key, used in trajectory_used.items():
            used_int = int(used)
            max_trajectory_budget_used[key] = max(max_trajectory_budget_used[key], used_int)
            limit = SEQUENCE_DRIFT_LIMITS[key]
            if used_int > limit:
                trajectory_budget_failures.append(f"{sequence_id}:{key}:{used_int}>{limit}")
        sequence_results.append(
            {
                "id": sequence_id,
                "step_count": len(steps),
                "approved_count": case_approved,
                "rejected_count": case_rejected,
                "invalid_accept_count": case_invalid_accepts,
                "inconsistent_accept_count": case_inconsistent_accepts,
                "fallback_used_count": case_fallbacks,
                "selection_screened_count": case_selection_screened_count,
                "selection_penalized_count": case_selection_penalized_count,
                "candidate_considered_count": case_candidate_considered_count,
                "safety_feasible_count": case_safety_feasible,
                "safety_blocked_count": case_safety_blocked,
                "opportunity_miss_count": case_opportunity_misses,
                "utility_score_total": case_utility_total,
                "frontier_utility_total": case_frontier_utility_total,
                "frontier_regret_total": case_frontier_regret_total,
                "frontier_regret_count": case_frontier_regret_count,
                "frontier_utility_completion_rate": round(
                    case_utility_total / max(1, case_frontier_utility_total), 6
                ),
                "oscillation_count": case_oscillations,
                "initial_state": initial_state,
                "final_state": state,
                "cumulative_drift": case_drift,
                "trajectory_used": dict(trajectory_used),
                "final_state_errors": list(final_errors),
                "steps": steps,
            }
        )

    observed_ids = tuple(sorted(str(item["id"]) for item in sequence_results))
    missing_ids = tuple(sequence_id for sequence_id in REQUIRED_SEQUENCE_CASES if sequence_id not in observed_ids)
    return {
        "label": label,
        "policy_id": str(frozen.get("policy_id", "")),
        "policy_hash": frozen["policy_hash"],
        "sequence_count": len(sequence_results),
        "step_count": step_count,
        "approved_count": approved_count,
        "rejected_count": rejected_count,
        "adaptive_approved_count": adaptive_approved_count,
        "fallback_used_count": fallback_used_count,
        "candidate_checked_count_total": candidate_checked_count_total,
        "selection_screened_count_total": selection_screened_count_total,
        "selection_penalized_count_total": selection_penalized_count_total,
        "candidate_considered_count_total": candidate_considered_count_total,
        "safety_feasible_count": safety_feasible_count,
        "safety_blocked_count": safety_blocked_count,
        "opportunity_miss_count": opportunity_miss_count,
        "opportunity_completion_rate": round(approved_count / max(1, safety_feasible_count), 6),
        "utility_score_total": utility_score_total,
        "frontier_utility_total": frontier_utility_total,
        "frontier_regret_total": frontier_regret_total,
        "frontier_regret_count": frontier_regret_count,
        "frontier_regret_max": frontier_regret_max,
        "frontier_action_match_count": frontier_action_match_count,
        "frontier_utility_match_count": frontier_utility_match_count,
        "frontier_selection_blocked_count": frontier_selection_blocked_count,
        "frontier_utility_completion_rate": round(
            utility_score_total / max(1, frontier_utility_total), 6
        ),
        "frontier_sample_misses": frontier_sample_misses,
        "invalid_accept_count": invalid_accept_count,
        "inconsistent_accept_count": inconsistent_accept_count,
        "oscillation_count": oscillation_count,
        "max_consecutive_rejected_steps": max_consecutive_rejected_steps,
        "max_abs_cumulative_drift": max_abs_cumulative_drift,
        "cumulative_drift_failures": tuple(cumulative_drift_failures),
        "max_trajectory_budget_used": max_trajectory_budget_used,
        "trajectory_budget_failures": tuple(trajectory_budget_failures),
        "final_state_error_histogram": _counter_to_dict(final_state_error_counter),
        "observed_ids": observed_ids,
        "missing_ids": missing_ids,
        "action_histogram": _counter_to_dict(action_histogram),
        "error_histogram": _counter_to_dict(error_histogram),
        "sequences": sequence_results,
    }


def _environment_curriculum_diagnostics(replay: Mapping[str, Any]) -> dict[str, Any]:
    """Audit the long-horizon replay as an interactive governance environment."""

    long_horizon = (
        replay.get("long_horizon", {})
        if isinstance(replay.get("long_horizon"), Mapping)
        else {}
    )
    sequences = (
        long_horizon.get("sequences", ())
        if isinstance(long_horizon.get("sequences", ()), list)
        else ()
    )
    observed_ids = tuple(sorted(str(item.get("id", "")) for item in sequences if isinstance(item, Mapping)))
    missing_ids = tuple(seq_id for seq_id in REQUIRED_SEQUENCE_CASES if seq_id not in observed_ids)
    step_count = int(long_horizon.get("step_count", 0)) if isinstance(long_horizon.get("step_count", 0), int) else 0
    state_transition_count = 0
    hold_step_count = 0
    noop_rejection_count = 0
    unique_bin_keys: set[str] = set()
    sequence_step_counts: dict[str, int] = {}
    sequence_outcomes: dict[str, dict[str, int]] = {}
    sequence_trajectory_used: dict[str, dict[str, int]] = {}

    for sequence in sequences:
        if not isinstance(sequence, Mapping):
            continue
        sequence_id = str(sequence.get("id", ""))
        sequence_step_count = int(sequence.get("step_count", 0)) if isinstance(sequence.get("step_count", 0), int) else 0
        sequence_step_counts[sequence_id] = sequence_step_count
        sequence_outcomes[sequence_id] = {
            "approved_count": int(sequence.get("approved_count", 0)) if isinstance(sequence.get("approved_count", 0), int) else 0,
            "rejected_count": int(sequence.get("rejected_count", 0)) if isinstance(sequence.get("rejected_count", 0), int) else 0,
            "safety_blocked_count": int(sequence.get("safety_blocked_count", 0)) if isinstance(sequence.get("safety_blocked_count", 0), int) else 0,
        }
        trajectory_used = sequence.get("trajectory_used", {})
        if isinstance(trajectory_used, Mapping):
            sequence_trajectory_used[sequence_id] = {
                key: int(value)
                for key, value in trajectory_used.items()
                if isinstance(value, int) and not isinstance(value, bool)
            }
        steps = sequence.get("steps", ())
        if not isinstance(steps, list):
            continue
        for step in steps:
            if not isinstance(step, Mapping):
                continue
            bin_key = str(step.get("bin_key", ""))
            if bin_key:
                unique_bin_keys.add(bin_key)
            before = step.get("state_before", {})
            after = step.get("state_after", {})
            state_changed = isinstance(before, Mapping) and isinstance(after, Mapping) and before != after
            approved = step.get("approved") is True
            if state_changed:
                state_transition_count += 1
            if approved and str(step.get("action_id", "")) == "hold" and not state_changed:
                hold_step_count += 1
            if not approved and not state_changed:
                noop_rejection_count += 1

    safety_interrupt = sequence_outcomes.get("safety_interrupt", {})
    trajectory_safety_interrupt = sequence_outcomes.get("trajectory_safety_interrupt", {})
    router_budget_walk = sequence_outcomes.get("router_budget_walk", {})
    router_budget_used = sequence_trajectory_used.get("router_budget_walk", {})
    router_recovery_walk = sequence_outcomes.get("router_recovery_walk", {})
    router_recovery_used = sequence_trajectory_used.get("router_recovery_walk", {})
    checks = {
        "sequence_ids_complete": not missing_ids,
        "sequence_count_matches": len(observed_ids) == len(REQUIRED_SEQUENCE_CASES),
        "step_count_positive": step_count > 0,
        "all_sequences_multi_step": (
            bool(sequence_step_counts)
            and all(count >= 4 for count in sequence_step_counts.values())
        ),
        "state_transitions_present": state_transition_count > 0,
        "hold_steps_present": hold_step_count > 0,
        "noop_rejections_present": noop_rejection_count > 0,
        "safety_interrupt_mixed_outcomes": (
            safety_interrupt.get("approved_count", 0) > 0
            and safety_interrupt.get("rejected_count", 0) > 0
            and safety_interrupt.get("safety_blocked_count", 0) > 0
        ),
        "trajectory_safety_interrupt_mixed_outcomes": (
            trajectory_safety_interrupt.get("approved_count", 0) > 0
            and trajectory_safety_interrupt.get("rejected_count", 0) > 0
            and trajectory_safety_interrupt.get("safety_blocked_count", 0) > 0
        ),
        "router_budget_walk_spends_router_budget": (
            router_budget_walk.get("approved_count", 0) > 0
            and router_budget_walk.get("rejected_count", 0) == 0
            and router_budget_used.get("reserve_bps", 0) == SEQUENCE_DRIFT_LIMITS["reserve_bps"]
            and router_budget_used.get("buyburn_bps", 0) == SEQUENCE_DRIFT_LIMITS["buyburn_bps"]
        ),
        "router_recovery_walk_spends_router_budget": (
            router_recovery_walk.get("approved_count", 0) > 0
            and router_recovery_walk.get("rejected_count", 0) == 0
            and router_recovery_used.get("reserve_bps", 0) == SEQUENCE_DRIFT_LIMITS["reserve_bps"]
            and router_recovery_used.get("buyburn_bps", 0) == SEQUENCE_DRIFT_LIMITS["buyburn_bps"]
        ),
        "unique_bin_paths_diverse": len(unique_bin_keys) >= 3,
        "frontier_regret_zero": long_horizon.get("frontier_regret_total") == 0,
        "no_invalid_accepts": long_horizon.get("invalid_accept_count") == 0,
        "no_inconsistent_accepts": long_horizon.get("inconsistent_accept_count") == 0,
        "final_states_safe": not long_horizon.get("final_state_error_histogram", {}),
        "cumulative_drift_within_limits": not long_horizon.get("cumulative_drift_failures", ()),
        "trajectory_budget_within_limits": not long_horizon.get("trajectory_budget_failures", ()),
    }
    return {
        "schema": ENVIRONMENT_CURRICULUM_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "boundary": (
            "Environment diagnostics audit the replay curriculum used for offline training; "
            "deterministic governance gates still decide execution."
        ),
        "required_sequence_ids": REQUIRED_SEQUENCE_CASES,
        "observed_sequence_ids": observed_ids,
        "missing_sequence_ids": missing_ids,
        "sequence_count": len(observed_ids),
        "step_count": step_count,
        "sequence_step_counts": sequence_step_counts,
        "sequence_outcomes": sequence_outcomes,
        "sequence_trajectory_used": sequence_trajectory_used,
        "state_transition_count": state_transition_count,
        "hold_step_count": hold_step_count,
        "noop_rejection_count": noop_rejection_count,
        "unique_bin_key_count": len(unique_bin_keys),
        "unique_bin_keys": tuple(sorted(unique_bin_keys)),
    }


def _counter_to_dict(counter: Counter[str]) -> dict[str, int]:
    return {key: counter[key] for key in sorted(counter)}


def _failure_family(errors: tuple[str, ...]) -> str:
    for error in errors:
        if error.startswith("governance_surface_gate_rejected:"):
            return error
    return errors[0] if errors else ""


def _scenario_utility(scenario: Mapping[str, Any], result: Mapping[str, Any]) -> int:
    """Heuristic replay utility for comparing policies, never for acceptance."""

    if result.get("approved") is not True:
        return 0
    action_id = str(result.get("action_id", ""))
    deviation_bin = int(scenario.get("deviation_bin", 0))
    volatility_bin = int(scenario.get("volatility_bin", 0))
    liquidity_bin = int(scenario.get("liquidity_bin", 0))
    current = result.get("surface_state", {})
    proposed = result.get("proposed", {})
    if not isinstance(current, Mapping):
        current = {}
    if not isinstance(proposed, Mapping):
        proposed = {}

    def delta(name: str) -> int:
        return int(proposed.get(name, current.get(name, 0))) - int(current.get(name, 0))

    fee_delta = delta("fee_bps")
    funding_delta = delta("funding_cap_bps")
    reserve_delta = delta("reserve_bps")
    buyburn_delta = delta("buyburn_bps")
    reserve_before = int(current.get("reserve_bps", 0))
    funding_after = int(proposed.get("funding_cap_bps", current.get("funding_cap_bps", 0)))
    funding_tightened_with_margin = (
        funding_delta < 0 and funding_after >= SOFT_FUNDING_RETAINED_FLOOR_BPS
    )

    score = 0
    if deviation_bin >= 3 and volatility_bin >= 2:
        if fee_delta > 0 and funding_tightened_with_margin:
            score += 140
        elif fee_delta > 0:
            score += 80
    elif deviation_bin >= 2:
        if fee_delta > 0 and not funding_tightened_with_margin:
            score += 90
        elif fee_delta > 0 and funding_tightened_with_margin:
            score += 75
    elif deviation_bin == 0 and volatility_bin == 0:
        if fee_delta < 0 and funding_delta > 0:
            score += 60
        elif action_id == "hold":
            score += 25

    if liquidity_bin == 0:
        if reserve_delta > 0 and buyburn_delta < 0:
            score += 70
    elif reserve_before > 9_000:
        if buyburn_delta > 0 and reserve_delta < 0:
            score += 90

    low_stress = deviation_bin <= 1 and volatility_bin <= 1 and liquidity_bin >= 1
    if low_stress:
        score += 35 if action_id == "hold" else -20

    return score


def _action_ids(policy: Mapping[str, Any]) -> tuple[str, ...]:
    ids: list[str] = []
    for action in policy.get("actions", []):
        if isinstance(action, Mapping) and isinstance(action.get("id"), str):
            ids.append(str(action["id"]))
    return tuple(ids)


def _frontier_for_scenario(
    *,
    forced_action_policies: Mapping[str, Mapping[str, Any]],
    scenario: Mapping[str, Any],
) -> dict[str, Any]:
    best_action_id = ""
    best_utility = 0
    approved_count = 0
    action_utilities: dict[str, int] = {}
    action_approved: dict[str, bool] = {}

    for action_id, action_policy in forced_action_policies.items():
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=action_policy,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=34,
            proposal_epoch=10,
            last_update_epoch=32,
            expected_policy_hash=action_policy["policy_hash"],
        )
        approved = result.get("approved") is True
        utility = _scenario_utility(scenario, result)
        action_approved[action_id] = approved
        action_utilities[action_id] = utility
        if approved:
            approved_count += 1
        if utility > best_utility:
            best_action_id = action_id
            best_utility = utility

    return {
        "best_action_id": best_action_id,
        "best_utility": best_utility,
        "approved_action_count": approved_count,
        "action_utilities": action_utilities,
        "action_approved": action_approved,
    }


def _replay_policy(policy: Mapping[str, Any], *, label: str) -> dict[str, Any]:
    frozen = _freeze_policy(policy)
    scenarios = _scenarios()
    forced_action_policies = {
        action_id: _forced_existing_action_policy(frozen, action_id=action_id)
        for action_id in sorted(_action_ids(frozen))
    }
    action_histogram: Counter[str] = Counter()
    error_histogram: Counter[str] = Counter()
    gate_rejection_histogram: Counter[str] = Counter()
    variant_histogram: Counter[str] = Counter()
    bin_histogram: Counter[str] = Counter()
    bin_keys: set[str] = set()
    approved_count = 0
    rejected_count = 0
    invalid_accept_count = 0
    inconsistent_accept_count = 0
    adaptive_approved_count = 0
    fallback_used_count = 0
    candidate_checked_count_total = 0
    selection_screened_count_total = 0
    selection_penalized_count_total = 0
    candidate_considered_count_total = 0
    safety_blocked_count = 0
    safety_feasible_count = 0
    opportunity_miss_count = 0
    utility_score_total = 0
    frontier_utility_total = 0
    frontier_regret_total = 0
    frontier_regret_count = 0
    frontier_regret_max = 0
    frontier_action_match_count = 0
    frontier_utility_match_count = 0
    frontier_sample_misses: list[dict[str, Any]] = []
    sample_failures: list[dict[str, Any]] = []

    for scenario in scenarios:
        bin_keys.add(str(scenario["bin_key"]))
        bin_histogram[str(scenario["bin_key"])] += 1
        variant_histogram[str(scenario["surface_variant"])] += 1
        opportunity_errors = _policy_safety_blockers(
            frozen,
            scenario["observation"],
            current_epoch=34,
            last_update_epoch=32,
        ) + _surface_state_safety_errors(scenario["surface_state"])
        safety_feasible = not opportunity_errors
        if safety_feasible:
            safety_feasible_count += 1
        else:
            safety_blocked_count += 1
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=34,
            proposal_epoch=10,
            last_update_epoch=32,
            expected_policy_hash=frozen["policy_hash"],
        )
        frontier = _frontier_for_scenario(
            forced_action_policies=forced_action_policies,
            scenario=scenario,
        )
        action_histogram[str(result.get("action_id", ""))] += 1
        candidate_search = result.get("candidate_search", {})
        if isinstance(candidate_search, Mapping):
            if candidate_search.get("fallback_used") is True:
                fallback_used_count += 1
            checked_count, screened_count, penalized_count, considered_count = _candidate_search_count_fields(candidate_search)
            candidate_checked_count_total += checked_count
            selection_screened_count_total += screened_count
            selection_penalized_count_total += penalized_count
            candidate_considered_count_total += considered_count
        approved = result.get("approved") is True
        if approved:
            approved_count += 1
            if result.get("action_id") != "hold":
                adaptive_approved_count += 1
        else:
            rejected_count += 1
            if safety_feasible:
                opportunity_miss_count += 1
        utility = _scenario_utility(scenario, result)
        utility_score_total += utility
        best_utility = int(frontier["best_utility"])
        frontier_utility_total += best_utility
        regret = max(0, best_utility - utility)
        if regret > 0:
            frontier_regret_total += regret
            frontier_regret_count += 1
            frontier_regret_max = max(frontier_regret_max, regret)
            if len(frontier_sample_misses) < 12:
                frontier_sample_misses.append(
                    {
                        "scenario": scenario["id"],
                        "selected_action_id": result.get("action_id", ""),
                        "selected_utility": utility,
                        "best_action_id": frontier["best_action_id"],
                        "best_utility": best_utility,
                        "regret": regret,
                        "approved_action_count": frontier["approved_action_count"],
                    }
                )
        if result.get("action_id") == frontier["best_action_id"]:
            frontier_action_match_count += 1
        if utility == best_utility:
            frontier_utility_match_count += 1
        if approved and result.get("governance_surface_all_gates_ok") is not True:
            invalid_accept_count += 1
            sample_failures.append(
                {
                    "scenario": scenario["id"],
                    "kind": "invalid_accept",
                    "action_id": result.get("action_id", ""),
                    "errors": list(result.get("errors", ())),
                }
            )
        if approved and result.get("errors"):
            inconsistent_accept_count += 1
        for error in result.get("errors", ()):
            error_histogram[str(error)] += 1
        for gate, accepted in result.get("governance_surface_gate_report", {}).items():
            if accepted is not True:
                gate_rejection_histogram[str(gate)] += 1
        if not approved and len(sample_failures) < 12:
            sample_failures.append(
                {
                    "scenario": scenario["id"],
                    "kind": "rejected",
                    "action_id": result.get("action_id", ""),
                    "safety_feasible": safety_feasible,
                    "opportunity_errors": list(opportunity_errors),
                    "errors": list(result.get("errors", ()))[:6],
                }
            )

    return {
        "label": label,
        "policy_id": str(frozen.get("policy_id", "")),
        "policy_hash": frozen["policy_hash"],
        "scenario_count": len(scenarios),
        "bin_count": len(bin_keys),
        "surface_variant_count": len(variant_histogram),
        "approved_count": approved_count,
        "rejected_count": rejected_count,
        "adaptive_approved_count": adaptive_approved_count,
        "fallback_used_count": fallback_used_count,
        "candidate_checked_count_total": candidate_checked_count_total,
        "selection_screened_count_total": selection_screened_count_total,
        "selection_penalized_count_total": selection_penalized_count_total,
        "candidate_considered_count_total": candidate_considered_count_total,
        "safety_feasible_count": safety_feasible_count,
        "safety_blocked_count": safety_blocked_count,
        "opportunity_miss_count": opportunity_miss_count,
        "opportunity_completion_rate": round(approved_count / max(1, safety_feasible_count), 6),
        "utility_score_total": utility_score_total,
        "utility_score_mean": round(utility_score_total / max(1, len(scenarios)), 6),
        "frontier_utility_total": frontier_utility_total,
        "frontier_regret_total": frontier_regret_total,
        "frontier_regret_count": frontier_regret_count,
        "frontier_regret_max": frontier_regret_max,
        "frontier_action_match_count": frontier_action_match_count,
        "frontier_utility_match_count": frontier_utility_match_count,
        "frontier_utility_completion_rate": round(
            utility_score_total / max(1, frontier_utility_total), 6
        ),
        "invalid_accept_count": invalid_accept_count,
        "inconsistent_accept_count": inconsistent_accept_count,
        "action_histogram": _counter_to_dict(action_histogram),
        "bin_histogram": _counter_to_dict(bin_histogram),
        "error_histogram": _counter_to_dict(error_histogram),
        "gate_rejection_histogram": _counter_to_dict(gate_rejection_histogram),
        "surface_variant_histogram": _counter_to_dict(variant_histogram),
        "frontier_sample_misses": frontier_sample_misses,
        "sample_failures": sample_failures,
    }


def _replay_intra_bin_stress(policy: Mapping[str, Any], *, label: str) -> dict[str, Any]:
    """Replay non-representative values that map to the same runtime bins."""

    frozen = _freeze_policy(policy)
    scenarios = _intra_bin_stress_scenarios()
    forced_action_policies = {
        action_id: _forced_existing_action_policy(frozen, action_id=action_id)
        for action_id in sorted(_action_ids(frozen))
    }
    action_histogram: Counter[str] = Counter()
    error_histogram: Counter[str] = Counter()
    bin_histogram: Counter[str] = Counter()
    probe_histogram: Counter[str] = Counter()
    surface_variant_histogram: Counter[str] = Counter()
    approved_count = 0
    rejected_count = 0
    invalid_accept_count = 0
    inconsistent_accept_count = 0
    safety_feasible_count = 0
    safety_blocked_count = 0
    opportunity_miss_count = 0
    candidate_checked_count_total = 0
    selection_screened_count_total = 0
    selection_penalized_count_total = 0
    candidate_considered_count_total = 0
    fallback_used_count = 0
    utility_score_total = 0
    frontier_utility_total = 0
    frontier_regret_total = 0
    frontier_regret_count = 0
    frontier_regret_max = 0
    bin_mismatch_count = 0
    bin_mismatch_samples: list[dict[str, Any]] = []
    frontier_sample_misses: list[dict[str, Any]] = []
    sample_failures: list[dict[str, Any]] = []

    for scenario in scenarios:
        bin_key = str(scenario["bin_key"])
        probe = str(scenario["probe"])
        variant = str(scenario["surface_variant"])
        bin_histogram[bin_key] += 1
        probe_histogram[probe] += 1
        surface_variant_histogram[variant] += 1
        opportunity_errors = _policy_safety_blockers(
            frozen,
            scenario["observation"],
            current_epoch=34,
            last_update_epoch=32,
        ) + _surface_state_safety_errors(scenario["surface_state"])
        safety_feasible = not opportunity_errors
        if safety_feasible:
            safety_feasible_count += 1
        else:
            safety_blocked_count += 1
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=34,
            proposal_epoch=10,
            last_update_epoch=32,
            expected_policy_hash=frozen["policy_hash"],
        )
        frontier = _frontier_for_scenario(
            forced_action_policies=forced_action_policies,
            scenario=scenario,
        )
        action_id = str(result.get("action_id", ""))
        action_histogram[action_id] += 1
        candidate_search = result.get("candidate_search", {})
        if isinstance(candidate_search, Mapping):
            if candidate_search.get("fallback_used") is True:
                fallback_used_count += 1
            checked_count, screened_count, penalized_count, considered_count = _candidate_search_count_fields(candidate_search)
            candidate_checked_count_total += checked_count
            selection_screened_count_total += screened_count
            selection_penalized_count_total += penalized_count
            candidate_considered_count_total += considered_count
        state_bins = result.get("state_bins", {})
        if not isinstance(state_bins, Mapping):
            state_bins = {}
        expected_bins = scenario.get("expected_bins", {})
        observed_bin_key = "|".join(
            str(state_bins.get(field, ""))
            for field in ("deviation_bps", "volatility_bps", "liquidity_depth_bps")
        )
        if observed_bin_key != bin_key:
            bin_mismatch_count += 1
            if len(bin_mismatch_samples) < 12:
                bin_mismatch_samples.append(
                    {
                        "scenario": scenario["id"],
                        "expected_bin_key": bin_key,
                        "observed_bin_key": observed_bin_key,
                        "expected_bins": dict(expected_bins) if isinstance(expected_bins, Mapping) else {},
                        "state_bins": dict(state_bins),
                    }
                )
        approved = result.get("approved") is True
        errors = tuple(str(error) for error in result.get("errors", ()))
        for error in errors:
            error_histogram[error] += 1
        if approved:
            approved_count += 1
        else:
            rejected_count += 1
            if safety_feasible:
                opportunity_miss_count += 1
        utility = _scenario_utility(scenario, result)
        utility_score_total += utility
        best_utility = int(frontier["best_utility"])
        frontier_utility_total += best_utility
        regret = max(0, best_utility - utility)
        if regret > 0:
            frontier_regret_total += regret
            frontier_regret_count += 1
            frontier_regret_max = max(frontier_regret_max, regret)
            if len(frontier_sample_misses) < 12:
                frontier_sample_misses.append(
                    {
                        "scenario": scenario["id"],
                        "selected_action_id": action_id,
                        "selected_utility": utility,
                        "best_action_id": frontier["best_action_id"],
                        "best_utility": best_utility,
                        "regret": regret,
                        "approved_action_count": frontier["approved_action_count"],
                    }
                )
        if approved and result.get("governance_surface_all_gates_ok") is not True:
            invalid_accept_count += 1
            if len(sample_failures) < 12:
                sample_failures.append(
                    {
                        "scenario": scenario["id"],
                        "kind": "invalid_accept",
                        "action_id": action_id,
                        "errors": list(errors),
                    }
                )
        if approved and errors:
            inconsistent_accept_count += 1
        if not approved and len(sample_failures) < 12:
            sample_failures.append(
                {
                    "scenario": scenario["id"],
                    "kind": "rejected",
                    "action_id": action_id,
                    "safety_feasible": safety_feasible,
                    "opportunity_errors": list(opportunity_errors),
                    "errors": list(errors)[:6],
                }
            )

    expected_bin_count = 48
    expected_count_per_bin = len(REQUIRED_INTRABIN_PROBES) * len(REQUIRED_SURFACE_VARIANTS)
    missing_bins = tuple(
        f"{d}|{v}|{l}"
        for d in range(4)
        for v in range(4)
        for l in range(3)
        if int(bin_histogram.get(f"{d}|{v}|{l}", 0)) == 0
    )
    uneven_bins = tuple(
        f"{d}|{v}|{l}"
        for d in range(4)
        for v in range(4)
        for l in range(3)
        if int(bin_histogram.get(f"{d}|{v}|{l}", 0)) != expected_count_per_bin
    )
    missing_probes = tuple(probe for probe in REQUIRED_INTRABIN_PROBES if int(probe_histogram.get(probe, 0)) == 0)
    expected_count_per_probe = expected_bin_count * len(REQUIRED_SURFACE_VARIANTS)
    uneven_probes = tuple(
        probe for probe in REQUIRED_INTRABIN_PROBES if int(probe_histogram.get(probe, 0)) != expected_count_per_probe
    )
    checks = {
        "scenario_count_matches": len(scenarios) == expected_bin_count * expected_count_per_bin,
        "all_bins_present": not missing_bins,
        "bin_counts_uniform": not uneven_bins,
        "probe_profiles_present": not missing_probes,
        "probe_profile_counts_uniform": not uneven_probes,
        "observed_bins_match_expected": bin_mismatch_count == 0,
        "safety_feasible_count_positive": safety_feasible_count > 0,
        "safety_feasible_opportunities_complete": opportunity_miss_count == 0,
        "frontier_regret_zero": frontier_regret_total == 0,
        "frontier_utility_complete": round(
            utility_score_total / max(1, frontier_utility_total), 6
        ) == 1.0,
        "invalid_accept_count_zero": invalid_accept_count == 0,
        "inconsistent_accept_count_zero": inconsistent_accept_count == 0,
    }
    return {
        "label": label,
        "policy_id": str(frozen.get("policy_id", "")),
        "policy_hash": frozen["policy_hash"],
        "ok": all(checks.values()),
        "checks": checks,
        "scenario_count": len(scenarios),
        "bin_count": len(bin_histogram),
        "probe_profile_count": len(probe_histogram),
        "surface_variant_count": len(surface_variant_histogram),
        "approved_count": approved_count,
        "rejected_count": rejected_count,
        "fallback_used_count": fallback_used_count,
        "candidate_checked_count_total": candidate_checked_count_total,
        "selection_screened_count_total": selection_screened_count_total,
        "selection_penalized_count_total": selection_penalized_count_total,
        "candidate_considered_count_total": candidate_considered_count_total,
        "safety_feasible_count": safety_feasible_count,
        "safety_blocked_count": safety_blocked_count,
        "opportunity_miss_count": opportunity_miss_count,
        "utility_score_total": utility_score_total,
        "frontier_utility_total": frontier_utility_total,
        "frontier_regret_total": frontier_regret_total,
        "frontier_regret_count": frontier_regret_count,
        "frontier_regret_max": frontier_regret_max,
        "frontier_utility_completion_rate": round(
            utility_score_total / max(1, frontier_utility_total), 6
        ),
        "invalid_accept_count": invalid_accept_count,
        "inconsistent_accept_count": inconsistent_accept_count,
        "bin_mismatch_count": bin_mismatch_count,
        "bin_mismatch_samples": bin_mismatch_samples,
        "missing_bins": missing_bins,
        "uneven_bins": uneven_bins,
        "missing_probe_profiles": missing_probes,
        "uneven_probe_profiles": uneven_probes,
        "action_histogram": _counter_to_dict(action_histogram),
        "bin_histogram": _counter_to_dict(bin_histogram),
        "probe_histogram": _counter_to_dict(probe_histogram),
        "surface_variant_histogram": _counter_to_dict(surface_variant_histogram),
        "error_histogram": _counter_to_dict(error_histogram),
        "frontier_sample_misses": frontier_sample_misses,
        "sample_failures": sample_failures,
        "boundary": "Intra-bin stress reuses runtime binning and exact gates; it does not authorize governance by score.",
    }


def _replay_safety_lanes(policy: Mapping[str, Any], *, label: str) -> dict[str, Any]:
    frozen = _freeze_policy(policy)
    lanes = _safety_lanes()
    approved_count = 0
    missing_expected_error_count = 0
    error_histogram: Counter[str] = Counter()
    lane_results: list[dict[str, Any]] = []

    for lane in lanes:
        expected_hash = (
            frozen["policy_hash"]
            if lane["expected_policy_hash"] == "policy"
            else str(lane["expected_policy_hash"])
        )
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=lane["surface_state"],
            observation=lane["observation"],
            current_epoch=int(lane["current_epoch"]),
            proposal_epoch=int(lane["proposal_epoch"]),
            last_update_epoch=lane["last_update_epoch"],
            expected_policy_hash=expected_hash,
        )
        errors = tuple(str(error) for error in result.get("errors", ()))
        for error in errors:
            error_histogram[error] += 1
        approved = result.get("approved") is True
        if approved:
            approved_count += 1
        expected_error = str(lane["expected_error"])
        has_expected_error = expected_error in errors
        if not has_expected_error:
            missing_expected_error_count += 1
        lane_results.append(
            {
                "id": lane["id"],
                "approved": approved,
                "action_id": result.get("action_id", ""),
                "expected_error": expected_error,
                "has_expected_error": has_expected_error,
                "errors": list(errors),
            }
        )

    return {
        "label": label,
        "policy_id": str(frozen.get("policy_id", "")),
        "policy_hash": frozen["policy_hash"],
        "scenario_count": len(lanes),
        "approved_count": approved_count,
        "rejected_count": len(lanes) - approved_count,
        "missing_expected_error_count": missing_expected_error_count,
        "error_histogram": _counter_to_dict(error_histogram),
        "lanes": lane_results,
    }


def _replay_safety_boundary_sweep(policy: Mapping[str, Any], *, label: str) -> dict[str, Any]:
    frozen = _freeze_policy(policy)
    scenarios = _safety_boundary_scenarios()
    approved_count = 0
    inside_count = 0
    inside_approved_count = 0
    outside_count = 0
    outside_approved_count = 0
    outside_missing_expected_error_count = 0
    invalid_accept_count = 0
    inconsistent_accept_count = 0
    error_histogram: Counter[str] = Counter()
    probe_histogram: Counter[str] = Counter()
    anchor_histogram: Counter[str] = Counter()
    scenario_results: list[dict[str, Any]] = []

    for scenario in scenarios:
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=int(scenario["current_epoch"]),
            proposal_epoch=int(scenario["proposal_epoch"]),
            last_update_epoch=scenario["last_update_epoch"],
            expected_policy_hash=frozen["policy_hash"],
        )
        status = str(scenario["status"])
        probe = str(scenario["probe"])
        anchor = str(scenario["anchor_bin_key"])
        probe_histogram[probe] += 1
        anchor_histogram[anchor] += 1
        errors = tuple(str(error) for error in result.get("errors", ()))
        for error in errors:
            error_histogram[error] += 1
        approved = result.get("approved") is True
        if approved:
            approved_count += 1
        if approved and result.get("governance_surface_all_gates_ok") is not True:
            invalid_accept_count += 1
        if approved and errors:
            inconsistent_accept_count += 1
        expected_error = str(scenario.get("expected_error", ""))
        has_expected_error = (not expected_error) or expected_error in errors
        if status == "inside":
            inside_count += 1
            if approved:
                inside_approved_count += 1
        else:
            outside_count += 1
            if approved:
                outside_approved_count += 1
            if not has_expected_error:
                outside_missing_expected_error_count += 1
        scenario_results.append(
            {
                "id": str(scenario["id"]),
                "status": status,
                "probe": probe,
                "anchor_bin_key": anchor,
                "bin_key": str(scenario["bin_key"]),
                "approved": approved,
                "action_id": result.get("action_id", ""),
                "expected_error": expected_error,
                "has_expected_error": has_expected_error,
                "errors": list(errors),
            }
        )

    missing_probes = tuple(
        probe for probe in REQUIRED_SAFETY_BOUNDARY_PROBES if int(probe_histogram.get(probe, 0)) == 0
    )
    uneven_probes = tuple(
        probe
        for probe in REQUIRED_SAFETY_BOUNDARY_PROBES
        if int(probe_histogram.get(probe, 0)) != len(SAFETY_BOUNDARY_BIN_ANCHORS)
    )
    missing_anchors = tuple(
        f"{deviation}|{volatility}|{liquidity}"
        for deviation, volatility, liquidity in SAFETY_BOUNDARY_BIN_ANCHORS
        if int(anchor_histogram.get(f"{deviation}|{volatility}|{liquidity}", 0)) == 0
    )
    uneven_anchors = tuple(
        f"{deviation}|{volatility}|{liquidity}"
        for deviation, volatility, liquidity in SAFETY_BOUNDARY_BIN_ANCHORS
        if int(anchor_histogram.get(f"{deviation}|{volatility}|{liquidity}", 0))
        != len(REQUIRED_SAFETY_BOUNDARY_PROBES)
    )
    checks = {
        "scenarios_present": len(scenarios) > 0,
        "probe_profiles_complete": not missing_probes,
        "probe_counts_uniform": not uneven_probes,
        "anchor_bins_complete": not missing_anchors,
        "anchor_counts_uniform": not uneven_anchors,
        "inside_cases_approve": inside_count > 0 and inside_approved_count == inside_count,
        "outside_cases_reject": outside_count > 0 and outside_approved_count == 0,
        "outside_expected_errors_present": outside_missing_expected_error_count == 0,
        "invalid_accept_count_zero": invalid_accept_count == 0,
        "inconsistent_accept_count_zero": inconsistent_accept_count == 0,
    }
    return {
        "schema": SAFETY_BOUNDARY_SWEEP_SCHEMA,
        "label": label,
        "policy_id": str(frozen.get("policy_id", "")),
        "policy_hash": frozen["policy_hash"],
        "ok": all(checks.values()),
        "checks": checks,
        "scenario_count": len(scenarios),
        "inside_count": inside_count,
        "inside_approved_count": inside_approved_count,
        "outside_count": outside_count,
        "outside_approved_count": outside_approved_count,
        "approved_count": approved_count,
        "rejected_count": len(scenarios) - approved_count,
        "outside_missing_expected_error_count": outside_missing_expected_error_count,
        "invalid_accept_count": invalid_accept_count,
        "inconsistent_accept_count": inconsistent_accept_count,
        "probe_histogram": _counter_to_dict(probe_histogram),
        "anchor_bin_histogram": _counter_to_dict(anchor_histogram),
        "missing_probes": missing_probes,
        "uneven_probes": uneven_probes,
        "missing_anchor_bins": missing_anchors,
        "uneven_anchor_bins": uneven_anchors,
        "error_histogram": _counter_to_dict(error_histogram),
        "scenarios": scenario_results,
        "boundary": "Safety-boundary sweep audits near-threshold runtime decisions; deterministic gates still decide execution.",
    }


def _replay_safety_interaction_sweep(policy: Mapping[str, Any], *, label: str) -> dict[str, Any]:
    frozen = _freeze_policy(policy)
    scenarios = _safety_interaction_scenarios()
    approved_count = 0
    inside_count = 0
    inside_approved_count = 0
    outside_count = 0
    outside_approved_count = 0
    outside_missing_expected_error_count = 0
    invalid_accept_count = 0
    inconsistent_accept_count = 0
    error_histogram: Counter[str] = Counter()
    profile_histogram: Counter[str] = Counter()
    pair_histogram: Counter[str] = Counter()
    anchor_histogram: Counter[str] = Counter()
    scenario_results: list[dict[str, Any]] = []

    for scenario in scenarios:
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=int(scenario["current_epoch"]),
            proposal_epoch=int(scenario["proposal_epoch"]),
            last_update_epoch=scenario["last_update_epoch"],
            expected_policy_hash=frozen["policy_hash"],
        )
        status = str(scenario["status"])
        profile = str(scenario["profile"])
        pair = str(scenario["control_pair"])
        anchor = str(scenario["anchor_bin_key"])
        profile_histogram[profile] += 1
        pair_histogram[pair] += 1
        anchor_histogram[anchor] += 1
        errors = tuple(str(error) for error in result.get("errors", ()))
        for error in errors:
            error_histogram[error] += 1
        approved = result.get("approved") is True
        if approved:
            approved_count += 1
        if approved and result.get("governance_surface_all_gates_ok") is not True:
            invalid_accept_count += 1
        if approved and errors:
            inconsistent_accept_count += 1
        expected_errors = tuple(str(error) for error in scenario.get("expected_errors", ()))
        has_expected_errors = all(error in errors for error in expected_errors)
        if status == "inside":
            inside_count += 1
            if approved:
                inside_approved_count += 1
        else:
            outside_count += 1
            if approved:
                outside_approved_count += 1
            if not has_expected_errors:
                outside_missing_expected_error_count += 1
        scenario_results.append(
            {
                "id": str(scenario["id"]),
                "status": status,
                "profile": profile,
                "control_pair": pair,
                "anchor_bin_key": anchor,
                "bin_key": str(scenario["bin_key"]),
                "approved": approved,
                "action_id": result.get("action_id", ""),
                "expected_errors": expected_errors,
                "has_expected_errors": has_expected_errors,
                "errors": list(errors),
            }
        )

    expected_pairs = tuple(
        f"{first}+{second}"
        for index, first in enumerate(SAFETY_INTERACTION_CONTROLS)
        for second in SAFETY_INTERACTION_CONTROLS[index + 1 :]
    )
    missing_profiles = tuple(
        profile for profile in SAFETY_INTERACTION_PROFILES if int(profile_histogram.get(profile, 0)) == 0
    )
    uneven_profiles = tuple(
        profile
        for profile in SAFETY_INTERACTION_PROFILES
        if int(profile_histogram.get(profile, 0))
        != len(SAFETY_INTERACTION_BIN_ANCHORS) * len(expected_pairs)
    )
    missing_pairs = tuple(pair for pair in expected_pairs if int(pair_histogram.get(pair, 0)) == 0)
    uneven_pairs = tuple(
        pair
        for pair in expected_pairs
        if int(pair_histogram.get(pair, 0))
        != len(SAFETY_INTERACTION_BIN_ANCHORS) * len(SAFETY_INTERACTION_PROFILES)
    )
    missing_anchors = tuple(
        f"{deviation}|{volatility}|{liquidity}"
        for deviation, volatility, liquidity in SAFETY_INTERACTION_BIN_ANCHORS
        if int(anchor_histogram.get(f"{deviation}|{volatility}|{liquidity}", 0)) == 0
    )
    uneven_anchors = tuple(
        f"{deviation}|{volatility}|{liquidity}"
        for deviation, volatility, liquidity in SAFETY_INTERACTION_BIN_ANCHORS
        if int(anchor_histogram.get(f"{deviation}|{volatility}|{liquidity}", 0))
        != len(expected_pairs) * len(SAFETY_INTERACTION_PROFILES)
    )
    checks = {
        "scenarios_present": len(scenarios) > 0,
        "profiles_complete": not missing_profiles,
        "profile_counts_uniform": not uneven_profiles,
        "control_pairs_complete": not missing_pairs,
        "control_pair_counts_uniform": not uneven_pairs,
        "anchor_bins_complete": not missing_anchors,
        "anchor_counts_uniform": not uneven_anchors,
        "inside_cases_approve": inside_count > 0 and inside_approved_count == inside_count,
        "outside_cases_reject": outside_count > 0 and outside_approved_count == 0,
        "outside_expected_errors_present": outside_missing_expected_error_count == 0,
        "invalid_accept_count_zero": invalid_accept_count == 0,
        "inconsistent_accept_count_zero": inconsistent_accept_count == 0,
    }
    return {
        "schema": SAFETY_INTERACTION_SWEEP_SCHEMA,
        "label": label,
        "policy_id": str(frozen.get("policy_id", "")),
        "policy_hash": frozen["policy_hash"],
        "ok": all(checks.values()),
        "checks": checks,
        "scenario_count": len(scenarios),
        "inside_count": inside_count,
        "inside_approved_count": inside_approved_count,
        "outside_count": outside_count,
        "outside_approved_count": outside_approved_count,
        "approved_count": approved_count,
        "rejected_count": len(scenarios) - approved_count,
        "outside_missing_expected_error_count": outside_missing_expected_error_count,
        "invalid_accept_count": invalid_accept_count,
        "inconsistent_accept_count": inconsistent_accept_count,
        "profile_histogram": _counter_to_dict(profile_histogram),
        "control_pair_histogram": _counter_to_dict(pair_histogram),
        "anchor_bin_histogram": _counter_to_dict(anchor_histogram),
        "missing_profiles": missing_profiles,
        "uneven_profiles": uneven_profiles,
        "missing_control_pairs": missing_pairs,
        "uneven_control_pairs": uneven_pairs,
        "missing_anchor_bins": missing_anchors,
        "uneven_anchor_bins": uneven_anchors,
        "error_histogram": _counter_to_dict(error_histogram),
        "scenarios": scenario_results,
        "boundary": "Safety-interaction sweep audits paired near-threshold runtime decisions; deterministic gates still decide execution.",
    }


def _replay_surface_boundary_sweep(policy: Mapping[str, Any], *, label: str) -> dict[str, Any]:
    frozen = _freeze_policy(policy)
    scenarios = _surface_boundary_scenarios()
    actions = _action_map(frozen)
    forced_action_policies = {
        action_id: _forced_existing_action_policy(frozen, action_id=action_id)
        for action_id in sorted(actions)
    }
    approved_count = 0
    candidate_approved_count = 0
    candidate_rejected_count = 0
    invalid_accept_count = 0
    inconsistent_accept_count = 0
    q_row_missing_count = 0
    missing_expected_rejection_count = 0
    profile_histogram: Counter[str] = Counter()
    family_histogram: Counter[str] = Counter()
    status_histogram: Counter[str] = Counter()
    error_histogram: Counter[str] = Counter()
    candidate_error_histogram: Counter[str] = Counter()
    scenario_results: list[dict[str, Any]] = []

    for scenario in scenarios:
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=int(scenario["current_epoch"]),
            proposal_epoch=int(scenario["proposal_epoch"]),
            last_update_epoch=scenario["last_update_epoch"],
            expected_policy_hash=frozen["policy_hash"],
        )
        profile = str(scenario["profile"])
        family = str(scenario["boundary_family"])
        limit_status = str(scenario["limit_status"])
        profile_histogram[profile] += 1
        family_histogram[family] += 1
        status_histogram[limit_status] += 1

        errors = tuple(str(error) for error in result.get("errors", ()))
        for error in errors:
            error_histogram[error] += 1
        selected_q_row_missing = tuple(error for error in errors if error.startswith("q_row_missing:"))
        q_row_missing_count += len(selected_q_row_missing)
        approved = result.get("approved") is True
        if approved:
            approved_count += 1
        if approved and result.get("governance_surface_all_gates_ok") is not True:
            invalid_accept_count += 1
        if approved and errors:
            inconsistent_accept_count += 1

        expected_error = str(scenario.get("expected_rejection_error", ""))
        expected_rejection_seen = not expected_error
        candidate_results: list[dict[str, Any]] = []
        for action_id, action_policy in forced_action_policies.items():
            candidate = evaluate_autonomous_governance_surface_q_policy_v1(
                policy=action_policy,
                surface_state=scenario["surface_state"],
                observation=scenario["observation"],
                current_epoch=int(scenario["current_epoch"]),
                proposal_epoch=int(scenario["proposal_epoch"]),
                last_update_epoch=scenario["last_update_epoch"],
                expected_policy_hash=action_policy["policy_hash"],
            )
            candidate_errors = tuple(str(error) for error in candidate.get("errors", ()))
            for error in candidate_errors:
                candidate_error_histogram[error] += 1
            candidate_approved = candidate.get("approved") is True
            if candidate_approved:
                candidate_approved_count += 1
            else:
                candidate_rejected_count += 1
            if expected_error and expected_error in candidate_errors:
                expected_rejection_seen = True
            candidate_results.append(
                {
                    "action_id": action_id,
                    "approved": candidate_approved,
                    "errors": list(candidate_errors),
                }
            )
        if not expected_rejection_seen:
            missing_expected_rejection_count += 1
        scenario_results.append(
            {
                "id": str(scenario["id"]),
                "profile": profile,
                "boundary_family": family,
                "limit_status": limit_status,
                "bin_key": str(scenario["bin_key"]),
                "approved": approved,
                "action_id": result.get("action_id", ""),
                "expected_rejection_error": expected_error,
                "expected_rejection_seen": expected_rejection_seen,
                "q_row_missing_count": len(selected_q_row_missing),
                "errors": list(errors),
                "candidate_approved_count": sum(1 for item in candidate_results if item["approved"]),
                "candidate_rejected_count": sum(1 for item in candidate_results if not item["approved"]),
                "candidate_results": candidate_results,
            }
        )

    missing_profiles = tuple(
        profile
        for profile in REQUIRED_SURFACE_BOUNDARY_PROFILES
        if int(profile_histogram.get(profile, 0)) == 0
    )
    uneven_profiles = tuple(
        profile
        for profile in REQUIRED_SURFACE_BOUNDARY_PROFILES
        if int(profile_histogram.get(profile, 0)) != 1
    )
    checks = {
        "scenarios_present": len(scenarios) > 0,
        "profiles_complete": not missing_profiles,
        "profile_counts_uniform": not uneven_profiles,
        "selected_q_rows_complete": q_row_missing_count == 0,
        "selected_cases_approve": approved_count == len(scenarios),
        "candidate_rejections_present": candidate_rejected_count > 0,
        "expected_rejections_present": missing_expected_rejection_count == 0,
        "invalid_accept_count_zero": invalid_accept_count == 0,
        "inconsistent_accept_count_zero": inconsistent_accept_count == 0,
    }
    return {
        "schema": SURFACE_BOUNDARY_SWEEP_SCHEMA,
        "label": label,
        "policy_id": str(frozen.get("policy_id", "")),
        "policy_hash": frozen["policy_hash"],
        "ok": all(checks.values()),
        "checks": checks,
        "scenario_count": len(scenarios),
        "approved_count": approved_count,
        "rejected_count": len(scenarios) - approved_count,
        "candidate_action_count": len(actions),
        "candidate_approved_count": candidate_approved_count,
        "candidate_rejected_count": candidate_rejected_count,
        "q_row_missing_count": q_row_missing_count,
        "missing_expected_rejection_count": missing_expected_rejection_count,
        "invalid_accept_count": invalid_accept_count,
        "inconsistent_accept_count": inconsistent_accept_count,
        "profile_histogram": _counter_to_dict(profile_histogram),
        "boundary_family_histogram": _counter_to_dict(family_histogram),
        "limit_status_histogram": _counter_to_dict(status_histogram),
        "missing_profiles": missing_profiles,
        "uneven_profiles": uneven_profiles,
        "error_histogram": _counter_to_dict(error_histogram),
        "candidate_error_histogram": _counter_to_dict(candidate_error_histogram),
        "scenarios": scenario_results,
        "boundary": "Surface-boundary sweep audits fee, funding, and router exact-limit behavior; deterministic gates still decide execution.",
    }


def _replay_negative_controls(policy: Mapping[str, Any], *, label: str) -> dict[str, Any]:
    controls = _negative_controls(policy)
    observation = _observation_for_bins(3, 2, 2)
    surface_state = _base_surface_state()
    approved_count = 0
    missing_expected_error_count = 0
    invalid_accept_count = 0
    error_histogram: Counter[str] = Counter()
    control_results: list[dict[str, Any]] = []

    for control in controls:
        control_policy = control["policy"]
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=control_policy,
            surface_state=surface_state,
            observation=observation,
            current_epoch=34,
            proposal_epoch=10,
            last_update_epoch=32,
            expected_policy_hash=control_policy["policy_hash"],
        )
        errors = tuple(str(error) for error in result.get("errors", ()))
        for error in errors:
            error_histogram[error] += 1
        approved = result.get("approved") is True
        if approved:
            approved_count += 1
        if approved and result.get("governance_surface_all_gates_ok") is not True:
            invalid_accept_count += 1
        expected_error = str(control["expected_error"])
        has_expected_error = expected_error in errors
        if not has_expected_error:
            missing_expected_error_count += 1
        control_results.append(
            {
                "id": control["id"],
                "approved": approved,
                "action_id": result.get("action_id", ""),
                "expected_error": expected_error,
                "has_expected_error": has_expected_error,
                "errors": list(errors),
            }
        )

    return {
        "label": label,
        "scenario_count": len(controls),
        "approved_count": approved_count,
        "rejected_count": len(controls) - approved_count,
        "invalid_accept_count": invalid_accept_count,
        "missing_expected_error_count": missing_expected_error_count,
        "error_histogram": _counter_to_dict(error_histogram),
        "controls": control_results,
    }


def _training_row(
    *,
    source: str,
    scenario_id: str,
    action_id: str,
    deltas: Mapping[str, int],
    result: Mapping[str, Any],
    utility: int,
    expected_error: str | None = None,
) -> dict[str, Any]:
    errors = tuple(str(error) for error in result.get("errors", ()))
    approved = result.get("approved") is True
    row = {
        "source": source,
        "scenario_id": scenario_id,
        "action_id": action_id,
        "deltas": dict(deltas),
        "label": "accepted" if approved else "rejected",
        "approved": approved,
        "all_gates_ok": result.get("governance_surface_all_gates_ok") is True,
        "utility": utility,
        "failure_family": _failure_family(errors),
        "errors": list(errors),
        "gate_report": result.get("governance_surface_gate_report", {}),
    }
    if expected_error is not None:
        row["expected_error"] = expected_error
        row["has_expected_error"] = expected_error in errors
    _attach_feature_context(row, result)
    return row


def _stable_code(value: str, *, modulus: int = 1_000_000) -> int:
    digest = hashlib.sha256(value.encode("utf-8")).hexdigest()
    return int(digest[:12], 16) % modulus


def _source_code(source: str) -> int:
    return {
        "normal_grid": 1,
        "intra_bin_stress": 2,
        "sequence_step": 3,
        "negative_control": 4,
        "safety_lane": 5,
        "safety_boundary_sweep": 6,
        "safety_interaction_sweep": 7,
        "surface_boundary_sweep": 8,
    }.get(source, 0)


def _probe_code(row: Mapping[str, Any]) -> int:
    probe = str(row.get("probe", ""))
    static_codes = {
        "bin_floor": 1,
        "bin_ceiling": 2,
        "freshness_at_limit": 3,
        "freshness_over_limit": 4,
        "divergence_at_limit": 5,
        "divergence_over_limit": 6,
        "volatility_at_limit": 7,
        "volatility_over_limit": 8,
        "liquidity_at_floor": 9,
        "liquidity_below_floor": 10,
        "cooldown_at_limit": 11,
        "cooldown_under_limit": 12,
        "fee_floor_inside": 50,
        "fee_floor_at_limit": 51,
        "fee_cap_inside": 52,
        "fee_cap_at_limit": 53,
        "funding_floor_inside": 54,
        "funding_floor_at_limit": 55,
        "funding_cap_inside": 56,
        "funding_cap_at_limit": 57,
        "reserve_cap_inside": 58,
        "reserve_cap_at_limit": 59,
        "buyburn_cap_inside": 60,
        "buyburn_cap_at_limit": 61,
    }
    if probe in static_codes:
        return static_codes[probe]
    if str(row.get("source", "")) == "sequence_step" and probe:
        return 1_000_000 + _stable_code(probe, modulus=1_000_000)
    if str(row.get("source", "")) == "safety_interaction_sweep":
        return 100 + _stable_code(probe, modulus=900_000)
    return 0


def _int_mapping_value(raw: Any, key: str, default: int = 0) -> int:
    if not isinstance(raw, Mapping):
        return default
    value = raw.get(key, default)
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else default


def _feature_vector_from_row(row: Mapping[str, Any]) -> list[int]:
    state_bins = row.get("_feature_state_bins", {})
    observation = row.get("_feature_observation", {})
    surface_state = row.get("_feature_surface_state", {})
    deltas = row.get("deltas", {})
    vector = [
        _source_code(str(row.get("source", ""))),
        _stable_code(str(row.get("action_id", ""))),
        _probe_code(row),
    ]
    vector.extend(_int_mapping_value(state_bins, field) for field in STATE_BIN_FEATURE_FIELDS)
    vector.extend(_int_mapping_value(observation, field) for field in OBSERVATION_FEATURE_FIELDS)
    vector.extend(_int_mapping_value(surface_state, field) for field in SURFACE_FEATURE_FIELDS)
    vector.extend(_int_mapping_value(deltas, field) for field in SURFACE_FEATURE_FIELDS)
    vector.append(_row_policy_score(row))
    vector.append(_row_policy_rank(row))
    return vector


def _attach_feature_context(row: dict[str, Any], result: Mapping[str, Any]) -> None:
    row["_feature_state_bins"] = dict(result.get("state_bins", {})) if isinstance(result.get("state_bins"), Mapping) else {}
    row["_feature_observation"] = dict(result.get("observation", {})) if isinstance(result.get("observation"), Mapping) else {}
    row["_feature_surface_state"] = (
        dict(result.get("surface_state", {})) if isinstance(result.get("surface_state"), Mapping) else {}
    )


def _annotate_feature_vectors(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Attach pre-decision numeric EBRM features and audit leakage boundaries."""

    row_count = 0
    missing_vector_count = 0
    wrong_length_count = 0
    non_numeric_value_count = 0
    private_context_removed_count = 0
    vector_hash = hashlib.sha256()
    split_histogram: dict[str, Counter[str]] = {"train": Counter(), "validation": Counter()}
    source_histogram: Counter[str] = Counter()
    leaked_feature_name_tokens = tuple(
        name
        for name in EBR_FEATURE_NAMES
        if name not in ALLOWED_FEATURE_NAME_TOKEN_EXCEPTIONS
        for token in FORBIDDEN_FEATURE_NAME_TOKENS
        if token in name
    )
    forbidden_source_intersection = tuple(
        field for field in FEATURE_CONTRACT_FORBIDDEN_SOURCES if field in EBR_FEATURE_NAMES
    )

    for row in rows:
        vector = _feature_vector_from_row(row)
        row["feature_vector"] = vector
        row_count += 1
        if not vector:
            missing_vector_count += 1
        if len(vector) != len(EBR_FEATURE_NAMES):
            wrong_length_count += 1
        non_numeric_value_count += sum(
            1 for value in vector if not isinstance(value, int) or isinstance(value, bool)
        )
        vector_hash.update(json.dumps(vector, separators=(",", ":")).encode("utf-8"))
        split = str(row.get("split", ""))
        source = str(row.get("source", ""))
        source_histogram[source] += 1
        if split in split_histogram:
            split_histogram[split][source] += 1
        for key in ("_feature_state_bins", "_feature_observation", "_feature_surface_state"):
            if key in row:
                private_context_removed_count += 1
                row.pop(key, None)

    checks = {
        "feature_names_nonempty": len(EBR_FEATURE_NAMES) > 0,
        "feature_vectors_present": missing_vector_count == 0,
        "feature_vector_lengths_fixed": wrong_length_count == 0,
        "feature_values_numeric": non_numeric_value_count == 0,
        "forbidden_feature_name_tokens_absent": not leaked_feature_name_tokens,
        "forbidden_source_fields_absent_from_feature_names": not forbidden_source_intersection,
        "private_feature_context_removed": private_context_removed_count == row_count * 3,
        "train_feature_rows_present": sum(split_histogram["train"].values()) > 0,
        "validation_feature_rows_present": sum(split_histogram["validation"].values()) > 0,
    }
    return {
        "schema": EBR_TRAINING_FEATURE_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "feature_names": EBR_FEATURE_NAMES,
        "feature_count": len(EBR_FEATURE_NAMES),
        "row_count": row_count,
        "feature_vector_count": row_count - missing_vector_count,
        "missing_vector_count": missing_vector_count,
        "wrong_length_count": wrong_length_count,
        "non_numeric_value_count": non_numeric_value_count,
        "leaked_feature_name_tokens": leaked_feature_name_tokens,
        "forbidden_source_intersection": forbidden_source_intersection,
        "allowed_source_fields": FEATURE_CONTRACT_ALLOWED_SOURCES,
        "forbidden_source_fields": FEATURE_CONTRACT_FORBIDDEN_SOURCES,
        "private_context_removed_count": private_context_removed_count,
        "source_histogram": _counter_to_dict(source_histogram),
        "source_histogram_by_split": {
            split: _counter_to_dict(counter) for split, counter in split_histogram.items()
        },
        "feature_vector_sha256": "0x" + vector_hash.hexdigest(),
        "boundary": "Feature vectors contain pre-decision context and action features only; verifier labels and targets remain separate.",
    }


def _feature_vector_key(row: Mapping[str, Any]) -> tuple[int, ...]:
    vector = row.get("feature_vector", ())
    if not isinstance(vector, list):
        return ()
    out: list[int] = []
    for value in vector:
        if not isinstance(value, int) or isinstance(value, bool):
            return ()
        out.append(int(value))
    return tuple(out)


def _training_diversity_diagnostics(
    *,
    rows: list[dict[str, Any]],
    action_ids: tuple[str, ...],
) -> dict[str, Any]:
    """Audit training-set diversity so the residual is not promoted on repeated prototypes."""

    candidate_sources = set(CANDIDATE_TRAINING_SOURCES)
    required_target_classes = (
        "frontier",
        "admissible_dominated",
        "gate_rejected",
        "no_accept_rejected",
        "selection_blocked",
        "negative_control",
        "safety_lane",
    )

    row_count = len(rows)
    vector_counter: Counter[tuple[int, ...]] = Counter()
    source_histogram: Counter[str] = Counter()
    target_histogram: Counter[str] = Counter()
    action_histogram: Counter[str] = Counter()
    failure_family_histogram: Counter[str] = Counter()
    source_vector_sets: dict[str, set[tuple[int, ...]]] = {}
    source_target_histograms: dict[str, Counter[str]] = {}
    split_target_histograms: dict[str, Counter[str]] = {"train": Counter(), "validation": Counter()}
    candidate_group_ids: set[str] = set()
    missing_feature_vector_count = 0

    for row in rows:
        source = str(row.get("source", ""))
        target_class = str(row.get("target_class", ""))
        action_id = str(row.get("action_id", ""))
        failure_family = str(row.get("failure_family", ""))
        split = str(row.get("split", ""))
        vector_key = _feature_vector_key(row)
        if not vector_key:
            missing_feature_vector_count += 1
        else:
            vector_counter[vector_key] += 1
            source_vector_sets.setdefault(source, set()).add(vector_key)

        source_histogram[source] += 1
        target_histogram[target_class] += 1
        action_histogram[action_id] += 1
        source_target_histograms.setdefault(source, Counter())[target_class] += 1
        if split in split_target_histograms:
            split_target_histograms[split][target_class] += 1
        if failure_family:
            failure_family_histogram[failure_family] += 1
        if source in candidate_sources:
            candidate_group_ids.add(f"{source}:{row.get('scenario_id', '')}")

    unique_feature_vector_count = len(vector_counter)
    duplicate_feature_vector_count = sum(count - 1 for count in vector_counter.values() if count > 1)
    duplicate_feature_vector_ppm = (
        (duplicate_feature_vector_count * 1_000_000) // row_count if row_count else 0
    )
    unique_feature_vector_ppm = (
        (unique_feature_vector_count * 1_000_000) // row_count if row_count else 0
    )
    max_duplicate_count = max(vector_counter.values()) if vector_counter else 0
    missing_target_classes = tuple(
        target for target in required_target_classes if int(target_histogram.get(target, 0)) == 0
    )
    split_missing_target_classes = {
        split: tuple(
            target
            for target in required_target_classes
            if int(histogram.get(target, 0)) == 0
        )
        for split, histogram in split_target_histograms.items()
    }
    source_unique_feature_vector_counts = {
        source: len(source_vector_sets.get(source, set())) for source in sorted(source_histogram)
    }
    source_duplicate_feature_vector_counts = {
        source: int(source_histogram[source]) - source_unique_feature_vector_counts.get(source, 0)
        for source in sorted(source_histogram)
    }
    hard_negative_failure_families = tuple(
        family
        for family in sorted(failure_family_histogram)
        if family.startswith("governance_surface_gate_rejected:")
        or family.startswith("anti_oscillation:")
        or family.startswith("trajectory_budget_exceeded:")
    )
    expected_candidate_group_count = _expected_candidate_group_count()
    checks = {
        "rows_present": row_count > 0,
        "feature_vectors_present": missing_feature_vector_count == 0,
        "unique_feature_vector_ratio_high": unique_feature_vector_ppm >= 950_000,
        "duplicate_feature_vector_rate_bounded": duplicate_feature_vector_ppm <= 50_000,
        "no_single_vector_dominates": max_duplicate_count <= 10,
        "required_target_classes_present": not missing_target_classes,
        "target_classes_present_in_train": not split_missing_target_classes["train"],
        "target_classes_present_in_validation": not split_missing_target_classes["validation"],
        "all_actions_present": all(int(action_histogram.get(action_id, 0)) > 0 for action_id in action_ids),
        "normal_grid_vectors_unique_per_row": (
            source_unique_feature_vector_counts.get("normal_grid", 0)
            == int(source_histogram.get("normal_grid", 0))
        ),
        "intra_bin_vectors_unique_per_row": (
            source_unique_feature_vector_counts.get("intra_bin_stress", 0)
            == int(source_histogram.get("intra_bin_stress", 0))
        ),
        "sequence_vectors_diverse": source_unique_feature_vector_counts.get("sequence_step", 0) >= 100,
        "safety_boundary_vectors_unique_per_row": (
            source_unique_feature_vector_counts.get("safety_boundary_sweep", 0)
            == int(source_histogram.get("safety_boundary_sweep", 0))
        ),
        "safety_interaction_vectors_unique_per_row": (
            source_unique_feature_vector_counts.get("safety_interaction_sweep", 0)
            == int(source_histogram.get("safety_interaction_sweep", 0))
        ),
        "surface_boundary_vectors_unique_per_row": (
            source_unique_feature_vector_counts.get("surface_boundary_sweep", 0)
            == int(source_histogram.get("surface_boundary_sweep", 0))
        ),
        "candidate_groups_complete": len(candidate_group_ids) == expected_candidate_group_count,
        "failure_families_diverse": len(failure_family_histogram) >= 8,
        "hard_negative_families_diverse": len(hard_negative_failure_families) >= 5,
    }
    return {
        "schema": EBR_TRAINING_DIVERSITY_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "row_count": row_count,
        "unique_feature_vector_count": unique_feature_vector_count,
        "unique_feature_vector_ppm": unique_feature_vector_ppm,
        "duplicate_feature_vector_count": duplicate_feature_vector_count,
        "duplicate_feature_vector_ppm": duplicate_feature_vector_ppm,
        "max_duplicate_feature_vector_count": max_duplicate_count,
        "missing_feature_vector_count": missing_feature_vector_count,
        "candidate_group_count": len(candidate_group_ids),
        "expected_candidate_group_count": expected_candidate_group_count,
        "required_target_classes": required_target_classes,
        "missing_target_classes": missing_target_classes,
        "split_missing_target_classes": split_missing_target_classes,
        "source_histogram": _counter_to_dict(source_histogram),
        "target_class_histogram": _counter_to_dict(target_histogram),
        "action_histogram": _counter_to_dict(action_histogram),
        "failure_family_histogram": _counter_to_dict(failure_family_histogram),
        "hard_negative_failure_families": hard_negative_failure_families,
        "source_unique_feature_vector_counts": source_unique_feature_vector_counts,
        "source_duplicate_feature_vector_counts": source_duplicate_feature_vector_counts,
        "source_target_class_histograms": {
            source: _counter_to_dict(histogram)
            for source, histogram in sorted(source_target_histograms.items())
        },
        "split_target_class_histograms": {
            split: _counter_to_dict(histogram)
            for split, histogram in split_target_histograms.items()
        },
        "boundary": "Diversity diagnostics audit offline training coverage only; deterministic gates still decide execution.",
    }


SUPERVISION_TARGET_FIELDS = (
    "target_class",
    "group_has_accepted_action",
    "frontier_action_id",
    "frontier_utility",
    "is_frontier",
    "utility_regret_to_frontier",
    "score_gap_to_frontier",
    "rank_gap_to_frontier",
)


def _row_policy_score(row: Mapping[str, Any]) -> int:
    value = row.get("policy_score", 0)
    return int(value) if isinstance(value, int) else 0


def _row_policy_rank(row: Mapping[str, Any]) -> int:
    value = row.get("policy_rank", 0)
    return int(value) if isinstance(value, int) else 0


def _row_utility(row: Mapping[str, Any]) -> int:
    value = row.get("utility", 0)
    return int(value) if isinstance(value, int) else 0


def _target_class_for_row(
    *,
    row: Mapping[str, Any],
    group_has_accept: bool,
    is_frontier: bool,
) -> str:
    if row.get("selection_blocked") is True:
        return "selection_blocked"
    if row.get("approved") is True:
        return "frontier" if is_frontier else "admissible_dominated"
    if not group_has_accept:
        return "no_accept_rejected"
    return "gate_rejected"


def _annotate_candidate_group_supervision(rows: list[dict[str, Any]]) -> None:
    accepted_rows = [row for row in rows if row.get("approved") is True]
    group_has_accept = bool(accepted_rows)
    if accepted_rows:
        frontier_utility = max(_row_utility(row) for row in accepted_rows)
        frontier_rows = [
            row for row in accepted_rows if _row_utility(row) == frontier_utility
        ]
        frontier_rows.sort(
            key=lambda row: (
                _row_policy_rank(row) if _row_policy_rank(row) > 0 else 10_000,
                -_row_policy_score(row),
                str(row.get("action_id", "")),
            )
        )
        frontier_action_id = str(frontier_rows[0].get("action_id", ""))
        frontier_score = _row_policy_score(frontier_rows[0])
        frontier_rank = _row_policy_rank(frontier_rows[0])
    else:
        frontier_utility = 0
        frontier_action_id = ""
        frontier_score = 0
        frontier_rank = 0

    for row in rows:
        is_frontier = (
            group_has_accept
            and row.get("approved") is True
            and _row_utility(row) == frontier_utility
        )
        row["target_class"] = _target_class_for_row(
            row=row,
            group_has_accept=group_has_accept,
            is_frontier=is_frontier,
        )
        row["group_has_accepted_action"] = group_has_accept
        row["frontier_action_id"] = frontier_action_id
        row["frontier_utility"] = frontier_utility
        row["is_frontier"] = is_frontier
        row["utility_regret_to_frontier"] = max(0, frontier_utility - _row_utility(row))
        row["score_gap_to_frontier"] = frontier_score - _row_policy_score(row)
        row["rank_gap_to_frontier"] = (
            _row_policy_rank(row) - frontier_rank
            if frontier_rank > 0 and _row_policy_rank(row) > 0
            else 0
        )


def _annotate_supervision_targets(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Attach verifier-derived EBRM training targets to every corpus row."""

    candidate_sources = set(CANDIDATE_TRAINING_SOURCES)
    rows_by_group: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        source = str(row.get("source", ""))
        if source not in candidate_sources:
            continue
        scenario_id = str(row.get("scenario_id", ""))
        rows_by_group.setdefault(f"{source}:{scenario_id}", []).append(row)

    for group_rows in rows_by_group.values():
        _annotate_candidate_group_supervision(group_rows)

    for row in rows:
        if str(row.get("source", "")) in candidate_sources:
            continue
        source = str(row.get("source", ""))
        row["target_class"] = source if source in {"negative_control", "safety_lane"} else "non_candidate"
        row["group_has_accepted_action"] = False
        row["frontier_action_id"] = ""
        row["frontier_utility"] = 0
        row["is_frontier"] = False
        row["utility_regret_to_frontier"] = 0
        row["score_gap_to_frontier"] = 0
        row["rank_gap_to_frontier"] = 0

    target_histogram: Counter[str] = Counter()
    missing_target_field_count = 0
    frontier_row_count = 0
    accepted_nonfrontier_count = 0
    gate_rejected_target_count = 0
    no_accept_target_count = 0
    selection_blocked_target_count = 0
    negative_control_target_count = 0
    safety_lane_target_count = 0
    negative_regret_count = 0
    negative_rank_gap_count = 0
    selection_blocked_negative_rank_gap_count = 0
    candidate_group_count = len(rows_by_group)
    accepting_candidate_group_count = 0
    no_accept_candidate_group_count = 0
    candidate_rows_missing_policy_rank = 0

    for group_rows in rows_by_group.values():
        if any(row.get("group_has_accepted_action") is True for row in group_rows):
            accepting_candidate_group_count += 1
        else:
            no_accept_candidate_group_count += 1

    for row in rows:
        for field in SUPERVISION_TARGET_FIELDS:
            if field not in row:
                missing_target_field_count += 1
        target_class = str(row.get("target_class", ""))
        target_histogram[target_class] += 1
        if row.get("is_frontier") is True:
            frontier_row_count += 1
        if target_class == "admissible_dominated":
            accepted_nonfrontier_count += 1
        elif target_class == "gate_rejected":
            gate_rejected_target_count += 1
        elif target_class == "no_accept_rejected":
            no_accept_target_count += 1
        elif target_class == "selection_blocked":
            selection_blocked_target_count += 1
        elif target_class == "negative_control":
            negative_control_target_count += 1
        elif target_class == "safety_lane":
            safety_lane_target_count += 1
        if int(row.get("utility_regret_to_frontier", 0)) < 0:
            negative_regret_count += 1
        if int(row.get("rank_gap_to_frontier", 0)) < 0:
            if row.get("selection_blocked") is True:
                selection_blocked_negative_rank_gap_count += 1
            else:
                negative_rank_gap_count += 1
        if str(row.get("source", "")) in candidate_sources and int(row.get("policy_rank", 0) or 0) <= 0:
            candidate_rows_missing_policy_rank += 1

    expected_group_count = _expected_candidate_group_count()
    checks = {
        "target_fields_present": missing_target_field_count == 0,
        "candidate_group_count_matches": candidate_group_count == expected_group_count,
        "frontier_rows_present": frontier_row_count > 0,
        "accepted_nonfrontier_rows_present": accepted_nonfrontier_count > 0,
        "gate_rejected_targets_present": gate_rejected_target_count > 0,
        "no_accept_targets_present": no_accept_target_count > 0,
        "selection_blocked_targets_present": selection_blocked_target_count > 0,
        "negative_control_targets_present": negative_control_target_count == len(REQUIRED_NEGATIVE_CONTROLS),
        "safety_lane_targets_present": safety_lane_target_count == len(REQUIRED_SAFETY_LANES),
        "utility_regret_nonnegative": negative_regret_count == 0,
        "rank_gap_nonnegative": negative_rank_gap_count == 0,
        "candidate_policy_ranks_present": candidate_rows_missing_policy_rank == 0,
    }
    return {
        "schema": EBR_TRAINING_SUPERVISION_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "target_class_histogram": _counter_to_dict(target_histogram),
        "candidate_group_count": candidate_group_count,
        "expected_candidate_group_count": expected_group_count,
        "accepting_candidate_group_count": accepting_candidate_group_count,
        "no_accept_candidate_group_count": no_accept_candidate_group_count,
        "frontier_row_count": frontier_row_count,
        "accepted_nonfrontier_count": accepted_nonfrontier_count,
        "gate_rejected_target_count": gate_rejected_target_count,
        "no_accept_target_count": no_accept_target_count,
        "selection_blocked_target_count": selection_blocked_target_count,
        "negative_control_target_count": negative_control_target_count,
        "safety_lane_target_count": safety_lane_target_count,
        "missing_target_field_count": missing_target_field_count,
        "negative_regret_count": negative_regret_count,
        "negative_rank_gap_count": negative_rank_gap_count,
        "selection_blocked_negative_rank_gap_count": selection_blocked_negative_rank_gap_count,
        "candidate_rows_missing_policy_rank": candidate_rows_missing_policy_rank,
        "boundary": "Supervision targets are verifier-derived training labels only; deterministic gates still decide acceptance.",
    }


def _margin_summary(values: list[int]) -> dict[str, int]:
    if not values:
        return {"count": 0, "min": 0, "p05": 0, "p50": 0, "p95": 0, "max": 0}
    ordered = sorted(values)

    def percentile(value: int) -> int:
        index = int(((len(ordered) - 1) * value) / 100)
        return ordered[index]

    return {
        "count": len(ordered),
        "min": ordered[0],
        "p05": percentile(5),
        "p50": percentile(50),
        "p95": percentile(95),
        "max": ordered[-1],
    }


def _entropy_mass_from_gap(gap: int) -> float:
    exponent = -float(gap) / float(ENTROPY_TEMPERATURE_SCORE)
    if exponent > 50.0:
        exponent = 50.0
    return math.exp(exponent)


def _training_entropy_diagnostics(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Measure whether score margins beat candidate-pool breadth."""

    candidate_sources = set(CANDIDATE_TRAINING_SOURCES)
    hard_negative_classes = {"gate_rejected", "selection_blocked"}
    rows_by_group: dict[str, dict[str, dict[str, Any]]] = {}
    for row in rows:
        source = str(row.get("source", ""))
        if source not in candidate_sources:
            continue
        scenario_id = str(row.get("scenario_id", ""))
        action_id = str(row.get("action_id", ""))
        rows_by_group.setdefault(f"{source}:{scenario_id}", {})[action_id] = row

    expected_group_count = _expected_candidate_group_count()
    accepting_group_count = 0
    no_accept_group_count = 0
    missing_frontier_action_count = 0
    negative_margin_count = 0
    selection_blocked_negative_margin_count = 0
    nonfinite_entropy_count = 0
    actual_calls_to_frontier_total = 0
    actual_calls_to_frontier_max = 0
    entropy_mass_total = 0.0
    hard_negative_entropy_mass_total = 0.0
    selection_blocked_entropy_mass_total = 0.0
    max_group_entropy_mass = 0.0
    hard_negative_margins: list[int] = []
    dominated_margins: list[int] = []
    all_nonfrontier_margins: list[int] = []
    source_entropy_mass: Counter[str] = Counter()
    source_accepting_groups: Counter[str] = Counter()
    target_class_entropy_mass: dict[str, float] = {}
    target_class_margin_histogram: Counter[str] = Counter()

    for group_id, group_rows in rows_by_group.items():
        accepted = [row for row in group_rows.values() if row.get("approved") is True]
        if not accepted:
            no_accept_group_count += 1
            continue
        accepting_group_count += 1
        source = group_id.split(":", 1)[0]
        source_accepting_groups[source] += 1
        sample_row = next(iter(group_rows.values()))
        frontier_action_id = str(sample_row.get("frontier_action_id", ""))
        frontier_row = group_rows.get(frontier_action_id)
        if frontier_row is None:
            missing_frontier_action_count += 1
            continue
        frontier_rank = _row_policy_rank(frontier_row)
        actual_calls = 1 + sum(
            1
            for row in group_rows.values()
            if row.get("selection_blocked") is not True
            and _row_policy_rank(row) > 0
            and frontier_rank > 0
            and _row_policy_rank(row) < frontier_rank
        )
        actual_calls_to_frontier_total += actual_calls
        actual_calls_to_frontier_max = max(actual_calls_to_frontier_max, actual_calls)

        group_entropy_mass = 0.0
        for row in group_rows.values():
            if row.get("is_frontier") is True:
                continue
            target_class = str(row.get("target_class", ""))
            gap = int(row.get("score_gap_to_frontier", 0))
            all_nonfrontier_margins.append(gap)
            target_class_margin_histogram[target_class] += 1
            if gap < 0 and row.get("selection_blocked") is True:
                selection_blocked_negative_margin_count += 1
            elif gap < 0:
                negative_margin_count += 1
            if target_class in hard_negative_classes and row.get("selection_blocked") is not True:
                hard_negative_margins.append(gap)
            elif target_class == "admissible_dominated":
                dominated_margins.append(gap)
            mass = _entropy_mass_from_gap(gap)
            if not math.isfinite(mass):
                nonfinite_entropy_count += 1
                continue
            target_class_entropy_mass[target_class] = target_class_entropy_mass.get(target_class, 0.0) + mass
            if row.get("selection_blocked") is True:
                selection_blocked_entropy_mass_total += mass
                continue
            group_entropy_mass += mass
            if target_class in hard_negative_classes and row.get("selection_blocked") is not True:
                hard_negative_entropy_mass_total += mass
        entropy_mass_total += group_entropy_mass
        max_group_entropy_mass = max(max_group_entropy_mass, group_entropy_mass)
        source_entropy_mass[source] += int(round(group_entropy_mass * 1_000_000))

    mean_actual_calls_to_frontier = round(
        actual_calls_to_frontier_total / max(1, accepting_group_count),
        6,
    )
    mean_entropy_mass = round(entropy_mass_total / max(1, accepting_group_count), 6)
    mean_entropy_call_bound = round(1.0 + mean_entropy_mass, 6)
    max_entropy_call_bound = round(1.0 + max_group_entropy_mass, 6)
    hard_negative_margin_summary = _margin_summary(hard_negative_margins)
    dominated_margin_summary = _margin_summary(dominated_margins)
    checks = {
        "candidate_group_count_matches": len(rows_by_group) == expected_group_count,
        "accepting_groups_present": accepting_group_count > 0,
        "frontier_action_present": missing_frontier_action_count == 0,
        "actual_frontier_calls_max_is_one": actual_calls_to_frontier_max == 1,
        "score_gaps_nonnegative": negative_margin_count == 0,
        "hard_negative_margins_positive": (
            hard_negative_margin_summary["count"] > 0
            and hard_negative_margin_summary["min"] > 0
        ),
        "dominated_margins_nonnegative": dominated_margin_summary["min"] >= 0,
        "entropy_mass_finite": nonfinite_entropy_count == 0,
        "mean_entropy_call_bound_below_exhaustive": mean_entropy_call_bound < 10.0,
    }
    return {
        "schema": EBR_TRAINING_ENTROPY_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "temperature_score_units": ENTROPY_TEMPERATURE_SCORE,
        "candidate_group_count": len(rows_by_group),
        "expected_candidate_group_count": expected_group_count,
        "accepting_group_count": accepting_group_count,
        "no_accept_group_count": no_accept_group_count,
        "missing_frontier_action_count": missing_frontier_action_count,
        "actual_calls_to_frontier_total": actual_calls_to_frontier_total,
        "actual_calls_to_frontier_max": actual_calls_to_frontier_max,
        "mean_actual_calls_to_frontier": mean_actual_calls_to_frontier,
        "entropy_mass_total": round(entropy_mass_total, 6),
        "mean_entropy_mass_per_accepting_group": mean_entropy_mass,
        "mean_entropy_call_bound": mean_entropy_call_bound,
        "max_entropy_call_bound": max_entropy_call_bound,
        "hard_negative_entropy_mass_total": round(hard_negative_entropy_mass_total, 6),
        "selection_blocked_entropy_mass_total": round(selection_blocked_entropy_mass_total, 6),
        "source_entropy_mass_x1e6": _counter_to_dict(source_entropy_mass),
        "source_accepting_group_counts": _counter_to_dict(source_accepting_groups),
        "target_class_entropy_mass": {
            key: round(value, 6) for key, value in sorted(target_class_entropy_mass.items())
        },
        "target_class_margin_histogram": _counter_to_dict(target_class_margin_histogram),
        "all_nonfrontier_margin_summary": _margin_summary(all_nonfrontier_margins),
        "hard_negative_margin_summary": hard_negative_margin_summary,
        "dominated_margin_summary": dominated_margin_summary,
        "negative_margin_count": negative_margin_count,
        "selection_blocked_negative_margin_count": selection_blocked_negative_margin_count,
        "nonfinite_entropy_count": nonfinite_entropy_count,
        "boundary": "Entropy diagnostics measure search-order margin strength only; deterministic gates still decide acceptance.",
    }


def _clamp_int(value: int, minimum: int, maximum: int) -> int:
    return max(minimum, min(maximum, value))


def _residual_layer_key(row: Mapping[str, Any]) -> str:
    vector = row.get("feature_vector", ())
    if not isinstance(vector, list):
        return ""
    pieces: list[str] = []
    for feature in TRAINED_EBR_RESIDUAL_LAYER_FEATURES:
        name = f"bin:{feature}"
        try:
            index = EBR_FEATURE_NAMES.index(name)
        except ValueError:
            return ""
        if index >= len(vector):
            return ""
        value = vector[index]
        if not isinstance(value, int) or isinstance(value, bool):
            return ""
        pieces.append(str(value))
    return "|".join(pieces)


def _residual_target_score(row: Mapping[str, Any]) -> int:
    target_class = str(row.get("target_class", ""))
    utility = _row_utility(row)
    regret = int(row.get("utility_regret_to_frontier", 0) or 0)
    rank_gap = int(row.get("rank_gap_to_frontier", 0) or 0)
    score_gap = int(row.get("score_gap_to_frontier", 0) or 0)
    if target_class == "frontier":
        return 360 + _clamp_int(utility, -150, 180)
    if target_class == "admissible_dominated":
        return (
            80
            + _clamp_int(utility, -100, 120)
            - min(regret, 240)
            - 10 * min(rank_gap, 8)
        )
    if target_class == "selection_blocked":
        return -260 - min(score_gap, 240)
    if target_class == "gate_rejected":
        return -360 - min(score_gap, 240)
    if target_class in {"no_accept_rejected", "negative_control", "safety_lane"}:
        return -500
    return -100


def _residual_action_deltas(rows: list[dict[str, Any]]) -> dict[str, dict[str, int]]:
    action_deltas: dict[str, dict[str, int]] = {}
    for row in rows:
        if not isinstance(row, Mapping):
            continue
        action_id = str(row.get("action_id", ""))
        if not action_id or action_id in action_deltas:
            continue
        deltas = row.get("deltas", {})
        if not isinstance(deltas, Mapping):
            continue
        parsed: dict[str, int] = {}
        for name, value in deltas.items():
            if isinstance(value, int) and not isinstance(value, bool):
                parsed[str(name)] = int(value)
        action_deltas[action_id] = parsed
    return action_deltas


def _residual_neutral_edge_prior_score(
    key: str,
    action_id: str,
    action_deltas: Mapping[str, Mapping[str, int]],
) -> int:
    try:
        parts = [int(part) for part in key.split("|")]
    except ValueError:
        return 0
    if len(parts) != len(TRAINED_EBR_RESIDUAL_LAYER_FEATURES):
        return 0

    feature_bins = dict(zip(TRAINED_EBR_RESIDUAL_LAYER_FEATURES, parts))
    deltas = action_deltas.get(action_id, {})
    if not isinstance(deltas, Mapping):
        return 0

    penalty = 0

    def add_if_boundary_push(feature: str, delta_name: str, *, upper_edge_bin: int | None = None) -> None:
        nonlocal penalty
        delta = deltas.get(delta_name, 0)
        if not isinstance(delta, int) or isinstance(delta, bool) or delta == 0:
            return
        bin_index = int(feature_bins.get(feature, 0))
        max_bin = TRAINED_EBR_RESIDUAL_LAYER_BIN_COUNTS[feature] - 1
        upper = max_bin if upper_edge_bin is None else upper_edge_bin
        if bin_index <= 0 and delta < 0:
            penalty += TRAINED_EBR_RESIDUAL_NEUTRAL_EDGE_PRIOR_PENALTY
        elif bin_index >= upper and delta > 0:
            penalty += TRAINED_EBR_RESIDUAL_NEUTRAL_EDGE_PRIOR_PENALTY

    add_if_boundary_push("fee_bps", "fee_bps")
    add_if_boundary_push("funding_cap_bps", "funding_cap_bps")
    add_if_boundary_push("buyburn_bps", "buyburn_bps", upper_edge_bin=2)
    add_if_boundary_push("reserve_bps", "reserve_bps", upper_edge_bin=2)
    return -penalty


def _residual_score(row: Mapping[str, Any], q_table: Mapping[str, Mapping[str, int]]) -> int:
    row_scores = q_table.get(_residual_layer_key(row), {})
    if not isinstance(row_scores, Mapping):
        return 0
    value = row_scores.get(str(row.get("action_id", "")), 0)
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else 0


def _residual_ranker_score(
    row: Mapping[str, Any],
    q_table: Mapping[str, Mapping[str, int]],
    *,
    mode: str,
) -> int:
    if mode == "policy":
        return _row_policy_score(row)
    if mode == "residual":
        return _residual_score(row, q_table)
    if mode == "hybrid":
        return _row_policy_score(row) + _residual_score(row, q_table)
    raise ValueError(f"unknown residual ranker mode: {mode}")


def _candidate_rows_by_group(rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    candidate_sources = set(CANDIDATE_TRAINING_SOURCES)
    rows_by_group: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        if str(row.get("source", "")) not in candidate_sources:
            continue
        group_id = str(row.get("split_group_id", ""))
        if not group_id:
            source = str(row.get("source", ""))
            scenario_id = str(row.get("scenario_id", ""))
            group_id = f"{source}:{scenario_id}"
        rows_by_group.setdefault(group_id, []).append(row)
    return rows_by_group


def _residual_ranker_metrics(
    rows: list[dict[str, Any]],
    q_table: Mapping[str, Mapping[str, int]],
    *,
    split: str,
    mode: str,
) -> dict[str, Any]:
    groups = {
        group_id: group_rows
        for group_id, group_rows in _candidate_rows_by_group(rows).items()
        if group_rows and str(group_rows[0].get("split", "")) == split
    }
    accepting_group_count = 0
    rank1_frontier_count = 0
    calls_to_frontier_total = 0
    calls_to_frontier_max = 0
    pair_count = 0
    pair_success_count = 0
    hard_negative_pair_count = 0
    hard_negative_pair_success_count = 0
    all_nonfrontier_margins: list[int] = []
    hard_negative_margins: list[int] = []
    selection_blocked_margins: list[int] = []
    dominated_margins: list[int] = []
    hard_negative_classes = {"gate_rejected"}

    for group_rows in groups.values():
        frontier_rows = [row for row in group_rows if row.get("is_frontier") is True]
        if not frontier_rows:
            continue
        accepting_group_count += 1
        ordered = sorted(
            group_rows,
            key=lambda row: (
                _residual_ranker_score(row, q_table, mode=mode),
                _row_policy_score(row),
                -(_row_policy_rank(row) if _row_policy_rank(row) > 0 else 10_000),
                str(row.get("action_id", "")),
            ),
            reverse=True,
        )
        executable_ordered = [
            row for row in ordered if row.get("selection_blocked") is not True
        ]
        for index, row in enumerate(executable_ordered, start=1):
            if row.get("is_frontier") is True:
                calls_to_frontier_total += index
                calls_to_frontier_max = max(calls_to_frontier_max, index)
                if index == 1:
                    rank1_frontier_count += 1
                break
        best_frontier_score = max(
            _residual_ranker_score(row, q_table, mode=mode) for row in frontier_rows
        )
        for row in group_rows:
            if row.get("is_frontier") is True:
                continue
            margin = best_frontier_score - _residual_ranker_score(row, q_table, mode=mode)
            pair_count += 1
            if margin > 0:
                pair_success_count += 1
            all_nonfrontier_margins.append(margin)
            target_class = str(row.get("target_class", ""))
            if target_class in hard_negative_classes:
                hard_negative_pair_count += 1
                hard_negative_margins.append(margin)
                if margin > 0:
                    hard_negative_pair_success_count += 1
            elif target_class == "selection_blocked":
                selection_blocked_margins.append(margin)
            elif target_class == "admissible_dominated":
                dominated_margins.append(margin)

    mean_calls = round(calls_to_frontier_total / max(1, accepting_group_count), 6)
    return {
        "split": split,
        "mode": mode,
        "candidate_group_count": len(groups),
        "accepting_group_count": accepting_group_count,
        "rank1_frontier_count": rank1_frontier_count,
        "calls_to_frontier_total": calls_to_frontier_total,
        "calls_to_frontier_max": calls_to_frontier_max,
        "mean_calls_to_frontier": mean_calls,
        "pair_count": pair_count,
        "pair_success_count": pair_success_count,
        "pairwise_accuracy": round(pair_success_count / max(1, pair_count), 6),
        "hard_negative_pair_count": hard_negative_pair_count,
        "hard_negative_pair_success_count": hard_negative_pair_success_count,
        "hard_negative_accuracy": round(
            hard_negative_pair_success_count / max(1, hard_negative_pair_count),
            6,
        ),
        "all_nonfrontier_margin_summary": _margin_summary(all_nonfrontier_margins),
        "hard_negative_margin_summary": _margin_summary(hard_negative_margins),
        "selection_blocked_margin_summary": _margin_summary(selection_blocked_margins),
        "dominated_margin_summary": _margin_summary(dominated_margins),
    }


def _residual_candidate_action_ids(rows: list[dict[str, Any]]) -> tuple[str, ...]:
    candidate_sources = set(CANDIDATE_TRAINING_SOURCES)
    return tuple(
        sorted(
            {
                str(row.get("action_id", ""))
                for row in rows
                if isinstance(row, dict)
                and str(row.get("source", "")) in candidate_sources
                and isinstance(row.get("action_id", ""), str)
                and str(row.get("action_id", ""))
            }
        )
    )


def _residual_layer_all_keys() -> tuple[str, ...]:
    ranges = [
        range(TRAINED_EBR_RESIDUAL_LAYER_BIN_COUNTS[feature])
        for feature in TRAINED_EBR_RESIDUAL_LAYER_FEATURES
    ]
    return tuple("|".join(str(part) for part in key_parts) for key_parts in product(*ranges))


def _complete_residual_q_table(
    learned_q_table: Mapping[str, Mapping[str, int]],
    *,
    action_ids: tuple[str, ...],
) -> tuple[dict[str, dict[str, int]], dict[str, Any]]:
    all_keys = _residual_layer_all_keys()
    all_key_set = set(all_keys)
    neutral_row = {action_id: 0 for action_id in action_ids}
    completed: dict[str, dict[str, int]] = {}
    missing_action_fill_count = 0

    extra_keys = tuple(sorted(str(key) for key in learned_q_table if str(key) not in all_key_set))
    for key in sorted(str(key) for key in learned_q_table if str(key) in all_key_set):
        raw_row = learned_q_table.get(key, {})
        if not isinstance(raw_row, Mapping):
            completed[key] = dict(neutral_row)
            missing_action_fill_count += len(action_ids)
            continue
        completed[key] = {
            action_id: int(raw_row.get(action_id, 0))
            if isinstance(raw_row.get(action_id, 0), int)
            and not isinstance(raw_row.get(action_id, 0), bool)
            else 0
            for action_id in action_ids
        }
        missing_action_fill_count += sum(1 for action_id in action_ids if action_id not in raw_row)
    completed["*"] = dict(neutral_row)

    learned_key_count = len(learned_q_table)
    neutral_fill_key_count = sum(1 for key in all_keys if key not in learned_q_table)
    expected_key_count = len(all_keys)
    expected_entry_count = expected_key_count * len(action_ids)
    completion = {
        "schema": "zenodex.autonomous_governance.ebr_residual_q_table_completion.v1",
        "ok": (
            bool(action_ids)
            and "*" in completed
            and all(len(row) == len(action_ids) for row in completed.values())
            and not extra_keys
        ),
        "features": TRAINED_EBR_RESIDUAL_LAYER_FEATURES,
        "bin_counts": dict(TRAINED_EBR_RESIDUAL_LAYER_BIN_COUNTS),
        "action_count": len(action_ids),
        "action_ids": action_ids,
        "expected_key_count": expected_key_count,
        "learned_key_count": learned_key_count,
        "materialized_key_count": len(completed),
        "effective_completed_key_count": expected_key_count,
        "fallback_key": "*",
        "neutral_fill_key_count": neutral_fill_key_count,
        "extra_key_count": len(extra_keys),
        "extra_keys": extra_keys,
        "learned_entry_count": sum(len(row_scores) for row_scores in learned_q_table.values()),
        "materialized_entry_count": sum(len(row_scores) for row_scores in completed.values()),
        "effective_completed_entry_count": expected_entry_count,
        "missing_action_fill_count": missing_action_fill_count,
        "boundary": "A neutral wildcard residual row completes unseen lookup-grid keys; deterministic governance gates still decide execution.",
    }
    return dict(sorted(completed.items())), completion


def _build_residual_q_table(
    rows: list[dict[str, Any]],
    *,
    train_split: str = "train",
) -> tuple[dict[str, dict[str, int]], Counter[str], dict[str, Any]]:
    accumulators: dict[tuple[str, str], list[int]] = {}
    source_histogram: Counter[str] = Counter()
    action_deltas = _residual_action_deltas(rows)
    for row in rows:
        if not isinstance(row, dict):
            continue
        if str(row.get("split", "")) != train_split:
            continue
        if str(row.get("source", "")) not in CANDIDATE_TRAINING_SOURCES:
            continue
        key = _residual_layer_key(row)
        action_id = str(row.get("action_id", ""))
        if not key or not action_id:
            continue
        bucket = accumulators.setdefault((key, action_id), [0, 0])
        bucket[0] += _residual_target_score(row)
        bucket[1] += 1
        source_histogram[str(row.get("source", ""))] += 1

    raw_table: dict[str, dict[str, int]] = {}
    for (key, action_id), (total, count) in accumulators.items():
        raw_table.setdefault(key, {})[action_id] = int(round(total / max(1, count)))

    learned_q_table: dict[str, dict[str, int]] = {}
    neutral_edge_prior_key_count = 0
    neutral_edge_prior_adjustment_count = 0
    for key, row_scores in raw_table.items():
        mean = int(round(sum(row_scores.values()) / max(1, len(row_scores))))
        centered = {
            action_id: TRAINED_EBR_RESIDUAL_SCORE_SCALE
            * _clamp_int(score - mean, -TRAINED_EBR_RESIDUAL_SCORE_CLAMP, TRAINED_EBR_RESIDUAL_SCORE_CLAMP)
            for action_id, score in sorted(row_scores.items())
        }
        if centered and all(score == 0 for score in centered.values()):
            adjusted = {
                action_id: score + _residual_neutral_edge_prior_score(key, action_id, action_deltas)
                for action_id, score in centered.items()
            }
            adjustment_count = sum(1 for action_id, score in centered.items() if adjusted[action_id] != score)
            if adjustment_count:
                neutral_edge_prior_key_count += 1
                neutral_edge_prior_adjustment_count += adjustment_count
            centered = adjusted
        learned_q_table[key] = centered
    q_table, completion = _complete_residual_q_table(
        dict(sorted(learned_q_table.items())),
        action_ids=_residual_candidate_action_ids(rows),
    )
    completion.update(
        {
            "neutral_edge_prior_enabled": True,
            "neutral_edge_prior_penalty": TRAINED_EBR_RESIDUAL_NEUTRAL_EDGE_PRIOR_PENALTY,
            "neutral_edge_prior_key_count": neutral_edge_prior_key_count,
            "neutral_edge_prior_adjustment_count": neutral_edge_prior_adjustment_count,
        }
    )
    return q_table, source_histogram, completion


def _residual_seed_fold(group_id: str, salt: str) -> int:
    digest = hashlib.sha256(f"{salt}:{group_id}".encode("utf-8")).hexdigest()
    return int(digest[:16], 16) % TRAINED_EBR_RESIDUAL_CROSS_SEED_STRIDE


def _rows_with_residual_seed_split(rows: list[dict[str, Any]], *, salt: str) -> list[dict[str, Any]]:
    seeded_rows: list[dict[str, Any]] = []
    for row in rows:
        seeded = dict(row)
        if str(row.get("source", "")) in CANDIDATE_TRAINING_SOURCES:
            group_id = str(row.get("split_group_id", ""))
            if not group_id:
                group_id = f"{row.get('source', '')}:{row.get('scenario_id', '')}"
            seeded["split"] = "validation" if _residual_seed_fold(group_id, salt) == 0 else "train"
        seeded_rows.append(seeded)
    return seeded_rows


def _residual_cross_seed_diagnostics(rows: list[dict[str, Any]]) -> dict[str, Any]:
    seed_reports: list[dict[str, Any]] = []
    nonfrontier_p50_lifts: list[int] = []
    hard_negative_p50_lifts: list[int] = []
    hard_negative_min_lifts: list[int] = []
    validation_accepting_group_counts: list[int] = []
    validation_group_counts: list[int] = []
    failing_salts: list[str] = []

    for salt in TRAINED_EBR_RESIDUAL_CROSS_SEED_SALTS:
        seeded_rows = _rows_with_residual_seed_split(rows, salt=salt)
        q_table, source_histogram, completion = _build_residual_q_table(seeded_rows)
        policy_metrics = _residual_ranker_metrics(seeded_rows, q_table, split="validation", mode="policy")
        hybrid_metrics = _residual_ranker_metrics(seeded_rows, q_table, split="validation", mode="hybrid")
        nonfrontier_lift = (
            hybrid_metrics["all_nonfrontier_margin_summary"]["p50"]
            - policy_metrics["all_nonfrontier_margin_summary"]["p50"]
        )
        hard_p50_lift = (
            hybrid_metrics["hard_negative_margin_summary"]["p50"]
            - policy_metrics["hard_negative_margin_summary"]["p50"]
        )
        hard_min_lift = (
            hybrid_metrics["hard_negative_margin_summary"]["min"]
            - policy_metrics["hard_negative_margin_summary"]["min"]
        )
        seed_checks = {
            "training_rows_present": sum(source_histogram.values()) > 0,
            "q_table_nonempty": bool(q_table),
            "q_table_complete": completion.get("ok") is True,
            "validation_groups_present": hybrid_metrics["candidate_group_count"] > 0,
            "validation_accepting_groups_present": hybrid_metrics["accepting_group_count"] > 0,
            "validation_hybrid_frontier_rank1_complete": (
                hybrid_metrics["rank1_frontier_count"] == hybrid_metrics["accepting_group_count"]
                and hybrid_metrics["accepting_group_count"] > 0
            ),
            "validation_hybrid_calls_not_worse_than_policy": (
                hybrid_metrics["calls_to_frontier_max"] <= policy_metrics["calls_to_frontier_max"]
                and hybrid_metrics["mean_calls_to_frontier"] <= policy_metrics["mean_calls_to_frontier"]
            ),
            "validation_hybrid_nonfrontier_p50_improves_policy": nonfrontier_lift > 0,
            "validation_hybrid_hard_negative_p50_improves_policy": hard_p50_lift > 0,
            "validation_hybrid_hard_negative_margin_positive": (
                hybrid_metrics["hard_negative_margin_summary"]["count"] > 0
                and hybrid_metrics["hard_negative_margin_summary"]["min"] > 0
            ),
        }
        if not all(seed_checks.values()):
            failing_salts.append(salt)
        nonfrontier_p50_lifts.append(nonfrontier_lift)
        hard_negative_p50_lifts.append(hard_p50_lift)
        hard_negative_min_lifts.append(hard_min_lift)
        validation_accepting_group_counts.append(int(hybrid_metrics["accepting_group_count"]))
        validation_group_counts.append(int(hybrid_metrics["candidate_group_count"]))
        seed_reports.append(
            {
                "salt": salt,
                "ok": all(seed_checks.values()),
                "checks": seed_checks,
                "q_table_completion": completion,
                "q_table_learned_key_count": completion.get("learned_key_count", 0),
                "q_table_materialized_key_count": completion.get("materialized_key_count", len(q_table)),
                "q_table_effective_completed_key_count": completion.get(
                    "effective_completed_key_count",
                    len(q_table),
                ),
                "q_table_neutral_fill_key_count": completion.get("neutral_fill_key_count", 0),
                "q_table_key_count": len(q_table),
                "q_table_entry_count": sum(len(row_scores) for row_scores in q_table.values()),
                "q_table_sha256": _sha256_json(q_table),
                "training_source_histogram": _counter_to_dict(source_histogram),
                "policy": policy_metrics,
                "hybrid": hybrid_metrics,
                "nonfrontier_p50_lift": nonfrontier_lift,
                "hard_negative_p50_lift": hard_p50_lift,
                "hard_negative_min_lift": hard_min_lift,
            }
        )

    checks = {
        "seed_count_matches": len(seed_reports) == len(TRAINED_EBR_RESIDUAL_CROSS_SEED_SALTS),
        "all_seed_checks_pass": not failing_salts,
        "validation_groups_present_all_seeds": bool(validation_group_counts) and min(validation_group_counts) > 0,
        "validation_accepting_groups_present_all_seeds": (
            bool(validation_accepting_group_counts) and min(validation_accepting_group_counts) > 0
        ),
        "nonfrontier_p50_lift_positive_all_seeds": (
            bool(nonfrontier_p50_lifts) and min(nonfrontier_p50_lifts) > 0
        ),
        "hard_negative_p50_lift_positive_all_seeds": (
            bool(hard_negative_p50_lifts) and min(hard_negative_p50_lifts) > 0
        ),
        "hard_negative_margin_positive_all_seeds": (
            bool(seed_reports)
            and all(seed["hybrid"]["hard_negative_margin_summary"]["min"] > 0 for seed in seed_reports)
        ),
    }
    return {
        "schema": "zenodex.autonomous_governance.ebr_residual_cross_seed_diagnostics.v1",
        "ok": all(checks.values()),
        "checks": checks,
        "stride": TRAINED_EBR_RESIDUAL_CROSS_SEED_STRIDE,
        "salts": TRAINED_EBR_RESIDUAL_CROSS_SEED_SALTS,
        "failing_salts": tuple(failing_salts),
        "seed_count": len(seed_reports),
        "min_validation_group_count": min(validation_group_counts) if validation_group_counts else 0,
        "min_validation_accepting_group_count": (
            min(validation_accepting_group_counts) if validation_accepting_group_counts else 0
        ),
        "min_nonfrontier_p50_lift": min(nonfrontier_p50_lifts) if nonfrontier_p50_lifts else 0,
        "min_hard_negative_p50_lift": min(hard_negative_p50_lifts) if hard_negative_p50_lifts else 0,
        "min_hard_negative_min_lift": min(hard_negative_min_lifts) if hard_negative_min_lifts else 0,
        "seeds": seed_reports,
        "boundary": "Cross-seed diagnostics stress offline residual ranking only; deterministic gates still decide execution.",
    }


def _train_ebr_residual_lookup_model(training_corpus: Mapping[str, Any]) -> dict[str, Any]:
    rows = list(training_corpus.get("rows", [])) if isinstance(training_corpus.get("rows", []), list) else []
    q_table, source_histogram, completion = _build_residual_q_table(rows)

    metrics = {
        split: {
            mode: _residual_ranker_metrics(rows, q_table, split=split, mode=mode)
            for mode in ("policy", "residual", "hybrid")
        }
        for split in ("train", "validation")
    }
    train_hybrid = metrics["train"]["hybrid"]
    validation_policy = metrics["validation"]["policy"]
    validation_hybrid = metrics["validation"]["hybrid"]
    cross_seed_diagnostics = _residual_cross_seed_diagnostics(rows)
    checks = {
        "training_rows_present": sum(source_histogram.values()) > 0,
        "q_table_nonempty": bool(q_table),
        "q_table_complete": completion.get("ok") is True,
        "train_hybrid_frontier_rank1_complete": (
            train_hybrid["rank1_frontier_count"] == train_hybrid["accepting_group_count"]
            and train_hybrid["accepting_group_count"] > 0
        ),
        "validation_hybrid_frontier_rank1_complete": (
            validation_hybrid["rank1_frontier_count"] == validation_hybrid["accepting_group_count"]
            and validation_hybrid["accepting_group_count"] > 0
        ),
        "validation_hybrid_calls_not_worse_than_policy": (
            validation_hybrid["calls_to_frontier_max"] <= validation_policy["calls_to_frontier_max"]
            and validation_hybrid["mean_calls_to_frontier"] <= validation_policy["mean_calls_to_frontier"]
        ),
        "validation_hybrid_nonfrontier_p50_improves_policy": (
            validation_hybrid["all_nonfrontier_margin_summary"]["p50"]
            > validation_policy["all_nonfrontier_margin_summary"]["p50"]
        ),
        "validation_hybrid_hard_negative_min_not_worse_than_policy": (
            validation_hybrid["hard_negative_margin_summary"]["min"]
            >= validation_policy["hard_negative_margin_summary"]["min"]
        ),
        "validation_hybrid_hard_negative_accuracy_not_worse_than_policy": (
            validation_hybrid["hard_negative_accuracy"] >= validation_policy["hard_negative_accuracy"]
        ),
        "validation_hybrid_hard_negative_margin_positive": (
            validation_hybrid["hard_negative_margin_summary"]["count"] > 0
            and validation_hybrid["hard_negative_margin_summary"]["min"] > 0
        ),
        "cross_seed_diagnostics_ok": cross_seed_diagnostics["ok"] is True,
    }
    layer = {
        "id": TRAINED_EBR_RESIDUAL_LAYER_ID,
        "features": TRAINED_EBR_RESIDUAL_LAYER_FEATURES,
        "q_table": q_table,
    }
    return {
        "schema": EBR_RESIDUAL_MODEL_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "source_policy_hash": str(training_corpus.get("policy_hash", "")),
        "feature_schema": EBR_TRAINING_FEATURE_SCHEMA,
        "layer": layer,
        "training_config": {
            "target": "frontier_vs_nonfrontier_lookup_residual",
            "split": "train",
            "score_clamp": TRAINED_EBR_RESIDUAL_SCORE_CLAMP,
            "score_scale": TRAINED_EBR_RESIDUAL_SCORE_SCALE,
            "features": TRAINED_EBR_RESIDUAL_LAYER_FEATURES,
        },
        "q_table_key_count": len(q_table),
        "q_table_learned_key_count": completion.get("learned_key_count", 0),
        "q_table_materialized_key_count": completion.get("materialized_key_count", len(q_table)),
        "q_table_effective_completed_key_count": completion.get(
            "effective_completed_key_count",
            len(q_table),
        ),
        "q_table_neutral_fill_key_count": completion.get("neutral_fill_key_count", 0),
        "q_table_entry_count": sum(len(row_scores) for row_scores in q_table.values()),
        "q_table_completion": completion,
        "training_source_histogram": _counter_to_dict(source_histogram),
        "q_table_sha256": _sha256_json(q_table),
        "metrics": metrics,
        "cross_seed_diagnostics": cross_seed_diagnostics,
        "boundary": "The trained residual is an offline ordering layer; deterministic governance gates still decide execution.",
        "non_claims": [
            "does_not_authorize_settlement",
            "does_not_replace_python_or_tau_governance_gates",
            "does_not_train_online",
            "does_not_prove_global_dynamic_optimality",
        ],
    }


def _policy_with_trained_ebr_residual(
    policy: Mapping[str, Any],
    residual_model: Mapping[str, Any],
) -> dict[str, Any]:
    candidate = copy.deepcopy(dict(policy))
    candidate.pop("policy_hash", None)
    selection = dict(candidate.get("selection", {})) if isinstance(candidate.get("selection", {}), Mapping) else {}
    trajectory = selection.get("trajectory_budget", {})
    if not isinstance(trajectory, Mapping) or trajectory.get("enabled") is not True:
        selection["trajectory_budget"] = {
            "enabled": True,
            "limits": dict(SEQUENCE_DRIFT_LIMITS),
        }
        candidate["selection"] = selection
    if residual_model.get("ok") is not True:
        return candidate
    layer = residual_model.get("layer", {})
    if not isinstance(layer, Mapping):
        return candidate
    q_layers = [
        dict(existing)
        for existing in candidate.get("q_layers", [])
        if isinstance(existing, Mapping) and existing.get("id") != TRAINED_EBR_RESIDUAL_LAYER_ID
    ]
    q_layers.append(copy.deepcopy(dict(layer)))
    candidate["q_layers"] = q_layers
    return candidate


def _split_fold(group_id: str, *, stride: int) -> int:
    digest = hashlib.sha256(group_id.encode("utf-8")).hexdigest()
    return int(digest[:16], 16) % stride


def _split_metric_template() -> dict[str, Any]:
    return {
        "candidate_group_count": 0,
        "accepting_group_count": 0,
        "no_accept_group_count": 0,
        "actual_calls_to_frontier_total": 0,
        "actual_calls_to_frontier_max": 0,
        "entropy_mass_total": 0.0,
        "selection_blocked_entropy_mass_total": 0.0,
        "hard_negative_margins": [],
        "dominated_margins": [],
        "nonfrontier_margins": [],
        "negative_margin_count": 0,
    }


def _finalize_split_metrics(metrics: Mapping[str, Any]) -> dict[str, Any]:
    accepting = int(metrics.get("accepting_group_count", 0))
    entropy_mass_total = float(metrics.get("entropy_mass_total", 0.0))
    hard_negative_margins = list(metrics.get("hard_negative_margins", []))
    dominated_margins = list(metrics.get("dominated_margins", []))
    nonfrontier_margins = list(metrics.get("nonfrontier_margins", []))
    mean_actual_calls = round(
        int(metrics.get("actual_calls_to_frontier_total", 0)) / max(1, accepting),
        6,
    )
    mean_entropy_mass = round(entropy_mass_total / max(1, accepting), 6)
    return {
        "candidate_group_count": int(metrics.get("candidate_group_count", 0)),
        "accepting_group_count": accepting,
        "no_accept_group_count": int(metrics.get("no_accept_group_count", 0)),
        "actual_calls_to_frontier_total": int(metrics.get("actual_calls_to_frontier_total", 0)),
        "actual_calls_to_frontier_max": int(metrics.get("actual_calls_to_frontier_max", 0)),
        "mean_actual_calls_to_frontier": mean_actual_calls,
        "entropy_mass_total": round(entropy_mass_total, 6),
        "selection_blocked_entropy_mass_total": round(
            float(metrics.get("selection_blocked_entropy_mass_total", 0.0)),
            6,
        ),
        "mean_entropy_mass_per_accepting_group": mean_entropy_mass,
        "mean_entropy_call_bound": round(1.0 + mean_entropy_mass, 6),
        "hard_negative_margin_summary": _margin_summary(hard_negative_margins),
        "dominated_margin_summary": _margin_summary(dominated_margins),
        "all_nonfrontier_margin_summary": _margin_summary(nonfrontier_margins),
        "negative_margin_count": int(metrics.get("negative_margin_count", 0)),
    }


def _split_source_histogram(
    group_sources: Mapping[str, str],
    group_splits: Mapping[str, str],
) -> dict[str, dict[str, int]]:
    out: dict[str, Counter[str]] = {"train": Counter(), "validation": Counter()}
    for group_id, source in group_sources.items():
        split = group_splits.get(group_id, "")
        if split in out:
            out[split][source] += 1
    return {split: _counter_to_dict(counter) for split, counter in out.items()}


def _annotate_train_validation_splits(rows: list[dict[str, Any]]) -> dict[str, Any]:
    """Attach deterministic group-level train/validation splits to corpus rows."""

    candidate_sources = set(CANDIDATE_TRAINING_SOURCES)
    hard_negative_classes = {"gate_rejected", "selection_blocked"}
    required_target_classes = (
        "frontier",
        "admissible_dominated",
        "gate_rejected",
        "no_accept_rejected",
        "selection_blocked",
        "negative_control",
        "safety_lane",
    )
    rows_by_group: dict[str, list[dict[str, Any]]] = {}
    group_sources: dict[str, str] = {}
    for row in rows:
        source = str(row.get("source", ""))
        scenario_id = str(row.get("scenario_id", ""))
        group_id = f"{source}:{scenario_id}"
        rows_by_group.setdefault(group_id, []).append(row)
        group_sources[group_id] = source

    group_splits: dict[str, str] = {}
    group_folds: dict[str, int] = {}
    for group_id in sorted(rows_by_group):
        source = group_sources[group_id]
        stride = (
            VALIDATION_STRIDE_CANDIDATE_GROUPS
            if source in candidate_sources
            else VALIDATION_STRIDE_SINGLETON_GROUPS
        )
        fold = _split_fold(group_id, stride=stride)
        group_folds[group_id] = fold
        group_splits[group_id] = "validation" if fold == 0 else "train"

    forced_validation_groups: set[str] = set()
    validation_target_classes = {
        str(row.get("target_class", ""))
        for group_id, group_rows in rows_by_group.items()
        if group_splits[group_id] == "validation"
        for row in group_rows
    }
    for target_class in required_target_classes:
        if target_class in validation_target_classes:
            continue
        for group_id in sorted(rows_by_group):
            if any(str(row.get("target_class", "")) == target_class for row in rows_by_group[group_id]):
                group_splits[group_id] = "validation"
                forced_validation_groups.add(group_id)
                validation_target_classes.add(target_class)
                break

    split_group_histogram: Counter[str] = Counter()
    split_row_histogram: Counter[str] = Counter()
    target_histograms: dict[str, Counter[str]] = {
        "train": Counter(),
        "validation": Counter(),
    }
    missing_split_field_count = 0
    group_split_leak_count = 0
    split_metrics = {
        "train": _split_metric_template(),
        "validation": _split_metric_template(),
    }

    for group_id, group_rows in rows_by_group.items():
        split = group_splits[group_id]
        split_group_histogram[split] += 1
        group_row_splits: set[str] = set()
        for row in group_rows:
            row["split"] = split
            row["split_group_id"] = group_id
            row["split_fold"] = group_folds[group_id]
            row["split_forced_validation"] = group_id in forced_validation_groups
            group_row_splits.add(str(row.get("split", "")))
            split_row_histogram[split] += 1
            target_histograms[split][str(row.get("target_class", ""))] += 1
            for field in ("split", "split_group_id", "split_fold", "split_forced_validation"):
                if field not in row:
                    missing_split_field_count += 1
        if len(group_row_splits) != 1:
            group_split_leak_count += 1

        source = group_sources[group_id]
        if source not in candidate_sources:
            continue
        by_action = {str(row.get("action_id", "")): row for row in group_rows}
        metrics = split_metrics[split]
        metrics["candidate_group_count"] += 1
        accepted = [row for row in group_rows if row.get("approved") is True]
        if not accepted:
            metrics["no_accept_group_count"] += 1
            continue
        metrics["accepting_group_count"] += 1
        frontier_action_id = str(group_rows[0].get("frontier_action_id", ""))
        frontier_row = by_action.get(frontier_action_id)
        if frontier_row is None:
            continue
        frontier_rank = _row_policy_rank(frontier_row)
        actual_calls = 1 + sum(
            1
            for row in group_rows
            if row.get("selection_blocked") is not True
            and _row_policy_rank(row) > 0
            and frontier_rank > 0
            and _row_policy_rank(row) < frontier_rank
        )
        metrics["actual_calls_to_frontier_total"] += actual_calls
        metrics["actual_calls_to_frontier_max"] = max(metrics["actual_calls_to_frontier_max"], actual_calls)
        for row in group_rows:
            if row.get("is_frontier") is True:
                continue
            target_class = str(row.get("target_class", ""))
            gap = int(row.get("score_gap_to_frontier", 0))
            metrics["nonfrontier_margins"].append(gap)
            if gap < 0 and row.get("selection_blocked") is not True:
                metrics["negative_margin_count"] += 1
            if target_class in hard_negative_classes and row.get("selection_blocked") is not True:
                metrics["hard_negative_margins"].append(gap)
            elif target_class == "admissible_dominated":
                metrics["dominated_margins"].append(gap)
            mass = _entropy_mass_from_gap(gap)
            if row.get("selection_blocked") is True:
                metrics["selection_blocked_entropy_mass_total"] += mass
            else:
                metrics["entropy_mass_total"] += mass

    train_target_classes = set(target_histograms["train"])
    validation_target_classes = set(target_histograms["validation"])
    train_metrics = _finalize_split_metrics(split_metrics["train"])
    validation_metrics = _finalize_split_metrics(split_metrics["validation"])
    expected_candidate_group_count = _expected_candidate_group_count()
    expected_total_group_count = _expected_total_group_count()
    required_source_set = set(CANDIDATE_TRAINING_SOURCES).union({"negative_control", "safety_lane"})
    source_histogram_by_split = _split_source_histogram(group_sources, group_splits)
    train_sources = set(source_histogram_by_split["train"])
    validation_sources = set(source_histogram_by_split["validation"])
    validation_hard_negative_min = validation_metrics["hard_negative_margin_summary"]["min"]
    train_hard_negative_min = train_metrics["hard_negative_margin_summary"]["min"]
    checks = {
        "split_fields_present": missing_split_field_count == 0,
        "group_count_matches": len(rows_by_group) == expected_total_group_count,
        "candidate_group_count_matches": (
            train_metrics["candidate_group_count"] + validation_metrics["candidate_group_count"]
            == expected_candidate_group_count
        ),
        "no_group_split_leakage": group_split_leak_count == 0,
        "train_rows_present": split_row_histogram.get("train", 0) > 0,
        "validation_rows_present": split_row_histogram.get("validation", 0) > 0,
        "train_sources_complete": required_source_set.issubset(train_sources),
        "validation_sources_complete": required_source_set.issubset(validation_sources),
        "train_target_classes_complete": set(required_target_classes).issubset(train_target_classes),
        "validation_target_classes_complete": set(required_target_classes).issubset(validation_target_classes),
        "validation_accepting_groups_present": validation_metrics["accepting_group_count"] > 0,
        "validation_no_accept_groups_present": validation_metrics["no_accept_group_count"] > 0,
        "validation_frontier_calls_max_is_one": validation_metrics["actual_calls_to_frontier_max"] == 1,
        "validation_hard_negative_margins_positive": (
            validation_metrics["hard_negative_margin_summary"]["count"] > 0
            and validation_hard_negative_min > 0
        ),
        "validation_entropy_bound_below_exhaustive": validation_metrics["mean_entropy_call_bound"] < 10.0,
        "train_frontier_calls_max_is_one": train_metrics["actual_calls_to_frontier_max"] == 1,
        "train_hard_negative_margins_positive": (
            train_metrics["hard_negative_margin_summary"]["count"] > 0
            and train_hard_negative_min > 0
        ),
        "train_entropy_bound_below_exhaustive": train_metrics["mean_entropy_call_bound"] < 10.0,
    }
    return {
        "schema": EBR_TRAINING_SPLIT_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "validation_stride_candidate_groups": VALIDATION_STRIDE_CANDIDATE_GROUPS,
        "validation_stride_singleton_groups": VALIDATION_STRIDE_SINGLETON_GROUPS,
        "group_count": len(rows_by_group),
        "expected_group_count": expected_total_group_count,
        "candidate_group_count": (
            train_metrics["candidate_group_count"] + validation_metrics["candidate_group_count"]
        ),
        "expected_candidate_group_count": expected_candidate_group_count,
        "forced_validation_group_count": len(forced_validation_groups),
        "group_split_leak_count": group_split_leak_count,
        "missing_split_field_count": missing_split_field_count,
        "row_count_by_split": _counter_to_dict(split_row_histogram),
        "group_count_by_split": _counter_to_dict(split_group_histogram),
        "source_group_count_by_split": source_histogram_by_split,
        "target_class_histogram_by_split": {
            split: _counter_to_dict(counter) for split, counter in target_histograms.items()
        },
        "train": train_metrics,
        "validation": validation_metrics,
        "boundary": "Train/validation split diagnostics audit offline EBRM evidence only; deterministic gates still decide acceptance.",
    }


def _action_map(policy: Mapping[str, Any]) -> dict[str, dict[str, int]]:
    out: dict[str, dict[str, int]] = {}
    for action in policy.get("actions", []):
        if not isinstance(action, Mapping):
            continue
        action_id = action.get("id")
        deltas = action.get("deltas", {})
        if isinstance(action_id, str) and isinstance(deltas, Mapping):
            out[action_id] = {str(key): int(value) for key, value in deltas.items()}
    return out


def _rank_action_ids_by_score(action_ids: tuple[str, ...], scores: Mapping[str, Any]) -> list[str]:
    order_index = {action_id: index for index, action_id in enumerate(action_ids)}

    def score(action_id: str) -> tuple[int, int]:
        raw_score = scores.get(action_id, 0)
        return (int(raw_score) if isinstance(raw_score, int) else 0, -order_index[action_id])

    return sorted(action_ids, key=score, reverse=True)


def _sequence_action_rows(
    *,
    policy: Mapping[str, Any],
    actions: Mapping[str, Mapping[str, int]],
    forced_action_policies: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Build verifier-labeled candidate rows for every long-horizon sequence step."""

    frozen = _freeze_policy(policy)
    rows: list[dict[str, Any]] = []
    for case in _sequence_cases():
        sequence_id = str(case["id"])
        state = dict(case["surface_state"])
        previous_approved_deltas: dict[str, int] = {}
        trajectory_used: dict[str, int] = {key: 0 for key in SEQUENCE_DRIFT_LIMITS}
        last_update_epoch: int | None = 75
        for index, bins in enumerate(case["bin_path"]):
            deviation_bin, volatility_bin, liquidity_bin = (int(part) for part in bins)
            observation = _observation_for_bins(deviation_bin, volatility_bin, liquidity_bin)
            overrides = case.get("observation_overrides_by_step", {})
            if isinstance(overrides, Mapping):
                observation.update(overrides.get(index, {}))
            current_epoch = 100 + (25 * index)
            proposal_epoch = current_epoch - gov_gate.MIN_DELAY
            step_scenario = {
                "id": f"{sequence_id}:step_{index}",
                "deviation_bin": deviation_bin,
                "volatility_bin": volatility_bin,
                "liquidity_bin": liquidity_bin,
                "bin_key": f"{deviation_bin}|{volatility_bin}|{liquidity_bin}",
            }
            selected = evaluate_autonomous_governance_surface_q_policy_v1(
                policy=frozen,
                surface_state=state,
                observation=observation,
                current_epoch=current_epoch,
                proposal_epoch=proposal_epoch,
                last_update_epoch=last_update_epoch,
                expected_policy_hash=frozen["policy_hash"],
                previous_approved_deltas=previous_approved_deltas,
                trajectory_used=trajectory_used,
            )
            scores = selected.get("scores", {})
            scores = scores if isinstance(scores, Mapping) else {}
            ranked_action_ids = _rank_action_ids_by_score(_action_ids(frozen), scores)
            rank_by_action = {action_id: rank for rank, action_id in enumerate(ranked_action_ids, start=1)}
            for action_id in sorted(actions):
                raw_score = scores.get(action_id, 0)
                policy_score = int(raw_score) if isinstance(raw_score, int) else 0
                blockers = _selection_blockers(
                    policy=frozen,
                    deltas=actions[action_id],
                    previous_approved_deltas=previous_approved_deltas,
                    trajectory_used=trajectory_used,
                )
                if blockers:
                    row = _training_row(
                        source="sequence_step",
                        scenario_id=f"{sequence_id}:step_{index}",
                        action_id=action_id,
                        deltas=actions[action_id],
                        result={
                            "approved": False,
                            "governance_surface_all_gates_ok": False,
                            "errors": blockers,
                            "governance_surface_gate_report": {},
                            "state_bins": (
                                dict(selected.get("state_bins", {}))
                                if isinstance(selected.get("state_bins"), Mapping)
                                else {}
                            ),
                            "observation": dict(observation),
                            "surface_state": dict(state),
                        },
                        utility=0,
                    )
                    row["selection_blocked"] = True
                    row["selection_blockers"] = list(blockers)
                    row["policy_score"] = policy_score
                    row["policy_rank"] = rank_by_action.get(action_id, 0)
                    row["probe"] = f"{sequence_id}:step_{index}"
                    rows.append(row)
                    continue
                action_policy = forced_action_policies[action_id]
                result = evaluate_autonomous_governance_surface_q_policy_v1(
                    policy=action_policy,
                    surface_state=state,
                    observation=observation,
                    current_epoch=current_epoch,
                    proposal_epoch=proposal_epoch,
                    last_update_epoch=last_update_epoch,
                    expected_policy_hash=action_policy["policy_hash"],
                )
                row = _training_row(
                    source="sequence_step",
                    scenario_id=f"{sequence_id}:step_{index}",
                    action_id=action_id,
                    deltas=actions[action_id],
                    result=result,
                    utility=_scenario_utility(step_scenario, result),
                )
                row["selection_blocked"] = False
                row["policy_score"] = policy_score
                row["policy_rank"] = rank_by_action.get(action_id, 0)
                row["probe"] = f"{sequence_id}:step_{index}"
                rows.append(row)

            if selected.get("approved") is True:
                proposed = selected.get("proposed", {})
                if isinstance(proposed, Mapping):
                    deltas = {
                        key: int(proposed.get(key, state.get(key, 0))) - int(state.get(key, 0))
                        for key in SEQUENCE_DRIFT_LIMITS
                    }
                    if any(value != 0 for value in deltas.values()):
                        previous_approved_deltas = dict(deltas)
                        last_update_epoch = current_epoch
                        for key, delta in deltas.items():
                            trajectory_used[key] = int(trajectory_used.get(key, 0)) + abs(int(delta))
                    state = {key: int(value) for key, value in proposed.items()}
    return rows


def _intra_bin_stress_action_rows(
    *,
    policy: Mapping[str, Any],
    actions: Mapping[str, Mapping[str, int]],
    forced_action_policies: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Build verifier-labeled rows for every intra-bin stress scenario and action."""

    frozen = _freeze_policy(policy)
    rows: list[dict[str, Any]] = []
    for scenario in _intra_bin_stress_scenarios():
        selected = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=34,
            proposal_epoch=10,
            last_update_epoch=32,
            expected_policy_hash=frozen["policy_hash"],
        )
        scores = selected.get("scores", {})
        scores = scores if isinstance(scores, Mapping) else {}
        ranked_action_ids = _rank_action_ids_by_score(_action_ids(frozen), scores)
        rank_by_action = {action_id: rank for rank, action_id in enumerate(ranked_action_ids, start=1)}
        for action_id, action_policy in forced_action_policies.items():
            result = evaluate_autonomous_governance_surface_q_policy_v1(
                policy=action_policy,
                surface_state=scenario["surface_state"],
                observation=scenario["observation"],
                current_epoch=34,
                proposal_epoch=10,
                last_update_epoch=32,
                expected_policy_hash=action_policy["policy_hash"],
            )
            row = _training_row(
                source="intra_bin_stress",
                scenario_id=str(scenario["id"]),
                action_id=action_id,
                deltas=actions[action_id],
                result=result,
                utility=_scenario_utility(scenario, result),
            )
            raw_score = scores.get(action_id, 0)
            row["policy_score"] = int(raw_score) if isinstance(raw_score, int) else 0
            row["policy_rank"] = rank_by_action.get(action_id, 0)
            row["expected_bin_key"] = scenario["bin_key"]
            row["probe"] = scenario["probe"]
            row["probe_values"] = dict(scenario["probe_values"])
            rows.append(row)
    return rows


def _safety_boundary_action_rows(
    *,
    policy: Mapping[str, Any],
    actions: Mapping[str, Mapping[str, int]],
    forced_action_policies: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Build verifier-labeled rows for each near-boundary safety scenario."""

    frozen = _freeze_policy(policy)
    rows: list[dict[str, Any]] = []
    for scenario in _safety_boundary_scenarios():
        selected = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=int(scenario["current_epoch"]),
            proposal_epoch=int(scenario["proposal_epoch"]),
            last_update_epoch=scenario["last_update_epoch"],
            expected_policy_hash=frozen["policy_hash"],
        )
        scores = selected.get("scores", {})
        scores = scores if isinstance(scores, Mapping) else {}
        ranked_action_ids = _rank_action_ids_by_score(_action_ids(frozen), scores)
        rank_by_action = {action_id: rank for rank, action_id in enumerate(ranked_action_ids, start=1)}
        for action_id, action_policy in forced_action_policies.items():
            result = evaluate_autonomous_governance_surface_q_policy_v1(
                policy=action_policy,
                surface_state=scenario["surface_state"],
                observation=scenario["observation"],
                current_epoch=int(scenario["current_epoch"]),
                proposal_epoch=int(scenario["proposal_epoch"]),
                last_update_epoch=scenario["last_update_epoch"],
                expected_policy_hash=action_policy["policy_hash"],
            )
            expected_error = str(scenario.get("expected_error", ""))
            row = _training_row(
                source="safety_boundary_sweep",
                scenario_id=str(scenario["id"]),
                action_id=action_id,
                deltas=actions[action_id],
                result=result,
                utility=_scenario_utility(scenario, result),
                expected_error=expected_error or None,
            )
            raw_score = scores.get(action_id, 0)
            row["policy_score"] = int(raw_score) if isinstance(raw_score, int) else 0
            row["policy_rank"] = rank_by_action.get(action_id, 0)
            row["probe"] = scenario["probe"]
            row["boundary_status"] = scenario["status"]
            row["anchor_bin_key"] = scenario["anchor_bin_key"]
            row["bin_key"] = scenario["bin_key"]
            rows.append(row)
    return rows


def _safety_interaction_action_rows(
    *,
    policy: Mapping[str, Any],
    actions: Mapping[str, Mapping[str, int]],
    forced_action_policies: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Build verifier-labeled rows for paired near-boundary safety scenarios."""

    frozen = _freeze_policy(policy)
    rows: list[dict[str, Any]] = []
    for scenario in _safety_interaction_scenarios():
        selected = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=int(scenario["current_epoch"]),
            proposal_epoch=int(scenario["proposal_epoch"]),
            last_update_epoch=scenario["last_update_epoch"],
            expected_policy_hash=frozen["policy_hash"],
        )
        scores = selected.get("scores", {})
        scores = scores if isinstance(scores, Mapping) else {}
        ranked_action_ids = _rank_action_ids_by_score(_action_ids(frozen), scores)
        rank_by_action = {action_id: rank for rank, action_id in enumerate(ranked_action_ids, start=1)}
        expected_errors = tuple(str(error) for error in scenario.get("expected_errors", ()))
        for action_id, action_policy in forced_action_policies.items():
            result = evaluate_autonomous_governance_surface_q_policy_v1(
                policy=action_policy,
                surface_state=scenario["surface_state"],
                observation=scenario["observation"],
                current_epoch=int(scenario["current_epoch"]),
                proposal_epoch=int(scenario["proposal_epoch"]),
                last_update_epoch=scenario["last_update_epoch"],
                expected_policy_hash=action_policy["policy_hash"],
            )
            row = _training_row(
                source="safety_interaction_sweep",
                scenario_id=str(scenario["id"]),
                action_id=action_id,
                deltas=actions[action_id],
                result=result,
                utility=_scenario_utility(scenario, result),
                expected_error=expected_errors[0] if expected_errors else None,
            )
            raw_score = scores.get(action_id, 0)
            row["policy_score"] = int(raw_score) if isinstance(raw_score, int) else 0
            row["policy_rank"] = rank_by_action.get(action_id, 0)
            row["probe"] = scenario["probe"]
            row["boundary_status"] = scenario["status"]
            row["interaction_profile"] = scenario["profile"]
            row["control_pair"] = scenario["control_pair"]
            row["anchor_bin_key"] = scenario["anchor_bin_key"]
            row["bin_key"] = scenario["bin_key"]
            row["expected_errors"] = list(expected_errors)
            row["has_expected_errors"] = all(
                error in row.get("errors", []) for error in expected_errors
            )
            rows.append(row)
    return rows


def _surface_boundary_action_rows(
    *,
    policy: Mapping[str, Any],
    actions: Mapping[str, Mapping[str, int]],
    forced_action_policies: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Build verifier-labeled rows for exact governance-surface boundary cases."""

    frozen = _freeze_policy(policy)
    rows: list[dict[str, Any]] = []
    for scenario in _surface_boundary_scenarios():
        selected = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=int(scenario["current_epoch"]),
            proposal_epoch=int(scenario["proposal_epoch"]),
            last_update_epoch=scenario["last_update_epoch"],
            expected_policy_hash=frozen["policy_hash"],
        )
        scores = selected.get("scores", {})
        scores = scores if isinstance(scores, Mapping) else {}
        ranked_action_ids = _rank_action_ids_by_score(_action_ids(frozen), scores)
        rank_by_action = {action_id: rank for rank, action_id in enumerate(ranked_action_ids, start=1)}
        expected_error = str(scenario.get("expected_rejection_error", ""))
        for action_id, action_policy in forced_action_policies.items():
            result = evaluate_autonomous_governance_surface_q_policy_v1(
                policy=action_policy,
                surface_state=scenario["surface_state"],
                observation=scenario["observation"],
                current_epoch=int(scenario["current_epoch"]),
                proposal_epoch=int(scenario["proposal_epoch"]),
                last_update_epoch=scenario["last_update_epoch"],
                expected_policy_hash=action_policy["policy_hash"],
            )
            row = _training_row(
                source="surface_boundary_sweep",
                scenario_id=str(scenario["id"]),
                action_id=action_id,
                deltas=actions[action_id],
                result=result,
                utility=_scenario_utility(scenario, result),
                expected_error=expected_error or None,
            )
            raw_score = scores.get(action_id, 0)
            row["policy_score"] = int(raw_score) if isinstance(raw_score, int) else 0
            row["policy_rank"] = rank_by_action.get(action_id, 0)
            row["probe"] = scenario["probe"]
            row["boundary_family"] = scenario["boundary_family"]
            row["limit_status"] = scenario["limit_status"]
            row["bin_key"] = scenario["bin_key"]
            row["expected_rejection_error"] = expected_error
            rows.append(row)
    return rows


def _normal_grid_ranking_diagnostics(
    *,
    policy: Mapping[str, Any],
    rows: list[dict[str, Any]],
) -> dict[str, Any]:
    """Audit EBRM ranking quality against verifier-labeled normal-grid rows."""

    frozen = _freeze_policy(policy)
    action_ids = _action_ids(frozen)
    rows_by_scenario: dict[str, dict[str, dict[str, Any]]] = {}
    for row in rows:
        if row.get("source") != "normal_grid":
            continue
        scenario_id = str(row.get("scenario_id", ""))
        action_id = str(row.get("action_id", ""))
        rows_by_scenario.setdefault(scenario_id, {})[action_id] = row

    scenario_count = 0
    accepting_scenario_count = 0
    no_accepted_scenario_count = 0
    missing_action_row_count = 0
    calls_to_first_accept_total = 0
    calls_to_best_utility_total = 0
    calls_to_first_accept_max = 0
    calls_to_best_utility_max = 0
    rank1_accepted_count = 0
    rank1_best_utility_count = 0
    best_utility_regret_total = 0
    best_utility_regret_count = 0
    best_utility_regret_max = 0
    hard_negative_count = 0
    hard_negative_scenario_count = 0
    hard_negative_margin_min: int | None = None
    hard_negative_margin_violation_count = 0
    margin_sample_failures: list[dict[str, Any]] = []
    regret_sample_failures: list[dict[str, Any]] = []

    for scenario in _scenarios():
        scenario_id = str(scenario["id"])
        scenario_count += 1
        scenario_rows = rows_by_scenario.get(scenario_id, {})
        missing_actions = tuple(action_id for action_id in action_ids if action_id not in scenario_rows)
        if missing_actions:
            missing_action_row_count += len(missing_actions)
            continue

        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=34,
            proposal_epoch=10,
            last_update_epoch=32,
            expected_policy_hash=frozen["policy_hash"],
        )
        scores = result.get("scores", {})
        scores = scores if isinstance(scores, Mapping) else {}
        ranked_action_ids = _rank_action_ids_by_score(action_ids, scores)
        approved_action_ids = tuple(
            action_id for action_id in action_ids if scenario_rows[action_id].get("approved") is True
        )
        if not approved_action_ids:
            no_accepted_scenario_count += 1
            continue

        accepting_scenario_count += 1
        best_utility = max(int(scenario_rows[action_id].get("utility", 0)) for action_id in approved_action_ids)
        first_accept_rank = 0
        best_utility_rank = 0
        first_accept_action_id = ""
        first_accept_utility = 0
        for rank, action_id in enumerate(ranked_action_ids, start=1):
            row = scenario_rows[action_id]
            if row.get("approved") is True and first_accept_rank == 0:
                first_accept_rank = rank
                first_accept_action_id = action_id
                first_accept_utility = int(row.get("utility", 0))
            if row.get("approved") is True and int(row.get("utility", 0)) == best_utility and best_utility_rank == 0:
                best_utility_rank = rank
        calls_to_first_accept_total += first_accept_rank
        calls_to_best_utility_total += best_utility_rank
        calls_to_first_accept_max = max(calls_to_first_accept_max, first_accept_rank)
        calls_to_best_utility_max = max(calls_to_best_utility_max, best_utility_rank)

        rank1_action_id = ranked_action_ids[0]
        rank1_row = scenario_rows[rank1_action_id]
        if rank1_row.get("approved") is True:
            rank1_accepted_count += 1
        if rank1_row.get("approved") is True and int(rank1_row.get("utility", 0)) == best_utility:
            rank1_best_utility_count += 1

        regret = max(0, best_utility - first_accept_utility)
        if regret > 0:
            best_utility_regret_total += regret
            best_utility_regret_count += 1
            best_utility_regret_max = max(best_utility_regret_max, regret)
            if len(regret_sample_failures) < 12:
                regret_sample_failures.append(
                    {
                        "scenario": scenario_id,
                        "first_accept_action_id": first_accept_action_id,
                        "first_accept_utility": first_accept_utility,
                        "best_utility": best_utility,
                        "regret": regret,
                    }
                )

        rejected_action_ids = tuple(
            action_id for action_id in action_ids if scenario_rows[action_id].get("approved") is not True
        )
        if rejected_action_ids:
            hard_negative_count += len(rejected_action_ids)
            hard_negative_scenario_count += 1
            best_accepted_score = max(int(scores.get(action_id, 0)) for action_id in approved_action_ids)
            max_rejected_score = max(int(scores.get(action_id, 0)) for action_id in rejected_action_ids)
            margin = best_accepted_score - max_rejected_score
            hard_negative_margin_min = (
                margin if hard_negative_margin_min is None else min(hard_negative_margin_min, margin)
            )
            if margin <= 0:
                hard_negative_margin_violation_count += 1
                if len(margin_sample_failures) < 12:
                    margin_sample_failures.append(
                        {
                            "scenario": scenario_id,
                            "best_accepted_score": best_accepted_score,
                            "max_rejected_score": max_rejected_score,
                            "margin": margin,
                            "ranked_action_ids": ranked_action_ids,
                        }
                    )

    mean_calls_to_first_accept = round(
        calls_to_first_accept_total / max(1, accepting_scenario_count), 6
    )
    mean_calls_to_best_utility = round(
        calls_to_best_utility_total / max(1, accepting_scenario_count), 6
    )
    verifier_call_savings_vs_exhaustive = round(
        1.0 - (calls_to_first_accept_total / max(1, accepting_scenario_count * len(action_ids))),
        6,
    )
    hard_negative_margin_min_value = hard_negative_margin_min if hard_negative_margin_min is not None else 0
    checks = {
        "normal_grid_scenarios_complete": scenario_count == len(_scenarios()),
        "ranked_action_rows_complete": missing_action_row_count == 0,
        "accepting_scenarios_present": accepting_scenario_count > 0,
        "first_accept_mean_calls_is_one": mean_calls_to_first_accept == 1.0,
        "first_accept_max_calls_is_one": calls_to_first_accept_max == 1,
        "best_utility_mean_calls_is_one": mean_calls_to_best_utility == 1.0,
        "best_utility_regret_zero": best_utility_regret_total == 0,
        "rank1_best_utility_complete": rank1_best_utility_count == accepting_scenario_count,
        "hard_negative_margin_positive": (
            hard_negative_scenario_count > 0
            and hard_negative_margin_min_value > 0
            and hard_negative_margin_violation_count == 0
        ),
    }
    return {
        "schema": EBR_TRAINING_RANKING_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "scenario_count": scenario_count,
        "action_count": len(action_ids),
        "accepting_scenario_count": accepting_scenario_count,
        "no_accepted_scenario_count": no_accepted_scenario_count,
        "missing_action_row_count": missing_action_row_count,
        "calls_to_first_accept_total": calls_to_first_accept_total,
        "calls_to_first_accept_max": calls_to_first_accept_max,
        "mean_calls_to_first_accept": mean_calls_to_first_accept,
        "calls_to_best_utility_total": calls_to_best_utility_total,
        "calls_to_best_utility_max": calls_to_best_utility_max,
        "mean_calls_to_best_utility": mean_calls_to_best_utility,
        "verifier_call_savings_vs_exhaustive": verifier_call_savings_vs_exhaustive,
        "rank1_accepted_count": rank1_accepted_count,
        "rank1_best_utility_count": rank1_best_utility_count,
        "best_utility_regret_total": best_utility_regret_total,
        "best_utility_regret_count": best_utility_regret_count,
        "best_utility_regret_max": best_utility_regret_max,
        "hard_negative_count": hard_negative_count,
        "hard_negative_scenario_count": hard_negative_scenario_count,
        "hard_negative_margin_min": hard_negative_margin_min_value,
        "hard_negative_margin_violation_count": hard_negative_margin_violation_count,
        "margin_sample_failures": margin_sample_failures,
        "regret_sample_failures": regret_sample_failures,
        "boundary": "Ranking diagnostics audit verifier-call savings and hard-negative margins; gates still decide acceptance.",
    }


def _sequence_ranking_diagnostics(
    *,
    policy: Mapping[str, Any],
    rows: list[dict[str, Any]],
) -> dict[str, Any]:
    """Audit temporal ranking quality against verifier-labeled sequence candidate rows."""

    action_ids = _action_ids(_freeze_policy(policy))
    rows_by_step: dict[str, dict[str, dict[str, Any]]] = {}
    for row in rows:
        if row.get("source") != "sequence_step":
            continue
        scenario_id = str(row.get("scenario_id", ""))
        action_id = str(row.get("action_id", ""))
        rows_by_step.setdefault(scenario_id, {})[action_id] = row

    expected_step_ids = tuple(
        f"{case['id']}:step_{index}"
        for case in _sequence_cases()
        for index, _bins in enumerate(case["bin_path"])
    )
    step_count = len(expected_step_ids)
    missing_action_row_count = 0
    accepting_step_count = 0
    no_accepted_step_count = 0
    selection_blocked_count = 0
    verifier_calls_to_first_accept_total = 0
    verifier_calls_to_first_accept_max = 0
    calls_to_best_utility_total = 0
    calls_to_best_utility_max = 0
    rank1_accepted_count = 0
    rank1_best_utility_count = 0
    first_verifier_best_utility_count = 0
    best_utility_regret_total = 0
    best_utility_regret_count = 0
    best_utility_regret_max = 0
    hard_negative_count = 0
    hard_negative_step_count = 0
    hard_negative_margin_min: int | None = None
    hard_negative_margin_violation_count = 0
    blocked_above_first_accept_count = 0
    margin_sample_failures: list[dict[str, Any]] = []
    regret_sample_failures: list[dict[str, Any]] = []

    for step_id in expected_step_ids:
        step_rows = rows_by_step.get(step_id, {})
        missing_actions = tuple(action_id for action_id in action_ids if action_id not in step_rows)
        if missing_actions:
            missing_action_row_count += len(missing_actions)
            continue
        ranked_action_ids = sorted(
            action_ids,
            key=lambda action_id: int(step_rows[action_id].get("policy_rank", 0) or 0),
        )
        selection_blocked_count += sum(
            1 for action_id in action_ids if step_rows[action_id].get("selection_blocked") is True
        )
        approved_action_ids = tuple(
            action_id for action_id in action_ids if step_rows[action_id].get("approved") is True
        )
        if not approved_action_ids:
            no_accepted_step_count += 1
            continue

        accepting_step_count += 1
        best_utility = max(int(step_rows[action_id].get("utility", 0)) for action_id in approved_action_ids)
        first_accept_action_id = ""
        first_accept_rank = 0
        first_accept_utility = 0
        verifier_calls = 0
        best_utility_calls = 0
        best_utility_seen = False
        blocked_before_first_accept = 0
        for action_id in ranked_action_ids:
            row = step_rows[action_id]
            if row.get("selection_blocked") is True:
                if not first_accept_action_id:
                    blocked_before_first_accept += 1
                continue
            verifier_calls += 1
            if not best_utility_seen:
                best_utility_calls += 1
            if row.get("approved") is True and int(row.get("utility", 0)) == best_utility:
                best_utility_seen = True
            if row.get("approved") is True and not first_accept_action_id:
                first_accept_action_id = action_id
                first_accept_rank = int(row.get("policy_rank", 0) or 0)
                first_accept_utility = int(row.get("utility", 0))
                break
        blocked_above_first_accept_count += blocked_before_first_accept
        verifier_calls_to_first_accept_total += verifier_calls
        verifier_calls_to_first_accept_max = max(verifier_calls_to_first_accept_max, verifier_calls)
        calls_to_best_utility_total += best_utility_calls
        calls_to_best_utility_max = max(calls_to_best_utility_max, best_utility_calls)

        rank1_row = step_rows[ranked_action_ids[0]]
        if rank1_row.get("approved") is True:
            rank1_accepted_count += 1
        if rank1_row.get("approved") is True and int(rank1_row.get("utility", 0)) == best_utility:
            rank1_best_utility_count += 1

        regret = max(0, best_utility - first_accept_utility)
        if first_accept_utility == best_utility:
            first_verifier_best_utility_count += 1
        if regret > 0:
            best_utility_regret_total += regret
            best_utility_regret_count += 1
            best_utility_regret_max = max(best_utility_regret_max, regret)
            if len(regret_sample_failures) < 12:
                regret_sample_failures.append(
                    {
                        "scenario": step_id,
                        "first_accept_action_id": first_accept_action_id,
                        "first_accept_rank": first_accept_rank,
                        "first_accept_utility": first_accept_utility,
                        "best_utility": best_utility,
                        "regret": regret,
                    }
                )

        rejected_action_ids = tuple(
            action_id
            for action_id in action_ids
            if step_rows[action_id].get("approved") is not True
            and step_rows[action_id].get("selection_blocked") is not True
        )
        if rejected_action_ids:
            hard_negative_count += len(rejected_action_ids)
            hard_negative_step_count += 1
            best_accepted_score = max(int(step_rows[action_id].get("policy_score", 0)) for action_id in approved_action_ids)
            max_rejected_score = max(int(step_rows[action_id].get("policy_score", 0)) for action_id in rejected_action_ids)
            margin = best_accepted_score - max_rejected_score
            hard_negative_margin_min = (
                margin if hard_negative_margin_min is None else min(hard_negative_margin_min, margin)
            )
            if margin <= 0:
                hard_negative_margin_violation_count += 1
                if len(margin_sample_failures) < 12:
                    margin_sample_failures.append(
                        {
                            "scenario": step_id,
                            "best_accepted_score": best_accepted_score,
                            "max_rejected_score": max_rejected_score,
                            "margin": margin,
                            "ranked_action_ids": ranked_action_ids,
                        }
                    )

    mean_verifier_calls_to_first_accept = round(
        verifier_calls_to_first_accept_total / max(1, accepting_step_count), 6
    )
    mean_calls_to_best_utility = round(
        calls_to_best_utility_total / max(1, accepting_step_count), 6
    )
    verifier_call_savings_vs_exhaustive = round(
        1.0 - (verifier_calls_to_first_accept_total / max(1, accepting_step_count * len(action_ids))),
        6,
    )
    hard_negative_margin_min_value = hard_negative_margin_min if hard_negative_margin_min is not None else 0
    checks = {
        "sequence_steps_complete": len(rows_by_step) == step_count,
        "ranked_action_rows_complete": missing_action_row_count == 0,
        "accepting_steps_present": accepting_step_count > 0,
        "verifier_calls_mean_is_one": mean_verifier_calls_to_first_accept == 1.0,
        "verifier_calls_max_is_one": verifier_calls_to_first_accept_max == 1,
        "best_utility_mean_calls_is_one": mean_calls_to_best_utility == 1.0,
        "best_utility_regret_zero": best_utility_regret_total == 0,
        "first_verifier_best_utility_complete": first_verifier_best_utility_count == accepting_step_count,
        "selection_blocked_rows_present": selection_blocked_count > 0,
        "nonblocked_hard_negative_margin_positive_or_absent": (
            hard_negative_step_count == 0
            or (hard_negative_margin_min_value > 0 and hard_negative_margin_violation_count == 0)
        ),
    }
    return {
        "schema": "zenodex.autonomous_governance.ebr_sequence_ranking_diagnostics.v1",
        "ok": all(checks.values()),
        "checks": checks,
        "step_count": step_count,
        "action_count": len(action_ids),
        "row_count": sum(len(step_rows) for step_rows in rows_by_step.values()),
        "accepting_step_count": accepting_step_count,
        "no_accepted_step_count": no_accepted_step_count,
        "missing_action_row_count": missing_action_row_count,
        "selection_blocked_count": selection_blocked_count,
        "blocked_above_first_accept_count": blocked_above_first_accept_count,
        "verifier_calls_to_first_accept_total": verifier_calls_to_first_accept_total,
        "verifier_calls_to_first_accept_max": verifier_calls_to_first_accept_max,
        "mean_verifier_calls_to_first_accept": mean_verifier_calls_to_first_accept,
        "calls_to_best_utility_total": calls_to_best_utility_total,
        "calls_to_best_utility_max": calls_to_best_utility_max,
        "mean_calls_to_best_utility": mean_calls_to_best_utility,
        "verifier_call_savings_vs_exhaustive": verifier_call_savings_vs_exhaustive,
        "rank1_accepted_count": rank1_accepted_count,
        "rank1_best_utility_count": rank1_best_utility_count,
        "first_verifier_best_utility_count": first_verifier_best_utility_count,
        "best_utility_regret_total": best_utility_regret_total,
        "best_utility_regret_count": best_utility_regret_count,
        "best_utility_regret_max": best_utility_regret_max,
        "hard_negative_count": hard_negative_count,
        "hard_negative_step_count": hard_negative_step_count,
        "hard_negative_margin_min": hard_negative_margin_min_value,
        "hard_negative_margin_violation_count": hard_negative_margin_violation_count,
        "margin_sample_failures": margin_sample_failures,
        "regret_sample_failures": regret_sample_failures,
        "boundary": "Sequence ranking diagnostics audit temporal verifier-call savings and hard-negative margins; gates still decide acceptance.",
    }


def _training_pairwise_diagnostics(
    *,
    policy: Mapping[str, Any],
    rows: list[dict[str, Any]],
) -> dict[str, Any]:
    """Audit pairwise/listwise ranking constraints over candidate-complete rows."""

    action_ids = _action_ids(_freeze_policy(policy))
    rows_by_group: dict[str, dict[str, dict[str, Any]]] = {}
    for row in rows:
        source = str(row.get("source", ""))
        if source not in CANDIDATE_TRAINING_SOURCES:
            continue
        scenario_id = str(row.get("scenario_id", ""))
        action_id = str(row.get("action_id", ""))
        rows_by_group.setdefault(f"{source}:{scenario_id}", {})[action_id] = row

    expected_group_ids = tuple(
        [f"normal_grid:{scenario['id']}" for scenario in _scenarios()]
        + [f"intra_bin_stress:{scenario['id']}" for scenario in _intra_bin_stress_scenarios()]
        + [
            f"sequence_step:{case['id']}:step_{index}"
            for case in _sequence_cases()
            for index, _bins in enumerate(case["bin_path"])
        ]
        + [f"safety_boundary_sweep:{scenario['id']}" for scenario in _safety_boundary_scenarios()]
        + [f"safety_interaction_sweep:{scenario['id']}" for scenario in _safety_interaction_scenarios()]
        + [f"surface_boundary_sweep:{scenario['id']}" for scenario in _surface_boundary_scenarios()]
    )
    source_group_counts: Counter[str] = Counter()
    accepting_source_counts: Counter[str] = Counter()
    no_accepted_source_counts: Counter[str] = Counter()
    negative_family_histogram: Counter[str] = Counter()
    missing_action_row_count = 0
    accepting_group_count = 0
    no_accepted_group_count = 0
    gate_rejected_pair_count = 0
    gate_rejected_margin_min: int | None = None
    gate_rejected_margin_violation_count = 0
    utility_dominated_pair_count = 0
    utility_dominated_margin_min: int | None = None
    utility_dominated_margin_tie_count = 0
    utility_dominated_margin_violation_count = 0
    utility_dominated_rank_violation_count = 0
    selection_blocked_pair_count = 0
    selection_blocked_above_best_accept_count = 0
    gate_margin_sample_failures: list[dict[str, Any]] = []
    utility_margin_sample_failures: list[dict[str, Any]] = []

    def row_score(row: Mapping[str, Any]) -> int:
        value = row.get("policy_score", 0)
        return int(value) if isinstance(value, int) else 0

    def row_rank(row: Mapping[str, Any]) -> int:
        value = row.get("policy_rank", 0)
        return int(value) if isinstance(value, int) else 0

    for group_id in expected_group_ids:
        source = group_id.split(":", 1)[0]
        source_group_counts[source] += 1
        group_rows = rows_by_group.get(group_id, {})
        missing_actions = tuple(action_id for action_id in action_ids if action_id not in group_rows)
        if missing_actions:
            missing_action_row_count += len(missing_actions)
            continue

        accepted_rows = tuple(
            group_rows[action_id]
            for action_id in action_ids
            if group_rows[action_id].get("approved") is True
        )
        gate_rejected_rows = tuple(
            group_rows[action_id]
            for action_id in action_ids
            if group_rows[action_id].get("approved") is not True
            and group_rows[action_id].get("selection_blocked") is not True
        )
        selection_blocked_rows = tuple(
            group_rows[action_id]
            for action_id in action_ids
            if group_rows[action_id].get("selection_blocked") is True
        )
        for row in gate_rejected_rows + selection_blocked_rows:
            family = str(row.get("failure_family", ""))
            if family:
                negative_family_histogram[family] += 1

        if not accepted_rows:
            no_accepted_group_count += 1
            no_accepted_source_counts[source] += 1
            continue

        accepting_group_count += 1
        accepting_source_counts[source] += 1

        best_utility = max(int(row.get("utility", 0)) for row in accepted_rows)
        best_rows = tuple(row for row in accepted_rows if int(row.get("utility", 0)) == best_utility)
        dominated_rows = tuple(row for row in accepted_rows if int(row.get("utility", 0)) < best_utility)
        best_score = max(row_score(row) for row in best_rows)
        best_rank = min(row_rank(row) for row in best_rows)
        best_score_rows = tuple(row for row in best_rows if row_score(row) == best_score)

        for accepted in best_score_rows:
            accepted_score = row_score(accepted)
            for rejected in gate_rejected_rows:
                gate_rejected_pair_count += 1
                margin = accepted_score - row_score(rejected)
                gate_rejected_margin_min = (
                    margin if gate_rejected_margin_min is None else min(gate_rejected_margin_min, margin)
                )
                if margin <= 0:
                    gate_rejected_margin_violation_count += 1
                    if len(gate_margin_sample_failures) < 12:
                        gate_margin_sample_failures.append(
                            {
                                "group": group_id,
                                "accepted_action_id": accepted.get("action_id", ""),
                                "rejected_action_id": rejected.get("action_id", ""),
                                "accepted_score": accepted_score,
                                "rejected_score": row_score(rejected),
                                "margin": margin,
                                "rejected_failure_family": rejected.get("failure_family", ""),
                            }
                        )

        for dominated in dominated_rows:
            utility_dominated_pair_count += 1
            margin = best_score - row_score(dominated)
            utility_dominated_margin_min = (
                margin
                if utility_dominated_margin_min is None
                else min(utility_dominated_margin_min, margin)
            )
            if margin == 0:
                utility_dominated_margin_tie_count += 1
            if margin < 0:
                utility_dominated_margin_violation_count += 1
            if row_rank(dominated) < best_rank:
                utility_dominated_rank_violation_count += 1
            if (margin < 0 or row_rank(dominated) < best_rank) and len(utility_margin_sample_failures) < 12:
                utility_margin_sample_failures.append(
                    {
                        "group": group_id,
                        "best_utility": best_utility,
                        "best_score": best_score,
                        "best_rank": best_rank,
                        "dominated_action_id": dominated.get("action_id", ""),
                        "dominated_utility": dominated.get("utility", 0),
                        "dominated_score": row_score(dominated),
                        "dominated_rank": row_rank(dominated),
                        "margin": margin,
                    }
                )

        selection_blocked_pair_count += len(accepted_rows) * len(selection_blocked_rows)
        if selection_blocked_rows:
            best_accept_rank = min(row_rank(row) for row in best_rows)
            selection_blocked_above_best_accept_count += sum(
                1 for row in selection_blocked_rows if row_rank(row) < best_accept_rank
            )

    gate_rejected_margin_min_value = gate_rejected_margin_min if gate_rejected_margin_min is not None else 0
    utility_dominated_margin_min_value = (
        utility_dominated_margin_min if utility_dominated_margin_min is not None else 0
    )
    checks = {
        "candidate_groups_complete": len(rows_by_group) == len(expected_group_ids),
        "candidate_action_rows_complete": missing_action_row_count == 0,
        "accepting_groups_present": accepting_group_count > 0,
        "no_accepted_groups_present": no_accepted_group_count > 0,
        "gate_rejected_pairs_present": gate_rejected_pair_count > 0,
        "gate_rejected_margin_positive": (
            gate_rejected_pair_count > 0
            and gate_rejected_margin_min_value > 0
            and gate_rejected_margin_violation_count == 0
        ),
        "utility_dominated_pairs_present": utility_dominated_pair_count > 0,
        "utility_dominated_best_score_not_lower": utility_dominated_margin_violation_count == 0,
        "utility_dominated_best_rank_not_lower": utility_dominated_rank_violation_count == 0,
        "selection_blocked_pairs_present": selection_blocked_pair_count > 0,
        "negative_failure_families_present": len(negative_family_histogram) >= 4,
    }
    return {
        "schema": EBR_TRAINING_PAIRWISE_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "group_count": len(rows_by_group),
        "expected_group_count": len(expected_group_ids),
        "action_count": len(action_ids),
        "missing_action_row_count": missing_action_row_count,
        "accepting_group_count": accepting_group_count,
        "no_accepted_group_count": no_accepted_group_count,
        "source_group_counts": _counter_to_dict(source_group_counts),
        "accepting_source_counts": _counter_to_dict(accepting_source_counts),
        "no_accepted_source_counts": _counter_to_dict(no_accepted_source_counts),
        "gate_rejected_pair_count": gate_rejected_pair_count,
        "gate_rejected_margin_min": gate_rejected_margin_min_value,
        "gate_rejected_margin_violation_count": gate_rejected_margin_violation_count,
        "utility_dominated_pair_count": utility_dominated_pair_count,
        "utility_dominated_margin_min": utility_dominated_margin_min_value,
        "utility_dominated_margin_tie_count": utility_dominated_margin_tie_count,
        "utility_dominated_margin_violation_count": utility_dominated_margin_violation_count,
        "utility_dominated_rank_violation_count": utility_dominated_rank_violation_count,
        "selection_blocked_pair_count": selection_blocked_pair_count,
        "selection_blocked_above_best_accept_count": selection_blocked_above_best_accept_count,
        "negative_failure_family_count": len(negative_family_histogram),
        "negative_failure_family_histogram": _counter_to_dict(negative_family_histogram),
        "gate_margin_sample_failures": gate_margin_sample_failures,
        "utility_margin_sample_failures": utility_margin_sample_failures,
        "boundary": "Pairwise diagnostics audit training-order constraints only; deterministic governance gates still decide acceptance.",
    }


def _build_training_corpus(policy: Mapping[str, Any]) -> dict[str, Any]:
    frozen = _freeze_policy(policy)
    actions = _action_map(frozen)
    rows: list[dict[str, Any]] = []
    label_histogram: Counter[str] = Counter()
    source_histogram: Counter[str] = Counter()
    action_histogram: Counter[str] = Counter()
    error_histogram: Counter[str] = Counter()
    failure_family_histogram: Counter[str] = Counter()
    invalid_accept_count = 0

    forced_action_policies = {
        action_id: _forced_existing_action_policy(frozen, action_id=action_id)
        for action_id in sorted(actions)
    }
    for scenario in _scenarios():
        selected = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=scenario["surface_state"],
            observation=scenario["observation"],
            current_epoch=34,
            proposal_epoch=10,
            last_update_epoch=32,
            expected_policy_hash=frozen["policy_hash"],
        )
        scores = selected.get("scores", {})
        scores = scores if isinstance(scores, Mapping) else {}
        ranked_action_ids = _rank_action_ids_by_score(_action_ids(frozen), scores)
        rank_by_action = {action_id: rank for rank, action_id in enumerate(ranked_action_ids, start=1)}
        for action_id, action_policy in forced_action_policies.items():
            result = evaluate_autonomous_governance_surface_q_policy_v1(
                policy=action_policy,
                surface_state=scenario["surface_state"],
                observation=scenario["observation"],
                current_epoch=34,
                proposal_epoch=10,
                last_update_epoch=32,
                expected_policy_hash=action_policy["policy_hash"],
            )
            row = _training_row(
                source="normal_grid",
                scenario_id=str(scenario["id"]),
                action_id=action_id,
                deltas=actions[action_id],
                result=result,
                utility=_scenario_utility(scenario, result),
            )
            raw_score = scores.get(action_id, 0)
            row["policy_score"] = int(raw_score) if isinstance(raw_score, int) else 0
            row["policy_rank"] = rank_by_action.get(action_id, 0)
            rows.append(row)

    base_observation = _observation_for_bins(3, 2, 2)
    base_state = _base_surface_state()
    for control in _negative_controls(frozen):
        control_policy = control["policy"]
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=control_policy,
            surface_state=base_state,
            observation=base_observation,
            current_epoch=34,
            proposal_epoch=10,
            last_update_epoch=32,
            expected_policy_hash=control_policy["policy_hash"],
        )
        rows.append(
            _training_row(
                source="negative_control",
                scenario_id=str(control["id"]),
                action_id=str(result.get("action_id", "")),
                deltas=dict(control_policy["actions"][-1].get("deltas", {})),
                result=result,
                utility=0,
                expected_error=str(control["expected_error"]),
            )
        )

    for lane in _safety_lanes():
        expected_hash = (
            frozen["policy_hash"]
            if lane["expected_policy_hash"] == "policy"
            else str(lane["expected_policy_hash"])
        )
        result = evaluate_autonomous_governance_surface_q_policy_v1(
            policy=frozen,
            surface_state=lane["surface_state"],
            observation=lane["observation"],
            current_epoch=int(lane["current_epoch"]),
            proposal_epoch=int(lane["proposal_epoch"]),
            last_update_epoch=lane["last_update_epoch"],
            expected_policy_hash=expected_hash,
        )
        action_id = str(result.get("action_id", ""))
        rows.append(
            _training_row(
                source="safety_lane",
                scenario_id=str(lane["id"]),
                action_id=action_id,
                deltas=actions.get(action_id, {}),
                result=result,
                utility=0,
                expected_error=str(lane["expected_error"]),
            )
        )

    rows.extend(
        _intra_bin_stress_action_rows(
            policy=frozen,
            actions=actions,
            forced_action_policies=forced_action_policies,
        )
    )

    rows.extend(
        _safety_boundary_action_rows(
            policy=frozen,
            actions=actions,
            forced_action_policies=forced_action_policies,
        )
    )

    rows.extend(
        _safety_interaction_action_rows(
            policy=frozen,
            actions=actions,
            forced_action_policies=forced_action_policies,
        )
    )

    rows.extend(
        _surface_boundary_action_rows(
            policy=frozen,
            actions=actions,
            forced_action_policies=forced_action_policies,
        )
    )

    rows.extend(
        _sequence_action_rows(
            policy=frozen,
            actions=actions,
            forced_action_policies=forced_action_policies,
        )
    )

    supervision_targets = _annotate_supervision_targets(rows)
    split_diagnostics = _annotate_train_validation_splits(rows)
    feature_contract = _annotate_feature_vectors(rows)
    diversity_diagnostics = _training_diversity_diagnostics(
        rows=rows,
        action_ids=tuple(sorted(actions)),
    )

    for row in rows:
        label_histogram[str(row["label"])] += 1
        source_histogram[str(row["source"])] += 1
        action_histogram[str(row["action_id"])] += 1
        failure_family = str(row.get("failure_family", ""))
        if failure_family:
            failure_family_histogram[failure_family] += 1
        for error in row.get("errors", []):
            error_histogram[str(error)] += 1
        if row["approved"] is True and row["all_gates_ok"] is not True:
            invalid_accept_count += 1

    missing_required_errors = tuple(error for error in REQUIRED_REJECTION_ERRORS if int(error_histogram.get(error, 0)) == 0)
    missing_action_ids = tuple(action_id for action_id in sorted(actions) if int(action_histogram.get(action_id, 0)) == 0)
    expected_normal_rows = len(_scenarios()) * len(actions)
    expected_intra_bin_rows = len(_intra_bin_stress_scenarios()) * len(actions)
    expected_safety_boundary_rows = len(_safety_boundary_scenarios()) * len(actions)
    expected_safety_interaction_rows = len(_safety_interaction_scenarios()) * len(actions)
    expected_surface_boundary_rows = len(_surface_boundary_scenarios()) * len(actions)
    expected_sequence_steps = sum(len(case["bin_path"]) for case in _sequence_cases())
    expected_sequence_rows = expected_sequence_steps * len(actions)
    sequence_selection_blocked_count = sum(
        1 for row in rows if row.get("source") == "sequence_step" and row.get("selection_blocked") is True
    )
    ranking_diagnostics = _normal_grid_ranking_diagnostics(policy=frozen, rows=rows)
    sequence_ranking_diagnostics = _sequence_ranking_diagnostics(policy=frozen, rows=rows)
    pairwise_diagnostics = _training_pairwise_diagnostics(policy=frozen, rows=rows)
    entropy_diagnostics = _training_entropy_diagnostics(rows)
    checks = {
        "normal_grid_row_count_matches": source_histogram.get("normal_grid", 0) == expected_normal_rows,
        "intra_bin_stress_row_count_matches": (
            source_histogram.get("intra_bin_stress", 0) == expected_intra_bin_rows
        ),
        "safety_boundary_sweep_row_count_matches": (
            source_histogram.get("safety_boundary_sweep", 0) == expected_safety_boundary_rows
        ),
        "safety_interaction_sweep_row_count_matches": (
            source_histogram.get("safety_interaction_sweep", 0) == expected_safety_interaction_rows
        ),
        "surface_boundary_sweep_row_count_matches": (
            source_histogram.get("surface_boundary_sweep", 0) == expected_surface_boundary_rows
        ),
        "negative_control_rows_present": source_histogram.get("negative_control", 0) == len(REQUIRED_NEGATIVE_CONTROLS),
        "safety_lane_rows_present": source_histogram.get("safety_lane", 0) == len(REQUIRED_SAFETY_LANES),
        "sequence_step_rows_present": source_histogram.get("sequence_step", 0) == expected_sequence_rows,
        "accepted_and_rejected_labels_present": label_histogram.get("accepted", 0) > 0 and label_histogram.get("rejected", 0) > 0,
        "all_policy_actions_covered": not missing_action_ids,
        "invalid_accept_count_zero": invalid_accept_count == 0,
        "required_rejection_errors_observed": not missing_required_errors,
        "ranking_diagnostics_ok": ranking_diagnostics["ok"] is True,
        "sequence_ranking_diagnostics_ok": sequence_ranking_diagnostics["ok"] is True,
        "pairwise_diagnostics_ok": pairwise_diagnostics["ok"] is True,
        "supervision_targets_ok": supervision_targets["ok"] is True,
        "split_diagnostics_ok": split_diagnostics["ok"] is True,
        "feature_contract_ok": feature_contract["ok"] is True,
        "entropy_diagnostics_ok": entropy_diagnostics["ok"] is True,
        "diversity_diagnostics_ok": diversity_diagnostics["ok"] is True,
    }
    summary = {
        "ok": all(checks.values()),
        "checks": checks,
        "row_count": len(rows),
        "expected_normal_grid_row_count": expected_normal_rows,
        "expected_intra_bin_stress_row_count": expected_intra_bin_rows,
        "expected_intra_bin_stress_scenario_count": len(_intra_bin_stress_scenarios()),
        "expected_safety_boundary_sweep_row_count": expected_safety_boundary_rows,
        "expected_safety_boundary_sweep_scenario_count": len(_safety_boundary_scenarios()),
        "expected_safety_interaction_sweep_row_count": expected_safety_interaction_rows,
        "expected_safety_interaction_sweep_scenario_count": len(_safety_interaction_scenarios()),
        "expected_surface_boundary_sweep_row_count": expected_surface_boundary_rows,
        "expected_surface_boundary_sweep_scenario_count": len(_surface_boundary_scenarios()),
        "expected_sequence_step_row_count": expected_sequence_rows,
        "expected_sequence_step_count": expected_sequence_steps,
        "sequence_actions_per_step": len(actions),
        "sequence_selection_blocked_count": sequence_selection_blocked_count,
        "policy_action_count": len(actions),
        "invalid_accept_count": invalid_accept_count,
        "label_histogram": _counter_to_dict(label_histogram),
        "source_histogram": _counter_to_dict(source_histogram),
        "action_histogram": _counter_to_dict(action_histogram),
        "failure_family_histogram": _counter_to_dict(failure_family_histogram),
        "missing_action_ids": missing_action_ids,
        "missing_required_errors": missing_required_errors,
        "ranking_diagnostics": ranking_diagnostics,
        "sequence_ranking_diagnostics": sequence_ranking_diagnostics,
        "pairwise_diagnostics": pairwise_diagnostics,
        "supervision_targets": supervision_targets,
        "split_diagnostics": split_diagnostics,
        "feature_contract": feature_contract,
        "diversity_diagnostics": diversity_diagnostics,
        "entropy_diagnostics": entropy_diagnostics,
    }
    return {
        "schema": EBR_TRAINING_CORPUS_SCHEMA,
        "policy_id": str(frozen.get("policy_id", "")),
        "policy_hash": frozen["policy_hash"],
        "summary": summary,
        "rows": rows,
        "non_claims": [
            "training_rows_do_not_authorize_governance",
            "training_rows_do_not_replace_replay_or_tau_gates",
            "labels_are_bounded_to_factory_scenarios",
        ],
    }


def _merge_error_histograms(*reports: Mapping[str, Any]) -> Counter[str]:
    merged: Counter[str] = Counter()
    for report in reports:
        histogram = report.get("error_histogram", {})
        if not isinstance(histogram, Mapping):
            continue
        for key, value in histogram.items():
            if isinstance(value, int):
                merged[str(key)] += value
    return merged


def _coverage_profile(replay: Mapping[str, Any]) -> dict[str, Any]:
    optimized = replay.get("optimized", {}) if isinstance(replay.get("optimized"), Mapping) else {}
    safety_lanes = replay.get("safety_lanes", {}) if isinstance(replay.get("safety_lanes"), Mapping) else {}
    safety_boundary_sweep = (
        replay.get("safety_boundary_sweep", {})
        if isinstance(replay.get("safety_boundary_sweep"), Mapping)
        else {}
    )
    safety_interaction_sweep = (
        replay.get("safety_interaction_sweep", {})
        if isinstance(replay.get("safety_interaction_sweep"), Mapping)
        else {}
    )
    surface_boundary_sweep = (
        replay.get("surface_boundary_sweep", {})
        if isinstance(replay.get("surface_boundary_sweep"), Mapping)
        else {}
    )
    negative_controls = replay.get("negative_controls", {}) if isinstance(replay.get("negative_controls"), Mapping) else {}
    long_horizon = replay.get("long_horizon", {}) if isinstance(replay.get("long_horizon"), Mapping) else {}
    intra_bin_stress = (
        replay.get("intra_bin_stress", {})
        if isinstance(replay.get("intra_bin_stress"), Mapping)
        else {}
    )

    bin_histogram = optimized.get("bin_histogram", {})
    if not isinstance(bin_histogram, Mapping):
        bin_histogram = {}
    surface_variant_histogram = optimized.get("surface_variant_histogram", {})
    if not isinstance(surface_variant_histogram, Mapping):
        surface_variant_histogram = {}

    observed_safety_lanes = tuple(
        sorted(str(lane.get("id", "")) for lane in safety_lanes.get("lanes", []) if isinstance(lane, Mapping))
    )
    observed_negative_controls = tuple(
        sorted(str(control.get("id", "")) for control in negative_controls.get("controls", []) if isinstance(control, Mapping))
    )
    observed_sequence_ids = tuple(
        sorted(str(sequence.get("id", "")) for sequence in long_horizon.get("sequences", []) if isinstance(sequence, Mapping))
    )
    merged_errors = _merge_error_histograms(
        optimized,
        safety_lanes,
        safety_boundary_sweep,
        safety_interaction_sweep,
        surface_boundary_sweep,
        negative_controls,
        long_horizon,
        intra_bin_stress,
    )
    observed_errors = tuple(sorted(merged_errors))

    missing_surface_variants = tuple(
        variant for variant in REQUIRED_SURFACE_VARIANTS if int(surface_variant_histogram.get(variant, 0)) == 0
    )
    uneven_surface_variants = tuple(
        variant for variant in REQUIRED_SURFACE_VARIANTS if int(surface_variant_histogram.get(variant, 0)) != 48
    )
    missing_bins = tuple(f"{d}|{v}|{l}" for d in range(4) for v in range(4) for l in range(3) if int(bin_histogram.get(f"{d}|{v}|{l}", 0)) == 0)
    uneven_bins = tuple(
        f"{d}|{v}|{l}"
        for d in range(4)
        for v in range(4)
        for l in range(3)
        if int(bin_histogram.get(f"{d}|{v}|{l}", 0)) != len(REQUIRED_SURFACE_VARIANTS)
    )
    missing_safety_lanes = tuple(lane for lane in REQUIRED_SAFETY_LANES if lane not in observed_safety_lanes)
    missing_negative_controls = tuple(control for control in REQUIRED_NEGATIVE_CONTROLS if control not in observed_negative_controls)
    missing_sequence_ids = tuple(sequence for sequence in REQUIRED_SEQUENCE_CASES if sequence not in observed_sequence_ids)
    missing_rejection_errors = tuple(error for error in REQUIRED_REJECTION_ERRORS if int(merged_errors.get(error, 0)) == 0)
    safety_boundary_probe_histogram = safety_boundary_sweep.get("probe_histogram", {})
    if not isinstance(safety_boundary_probe_histogram, Mapping):
        safety_boundary_probe_histogram = {}
    safety_boundary_anchor_histogram = safety_boundary_sweep.get("anchor_bin_histogram", {})
    if not isinstance(safety_boundary_anchor_histogram, Mapping):
        safety_boundary_anchor_histogram = {}
    missing_safety_boundary_probes = tuple(
        probe
        for probe in REQUIRED_SAFETY_BOUNDARY_PROBES
        if int(safety_boundary_probe_histogram.get(probe, 0)) == 0
    )
    uneven_safety_boundary_probes = tuple(
        probe
        for probe in REQUIRED_SAFETY_BOUNDARY_PROBES
        if int(safety_boundary_probe_histogram.get(probe, 0)) != len(SAFETY_BOUNDARY_BIN_ANCHORS)
    )
    missing_safety_boundary_anchors = tuple(
        f"{deviation}|{volatility}|{liquidity}"
        for deviation, volatility, liquidity in SAFETY_BOUNDARY_BIN_ANCHORS
        if int(safety_boundary_anchor_histogram.get(f"{deviation}|{volatility}|{liquidity}", 0)) == 0
    )
    uneven_safety_boundary_anchors = tuple(
        f"{deviation}|{volatility}|{liquidity}"
        for deviation, volatility, liquidity in SAFETY_BOUNDARY_BIN_ANCHORS
        if int(safety_boundary_anchor_histogram.get(f"{deviation}|{volatility}|{liquidity}", 0))
        != len(REQUIRED_SAFETY_BOUNDARY_PROBES)
    )
    safety_interaction_profile_histogram = safety_interaction_sweep.get("profile_histogram", {})
    if not isinstance(safety_interaction_profile_histogram, Mapping):
        safety_interaction_profile_histogram = {}
    safety_interaction_pair_histogram = safety_interaction_sweep.get("control_pair_histogram", {})
    if not isinstance(safety_interaction_pair_histogram, Mapping):
        safety_interaction_pair_histogram = {}
    safety_interaction_anchor_histogram = safety_interaction_sweep.get("anchor_bin_histogram", {})
    if not isinstance(safety_interaction_anchor_histogram, Mapping):
        safety_interaction_anchor_histogram = {}
    surface_boundary_profile_histogram = surface_boundary_sweep.get("profile_histogram", {})
    if not isinstance(surface_boundary_profile_histogram, Mapping):
        surface_boundary_profile_histogram = {}
    expected_interaction_pairs = tuple(
        f"{first}+{second}"
        for index, first in enumerate(SAFETY_INTERACTION_CONTROLS)
        for second in SAFETY_INTERACTION_CONTROLS[index + 1 :]
    )
    missing_safety_interaction_profiles = tuple(
        profile
        for profile in SAFETY_INTERACTION_PROFILES
        if int(safety_interaction_profile_histogram.get(profile, 0)) == 0
    )
    uneven_safety_interaction_profiles = tuple(
        profile
        for profile in SAFETY_INTERACTION_PROFILES
        if int(safety_interaction_profile_histogram.get(profile, 0))
        != len(SAFETY_INTERACTION_BIN_ANCHORS) * len(expected_interaction_pairs)
    )
    missing_safety_interaction_pairs = tuple(
        pair for pair in expected_interaction_pairs if int(safety_interaction_pair_histogram.get(pair, 0)) == 0
    )
    uneven_safety_interaction_pairs = tuple(
        pair
        for pair in expected_interaction_pairs
        if int(safety_interaction_pair_histogram.get(pair, 0))
        != len(SAFETY_INTERACTION_BIN_ANCHORS) * len(SAFETY_INTERACTION_PROFILES)
    )
    missing_safety_interaction_anchors = tuple(
        f"{deviation}|{volatility}|{liquidity}"
        for deviation, volatility, liquidity in SAFETY_INTERACTION_BIN_ANCHORS
        if int(safety_interaction_anchor_histogram.get(f"{deviation}|{volatility}|{liquidity}", 0)) == 0
    )
    uneven_safety_interaction_anchors = tuple(
        f"{deviation}|{volatility}|{liquidity}"
        for deviation, volatility, liquidity in SAFETY_INTERACTION_BIN_ANCHORS
        if int(safety_interaction_anchor_histogram.get(f"{deviation}|{volatility}|{liquidity}", 0))
        != len(expected_interaction_pairs) * len(SAFETY_INTERACTION_PROFILES)
    )
    missing_surface_boundary_profiles = tuple(
        profile
        for profile in REQUIRED_SURFACE_BOUNDARY_PROFILES
        if int(surface_boundary_profile_histogram.get(profile, 0)) == 0
    )
    uneven_surface_boundary_profiles = tuple(
        profile
        for profile in REQUIRED_SURFACE_BOUNDARY_PROFILES
        if int(surface_boundary_profile_histogram.get(profile, 0)) != 1
    )
    intra_bin_histogram = intra_bin_stress.get("bin_histogram", {})
    if not isinstance(intra_bin_histogram, Mapping):
        intra_bin_histogram = {}
    intra_probe_histogram = intra_bin_stress.get("probe_histogram", {})
    if not isinstance(intra_probe_histogram, Mapping):
        intra_probe_histogram = {}
    expected_intra_count_per_bin = len(REQUIRED_INTRABIN_PROBES) * len(REQUIRED_SURFACE_VARIANTS)
    missing_intra_bins = tuple(
        f"{d}|{v}|{l}"
        for d in range(4)
        for v in range(4)
        for l in range(3)
        if int(intra_bin_histogram.get(f"{d}|{v}|{l}", 0)) == 0
    )
    uneven_intra_bins = tuple(
        f"{d}|{v}|{l}"
        for d in range(4)
        for v in range(4)
        for l in range(3)
        if int(intra_bin_histogram.get(f"{d}|{v}|{l}", 0)) != expected_intra_count_per_bin
    )
    missing_intra_probes = tuple(
        probe for probe in REQUIRED_INTRABIN_PROBES if int(intra_probe_histogram.get(probe, 0)) == 0
    )

    checks = {
        "normal_grid_all_bins_present": not missing_bins,
        "normal_grid_bin_counts_uniform": not uneven_bins,
        "surface_variants_present": not missing_surface_variants,
        "surface_variant_counts_uniform": not uneven_surface_variants,
        "safety_lane_ids_complete": not missing_safety_lanes,
        "safety_boundary_sweep_ok": safety_boundary_sweep.get("ok") is True,
        "safety_boundary_probe_profiles_present": not missing_safety_boundary_probes,
        "safety_boundary_probe_counts_uniform": not uneven_safety_boundary_probes,
        "safety_boundary_anchor_bins_present": not missing_safety_boundary_anchors,
        "safety_boundary_anchor_counts_uniform": not uneven_safety_boundary_anchors,
        "safety_interaction_sweep_ok": safety_interaction_sweep.get("ok") is True,
        "safety_interaction_profiles_present": not missing_safety_interaction_profiles,
        "safety_interaction_profile_counts_uniform": not uneven_safety_interaction_profiles,
        "safety_interaction_control_pairs_present": not missing_safety_interaction_pairs,
        "safety_interaction_control_pair_counts_uniform": not uneven_safety_interaction_pairs,
        "safety_interaction_anchor_bins_present": not missing_safety_interaction_anchors,
        "safety_interaction_anchor_counts_uniform": not uneven_safety_interaction_anchors,
        "surface_boundary_sweep_ok": surface_boundary_sweep.get("ok") is True,
        "surface_boundary_profiles_present": not missing_surface_boundary_profiles,
        "surface_boundary_profile_counts_uniform": not uneven_surface_boundary_profiles,
        "negative_control_ids_complete": not missing_negative_controls,
        "long_horizon_ids_complete": not missing_sequence_ids,
        "long_horizon_nonempty": int(long_horizon.get("step_count", 0)) > 0,
        "intra_bin_stress_ok": intra_bin_stress.get("ok") is True,
        "intra_bin_all_bins_present": not missing_intra_bins,
        "intra_bin_counts_uniform": not uneven_intra_bins,
        "intra_bin_probe_profiles_present": not missing_intra_probes,
        "required_rejection_errors_observed": not missing_rejection_errors,
    }
    return {
        "schema": FACTORY_COVERAGE_SCHEMA,
        "ok": all(checks.values()),
        "checks": checks,
        "normal_grid": {
            "required_bin_count": 48,
            "observed_bin_count": len(bin_histogram),
            "missing_bins": missing_bins,
            "uneven_bins": uneven_bins,
            "required_surface_variants": REQUIRED_SURFACE_VARIANTS,
            "surface_variant_histogram": dict(sorted(surface_variant_histogram.items())),
            "missing_surface_variants": missing_surface_variants,
            "uneven_surface_variants": uneven_surface_variants,
        },
        "safety_lanes": {
            "required_ids": REQUIRED_SAFETY_LANES,
            "observed_ids": observed_safety_lanes,
            "missing_ids": missing_safety_lanes,
        },
        "safety_boundary_sweep": {
            "schema": SAFETY_BOUNDARY_SWEEP_SCHEMA,
            "required_probe_profiles": REQUIRED_SAFETY_BOUNDARY_PROBES,
            "probe_histogram": dict(sorted(safety_boundary_probe_histogram.items())),
            "required_anchor_bins": tuple(
                f"{deviation}|{volatility}|{liquidity}"
                for deviation, volatility, liquidity in SAFETY_BOUNDARY_BIN_ANCHORS
            ),
            "anchor_bin_histogram": dict(sorted(safety_boundary_anchor_histogram.items())),
            "missing_probe_profiles": missing_safety_boundary_probes,
            "uneven_probe_profiles": uneven_safety_boundary_probes,
            "missing_anchor_bins": missing_safety_boundary_anchors,
            "uneven_anchor_bins": uneven_safety_boundary_anchors,
        },
        "safety_interaction_sweep": {
            "schema": SAFETY_INTERACTION_SWEEP_SCHEMA,
            "required_profiles": SAFETY_INTERACTION_PROFILES,
            "profile_histogram": dict(sorted(safety_interaction_profile_histogram.items())),
            "required_control_pairs": expected_interaction_pairs,
            "control_pair_histogram": dict(sorted(safety_interaction_pair_histogram.items())),
            "required_anchor_bins": tuple(
                f"{deviation}|{volatility}|{liquidity}"
                for deviation, volatility, liquidity in SAFETY_INTERACTION_BIN_ANCHORS
            ),
            "anchor_bin_histogram": dict(sorted(safety_interaction_anchor_histogram.items())),
            "missing_profiles": missing_safety_interaction_profiles,
            "uneven_profiles": uneven_safety_interaction_profiles,
            "missing_control_pairs": missing_safety_interaction_pairs,
            "uneven_control_pairs": uneven_safety_interaction_pairs,
            "missing_anchor_bins": missing_safety_interaction_anchors,
            "uneven_anchor_bins": uneven_safety_interaction_anchors,
        },
        "surface_boundary_sweep": {
            "schema": SURFACE_BOUNDARY_SWEEP_SCHEMA,
            "required_profiles": REQUIRED_SURFACE_BOUNDARY_PROFILES,
            "profile_histogram": dict(sorted(surface_boundary_profile_histogram.items())),
            "missing_profiles": missing_surface_boundary_profiles,
            "uneven_profiles": uneven_surface_boundary_profiles,
        },
        "negative_controls": {
            "required_ids": REQUIRED_NEGATIVE_CONTROLS,
            "observed_ids": observed_negative_controls,
            "missing_ids": missing_negative_controls,
        },
        "long_horizon": {
            "required_ids": REQUIRED_SEQUENCE_CASES,
            "observed_ids": observed_sequence_ids,
            "missing_ids": missing_sequence_ids,
            "step_count": int(long_horizon.get("step_count", 0)),
        },
        "intra_bin_stress": {
            "required_bin_count": 48,
            "observed_bin_count": len(intra_bin_histogram),
            "required_probe_profiles": REQUIRED_INTRABIN_PROBES,
            "probe_histogram": dict(sorted(intra_probe_histogram.items())),
            "missing_bins": missing_intra_bins,
            "uneven_bins": uneven_intra_bins,
            "missing_probe_profiles": missing_intra_probes,
            "bin_mismatch_count": int(intra_bin_stress.get("bin_mismatch_count", 0)),
        },
        "rejection_error_coverage": {
            "required_errors": REQUIRED_REJECTION_ERRORS,
            "observed_errors": observed_errors,
            "missing_errors": missing_rejection_errors,
        },
    }


def _promotion_gate(
    *,
    optimizer_ok: bool,
    replay: Mapping[str, Any],
    coverage_profile: Mapping[str, Any],
    training_corpus_summary: Mapping[str, Any],
    source_manifest: list[Mapping[str, Any]],
) -> dict[str, Any]:
    optimized = replay.get("optimized", {}) if isinstance(replay.get("optimized"), Mapping) else replay
    hold_only = replay.get("hold_only", {}) if isinstance(replay.get("hold_only"), Mapping) else {}
    pid_like = replay.get("pid_like", {}) if isinstance(replay.get("pid_like"), Mapping) else {}
    safety_lanes = replay.get("safety_lanes", {}) if isinstance(replay.get("safety_lanes"), Mapping) else {}
    safety_boundary_sweep = (
        replay.get("safety_boundary_sweep", {})
        if isinstance(replay.get("safety_boundary_sweep"), Mapping)
        else {}
    )
    safety_interaction_sweep = (
        replay.get("safety_interaction_sweep", {})
        if isinstance(replay.get("safety_interaction_sweep"), Mapping)
        else {}
    )
    surface_boundary_sweep = (
        replay.get("surface_boundary_sweep", {})
        if isinstance(replay.get("surface_boundary_sweep"), Mapping)
        else {}
    )
    long_horizon = replay.get("long_horizon", {}) if isinstance(replay.get("long_horizon"), Mapping) else {}
    long_horizon_hold_only = (
        replay.get("long_horizon_hold_only", {})
        if isinstance(replay.get("long_horizon_hold_only"), Mapping)
        else {}
    )
    long_horizon_pid_like = (
        replay.get("long_horizon_pid_like", {})
        if isinstance(replay.get("long_horizon_pid_like"), Mapping)
        else {}
    )
    intra_bin_stress = (
        replay.get("intra_bin_stress", {})
        if isinstance(replay.get("intra_bin_stress"), Mapping)
        else {}
    )
    action_gate_diagnostics = (
        replay.get("action_gate_diagnostics", {})
        if isinstance(replay.get("action_gate_diagnostics"), Mapping)
        else {}
    )
    environment_curriculum_diagnostics = (
        replay.get("environment_curriculum_diagnostics", {})
        if isinstance(replay.get("environment_curriculum_diagnostics"), Mapping)
        else {}
    )
    checks = {
        "optimizer_ok": optimizer_ok,
        "policy_hash_present": bool(optimized.get("policy_hash")),
        "action_gate_diagnostics_ok": action_gate_diagnostics.get("ok") is True,
        "environment_curriculum_diagnostics_ok": environment_curriculum_diagnostics.get("ok") is True,
        "all_bins_covered": optimized.get("bin_count") == 48,
        "stress_grid_nonempty": optimized.get("scenario_count", 0) > 0,
        "optimized_safety_feasible_opportunities_complete": optimized.get("opportunity_miss_count") == 0,
        "optimized_safety_feasible_count_positive": optimized.get("safety_feasible_count", 0) > 0,
        "optimized_frontier_regret_zero": optimized.get("frontier_regret_total") == 0,
        "optimized_frontier_utility_complete": optimized.get("frontier_utility_completion_rate") == 1.0,
        "invalid_accept_count_zero": optimized.get("invalid_accept_count") == 0,
        "inconsistent_accept_count_zero": optimized.get("inconsistent_accept_count") == 0,
        "safety_lanes_reject_all": safety_lanes.get("approved_count") == 0,
        "safety_lanes_expected_errors_present": safety_lanes.get("missing_expected_error_count") == 0,
        "safety_boundary_sweep_ok": safety_boundary_sweep.get("ok") is True,
        "safety_boundary_inside_cases_approve": (
            safety_boundary_sweep.get("inside_count", 0) > 0
            and safety_boundary_sweep.get("inside_approved_count")
            == safety_boundary_sweep.get("inside_count")
        ),
        "safety_boundary_outside_cases_reject": (
            safety_boundary_sweep.get("outside_count", 0) > 0
            and safety_boundary_sweep.get("outside_approved_count") == 0
        ),
        "safety_boundary_expected_errors_present": (
            safety_boundary_sweep.get("outside_missing_expected_error_count") == 0
        ),
        "safety_boundary_invalid_accept_count_zero": (
            safety_boundary_sweep.get("invalid_accept_count") == 0
        ),
        "safety_interaction_sweep_ok": safety_interaction_sweep.get("ok") is True,
        "safety_interaction_inside_cases_approve": (
            safety_interaction_sweep.get("inside_count", 0) > 0
            and safety_interaction_sweep.get("inside_approved_count")
            == safety_interaction_sweep.get("inside_count")
        ),
        "safety_interaction_outside_cases_reject": (
            safety_interaction_sweep.get("outside_count", 0) > 0
            and safety_interaction_sweep.get("outside_approved_count") == 0
        ),
        "safety_interaction_expected_errors_present": (
            safety_interaction_sweep.get("outside_missing_expected_error_count") == 0
        ),
        "safety_interaction_invalid_accept_count_zero": (
            safety_interaction_sweep.get("invalid_accept_count") == 0
        ),
        "surface_boundary_sweep_ok": surface_boundary_sweep.get("ok") is True,
        "surface_boundary_profiles_complete": (
            surface_boundary_sweep.get("scenario_count") == len(REQUIRED_SURFACE_BOUNDARY_PROFILES)
            and not surface_boundary_sweep.get("missing_profiles", ())
            and not surface_boundary_sweep.get("uneven_profiles", ())
        ),
        "surface_boundary_selected_q_rows_complete": (
            surface_boundary_sweep.get("q_row_missing_count") == 0
        ),
        "surface_boundary_selected_cases_approve": (
            surface_boundary_sweep.get("approved_count") == surface_boundary_sweep.get("scenario_count")
            and surface_boundary_sweep.get("scenario_count", 0) > 0
        ),
        "surface_boundary_expected_rejections_present": (
            surface_boundary_sweep.get("missing_expected_rejection_count") == 0
        ),
        "surface_boundary_invalid_accept_count_zero": (
            surface_boundary_sweep.get("invalid_accept_count") == 0
        ),
        "negative_controls_reject_all": (
            isinstance(replay.get("negative_controls"), Mapping)
            and replay["negative_controls"].get("approved_count") == 0
        ),
        "negative_controls_expected_errors_present": (
            isinstance(replay.get("negative_controls"), Mapping)
            and replay["negative_controls"].get("missing_expected_error_count") == 0
        ),
        "negative_controls_invalid_accept_count_zero": (
            isinstance(replay.get("negative_controls"), Mapping)
            and replay["negative_controls"].get("invalid_accept_count") == 0
        ),
        "long_horizon_nonempty": long_horizon.get("step_count", 0) > 0,
        "long_horizon_ids_complete": not long_horizon.get("missing_ids", ()),
        "long_horizon_safety_feasible_opportunities_complete": long_horizon.get("opportunity_miss_count") == 0,
        "long_horizon_safety_feasible_count_positive": long_horizon.get("safety_feasible_count", 0) > 0,
        "long_horizon_invalid_accept_count_zero": long_horizon.get("invalid_accept_count") == 0,
        "long_horizon_inconsistent_accept_count_zero": long_horizon.get("inconsistent_accept_count") == 0,
        "long_horizon_frontier_regret_zero": long_horizon.get("frontier_regret_total") == 0,
        "long_horizon_frontier_utility_complete": long_horizon.get("frontier_utility_completion_rate") == 1.0,
        "long_horizon_final_states_safe": not long_horizon.get("final_state_error_histogram", {}),
        "long_horizon_cumulative_drift_within_limits": not long_horizon.get("cumulative_drift_failures", ()),
        "long_horizon_trajectory_budget_within_limits": not long_horizon.get("trajectory_budget_failures", ()),
        "long_horizon_hold_only_invalid_accept_count_zero": long_horizon_hold_only.get("invalid_accept_count") == 0,
        "long_horizon_pid_like_invalid_accept_count_zero": long_horizon_pid_like.get("invalid_accept_count") == 0,
        "intra_bin_stress_ok": intra_bin_stress.get("ok") is True,
        "intra_bin_stress_nonempty": intra_bin_stress.get("scenario_count", 0) > 0,
        "intra_bin_stress_bins_complete": intra_bin_stress.get("bin_count") == 48,
        "intra_bin_stress_profiles_complete": (
            intra_bin_stress.get("probe_profile_count") == len(REQUIRED_INTRABIN_PROBES)
        ),
        "intra_bin_stress_observed_bins_match_expected": intra_bin_stress.get("bin_mismatch_count") == 0,
        "intra_bin_stress_safety_feasible_opportunities_complete": (
            intra_bin_stress.get("opportunity_miss_count") == 0
        ),
        "intra_bin_stress_invalid_accept_count_zero": intra_bin_stress.get("invalid_accept_count") == 0,
        "intra_bin_stress_inconsistent_accept_count_zero": (
            intra_bin_stress.get("inconsistent_accept_count") == 0
        ),
        "intra_bin_stress_frontier_regret_zero": intra_bin_stress.get("frontier_regret_total") == 0,
        "intra_bin_stress_frontier_utility_complete": (
            intra_bin_stress.get("frontier_utility_completion_rate") == 1.0
        ),
        "long_horizon_utility_beats_hold_only": (
            long_horizon.get("utility_score_total", 0) > long_horizon_hold_only.get("utility_score_total", 0)
        ),
        "long_horizon_utility_not_worse_than_pid_like": (
            long_horizon.get("utility_score_total", 0) >= long_horizon_pid_like.get("utility_score_total", 0)
        ),
        "utility_beats_hold_only": optimized.get("utility_score_total", 0) > hold_only.get("utility_score_total", 0),
        "utility_not_worse_than_pid_like": optimized.get("utility_score_total", 0) >= pid_like.get("utility_score_total", 0),
        "coverage_profile_ok": coverage_profile.get("ok") is True,
        "training_corpus_ok": training_corpus_summary.get("ok") is True,
        "training_ranking_diagnostics_ok": (
            isinstance(training_corpus_summary.get("ranking_diagnostics"), Mapping)
            and training_corpus_summary["ranking_diagnostics"].get("ok") is True
        ),
        "training_sequence_ranking_diagnostics_ok": (
            isinstance(training_corpus_summary.get("sequence_ranking_diagnostics"), Mapping)
            and training_corpus_summary["sequence_ranking_diagnostics"].get("ok") is True
        ),
        "training_pairwise_diagnostics_ok": (
            isinstance(training_corpus_summary.get("pairwise_diagnostics"), Mapping)
            and training_corpus_summary["pairwise_diagnostics"].get("ok") is True
        ),
        "training_supervision_targets_ok": (
            isinstance(training_corpus_summary.get("supervision_targets"), Mapping)
            and training_corpus_summary["supervision_targets"].get("ok") is True
        ),
        "training_split_diagnostics_ok": (
            isinstance(training_corpus_summary.get("split_diagnostics"), Mapping)
            and training_corpus_summary["split_diagnostics"].get("ok") is True
        ),
        "training_feature_contract_ok": (
            isinstance(training_corpus_summary.get("feature_contract"), Mapping)
            and training_corpus_summary["feature_contract"].get("ok") is True
        ),
        "training_diversity_diagnostics_ok": (
            isinstance(training_corpus_summary.get("diversity_diagnostics"), Mapping)
            and training_corpus_summary["diversity_diagnostics"].get("ok") is True
        ),
        "training_entropy_diagnostics_ok": (
            isinstance(training_corpus_summary.get("entropy_diagnostics"), Mapping)
            and training_corpus_summary["entropy_diagnostics"].get("ok") is True
        ),
        "source_manifest_complete": all(item.get("exists") is True for item in source_manifest),
    }
    return {
        "ok": all(checks.values()),
        "checks": checks,
        "boundary": "Promotion gate checks replay safety of the policy artifact; it does not prove market optimality.",
    }


def build_factory_report(*, out_dir: Path, julia_bin: str, policy_input: Path | None) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    raw_policy_path = out_dir / "optimized_policy.raw.json"
    optimizer_report_path = out_dir / "optimizer_report.json"
    frozen_policy_path = out_dir / "optimized_policy.frozen.json"
    training_corpus_path = out_dir / "ebr_training_corpus.json"
    residual_model_path = out_dir / "ebr_residual_model.json"

    if policy_input is None:
        optimizer_run = _run_julia_optimizer(
            julia_bin=julia_bin,
            policy_path=raw_policy_path,
            report_path=optimizer_report_path,
        )
        if not optimizer_run["ok"]:
            raise RuntimeError(f"julia_optimizer_failed:{optimizer_run['stderr']}")
        raw_policy = _load_json(raw_policy_path)
        optimizer_report = _load_json(optimizer_report_path)
    else:
        raw_policy = _load_json(policy_input)
        _write_json(raw_policy_path, raw_policy)
        optimizer_report = {
            "schema": "zenodex.autonomous_governance.external_policy_input.v1",
            "ok": True,
            "source": str(policy_input),
        }
        _write_json(optimizer_report_path, optimizer_report)
        optimizer_run = {
            "command": [],
            "returncode": 0,
            "stdout": "",
            "stderr": "",
            "ok": True,
            "skipped": True,
        }

    baseline_frozen_policy = _freeze_policy(raw_policy)
    residual_source_corpus = _build_training_corpus(baseline_frozen_policy)
    residual_model = _train_ebr_residual_lookup_model(residual_source_corpus)
    residual_candidate_policy = _policy_with_trained_ebr_residual(
        baseline_frozen_policy,
        residual_model,
    )
    frozen_policy = _freeze_policy(residual_candidate_policy)
    residual_model = {
        **residual_model,
        "applied_to_policy": residual_model.get("ok") is True,
        "candidate_policy_hash": frozen_policy["policy_hash"],
    }
    _write_json(residual_model_path, residual_model)
    _write_json(frozen_policy_path, frozen_policy)

    hold_policy = _hold_only_policy(frozen_policy)
    pid_policy = _pid_like_policy(frozen_policy)
    optimized_replay = _replay_policy(frozen_policy, label="optimized")
    hold_replay = _replay_policy(hold_policy, label="hold_only")
    pid_replay = _replay_policy(pid_policy, label="pid_like")
    source_manifest = _source_manifest()
    replay = {
        "optimized": optimized_replay,
        "hold_only": hold_replay,
        "pid_like": pid_replay,
        "safety_lanes": _replay_safety_lanes(frozen_policy, label="optimized_safety_lanes"),
        "safety_boundary_sweep": _replay_safety_boundary_sweep(
            frozen_policy,
            label="optimized_safety_boundary_sweep",
        ),
        "safety_interaction_sweep": _replay_safety_interaction_sweep(
            frozen_policy,
            label="optimized_safety_interaction_sweep",
        ),
        "surface_boundary_sweep": _replay_surface_boundary_sweep(
            frozen_policy,
            label="optimized_surface_boundary_sweep",
        ),
        "negative_controls": _replay_negative_controls(frozen_policy, label="adversarial_negative_controls"),
        "action_gate_diagnostics": _action_gate_diagnostics(frozen_policy),
        "intra_bin_stress": _replay_intra_bin_stress(frozen_policy, label="optimized_intra_bin_stress"),
        "long_horizon": _replay_long_horizon_sequences(frozen_policy, label="multi_epoch_sequences"),
        "long_horizon_hold_only": _replay_long_horizon_sequences(
            hold_policy, label="multi_epoch_sequences_hold_only"
        ),
        "long_horizon_pid_like": _replay_long_horizon_sequences(
            pid_policy, label="multi_epoch_sequences_pid_like"
        ),
    }
    replay["environment_curriculum_diagnostics"] = _environment_curriculum_diagnostics(replay)
    coverage_profile = _coverage_profile(replay)
    training_corpus = _build_training_corpus(frozen_policy)
    _write_json(training_corpus_path, training_corpus)
    training_corpus_summary = dict(training_corpus["summary"])
    promotion_gate = _promotion_gate(
        optimizer_ok=bool(optimizer_run.get("ok")) and bool(optimizer_report.get("ok", True)),
        replay=replay,
        coverage_profile=coverage_profile,
        training_corpus_summary=training_corpus_summary,
        source_manifest=source_manifest,
    )

    report = {
        "schema": FACTORY_SCHEMA,
        "generated_at": _utc_now(),
        "ok": promotion_gate["ok"],
        "artifacts": {
            "out_dir": str(out_dir),
            "raw_policy": str(raw_policy_path),
            "frozen_policy": str(frozen_policy_path),
            "ebr_training_corpus": str(training_corpus_path),
            "ebr_residual_model": str(residual_model_path),
            "optimizer_report": str(optimizer_report_path),
            "factory_report": str(out_dir / "policy_factory_report.json"),
        },
        "optimizer_run": optimizer_run,
        "optimizer_report_summary": {
            "schema": optimizer_report.get("schema", ""),
            "ok": optimizer_report.get("ok", False),
            "state_count": optimizer_report.get("state_count"),
            "action_count": optimizer_report.get("action_count"),
            "objective": optimizer_report.get("objective", ""),
        },
        "policy": {
            "policy_id": frozen_policy.get("policy_id", ""),
            "policy_hash": frozen_policy["policy_hash"],
            "schema": frozen_policy.get("schema", ""),
        },
        "replay": replay,
        "coverage_profile": coverage_profile,
        "ebr_residual_model": residual_model,
        "training_corpus_summary": training_corpus_summary,
        "promotion_gate": promotion_gate,
        "source_manifest": source_manifest,
        "non_claims": [
            "does_not_authorize_settlement",
            "does_not_replace_python_or_tau_governance_gates",
            "does_not_train_online",
            "does_not_prove_global_dynamic_optimality",
            "does_not_claim_oracle_truth",
        ],
    }
    _write_json(out_dir / "policy_factory_report.json", report)
    return report


def build_policy_artifact_check_report(
    *,
    policy_path: Path,
    training_corpus_path: Path | None = None,
    optimizer_report_path: Path | None = None,
    factory_report_path: Path | None = None,
    report_output: Path | None = None,
) -> dict[str, Any]:
    policy_from_disk = _load_json(policy_path)
    computed_policy_hash = policy_content_hash_v1(policy_from_disk)
    embedded_policy_hash = str(policy_from_disk.get("policy_hash", ""))
    checked_policy = dict(policy_from_disk)
    checked_policy["policy_hash"] = computed_policy_hash

    hold_policy = _hold_only_policy(checked_policy)
    pid_policy = _pid_like_policy(checked_policy)
    optimized_replay = _replay_policy(checked_policy, label="optimized")
    hold_replay = _replay_policy(hold_policy, label="hold_only")
    pid_replay = _replay_policy(pid_policy, label="pid_like")
    replay = {
        "optimized": optimized_replay,
        "hold_only": hold_replay,
        "pid_like": pid_replay,
        "safety_lanes": _replay_safety_lanes(checked_policy, label="optimized_safety_lanes"),
        "safety_boundary_sweep": _replay_safety_boundary_sweep(
            checked_policy,
            label="optimized_safety_boundary_sweep",
        ),
        "safety_interaction_sweep": _replay_safety_interaction_sweep(
            checked_policy,
            label="optimized_safety_interaction_sweep",
        ),
        "surface_boundary_sweep": _replay_surface_boundary_sweep(
            checked_policy,
            label="optimized_surface_boundary_sweep",
        ),
        "negative_controls": _replay_negative_controls(checked_policy, label="adversarial_negative_controls"),
        "action_gate_diagnostics": _action_gate_diagnostics(checked_policy),
        "intra_bin_stress": _replay_intra_bin_stress(checked_policy, label="optimized_intra_bin_stress"),
        "long_horizon": _replay_long_horizon_sequences(checked_policy, label="multi_epoch_sequences"),
        "long_horizon_hold_only": _replay_long_horizon_sequences(
            hold_policy, label="multi_epoch_sequences_hold_only"
        ),
        "long_horizon_pid_like": _replay_long_horizon_sequences(
            pid_policy, label="multi_epoch_sequences_pid_like"
        ),
    }
    replay["environment_curriculum_diagnostics"] = _environment_curriculum_diagnostics(replay)
    coverage_profile = _coverage_profile(replay)
    recomputed_training_corpus = _build_training_corpus(checked_policy)
    training_corpus_summary = dict(recomputed_training_corpus["summary"])
    source_manifest = _source_manifest()

    optimizer_report: dict[str, Any] = {}
    if optimizer_report_path is not None:
        optimizer_report = _load_json(optimizer_report_path)
    optimizer_ok = optimizer_report.get("ok") is True

    factory_report: dict[str, Any] = {}
    if factory_report_path is not None:
        factory_report = _load_json(factory_report_path)
    factory_policy = factory_report.get("policy", {}) if isinstance(factory_report.get("policy", {}), Mapping) else {}
    factory_source_manifest = (
        factory_report.get("source_manifest", [])
        if isinstance(factory_report.get("source_manifest", []), list)
        else []
    )
    factory_replay = factory_report.get("replay", {}) if isinstance(factory_report.get("replay", {}), Mapping) else {}
    factory_coverage_profile = (
        factory_report.get("coverage_profile", {})
        if isinstance(factory_report.get("coverage_profile", {}), Mapping)
        else {}
    )
    factory_training_summary = (
        factory_report.get("training_corpus_summary", {})
        if isinstance(factory_report.get("training_corpus_summary", {}), Mapping)
        else {}
    )
    factory_promotion_gate = (
        factory_report.get("promotion_gate", {})
        if isinstance(factory_report.get("promotion_gate", {}), Mapping)
        else {}
    )
    factory_source_manifest_hash = _sha256_json(factory_source_manifest) if factory_source_manifest else ""
    current_source_manifest_hash = _sha256_json(source_manifest)
    factory_replay_hash = _sha256_json(factory_replay) if factory_replay else ""
    current_replay_hash = _sha256_json(replay)
    factory_coverage_hash = _sha256_json(factory_coverage_profile) if factory_coverage_profile else ""
    current_coverage_hash = _sha256_json(coverage_profile)
    factory_training_summary_hash = _sha256_json(factory_training_summary) if factory_training_summary else ""
    current_training_summary_hash = _sha256_json(training_corpus_summary)

    provided_training_corpus: dict[str, Any] = {}
    if training_corpus_path is not None:
        provided_training_corpus = _load_json(training_corpus_path)

    provided_corpus_summary = (
        provided_training_corpus.get("summary", {})
        if isinstance(provided_training_corpus.get("summary", {}), Mapping)
        else {}
    )
    provided_corpus_policy_hash = str(provided_training_corpus.get("policy_hash", ""))
    provided_corpus_hash = _sha256_json(provided_training_corpus) if provided_training_corpus else ""
    recomputed_corpus_hash = _sha256_json(recomputed_training_corpus)
    corpus_summary_matches = (
        bool(provided_training_corpus)
        and _json_normalized(provided_corpus_summary) == _json_normalized(training_corpus_summary)
    )
    corpus_rows_match = (
        bool(provided_training_corpus)
        and _json_normalized(provided_training_corpus.get("rows", []))
        == _json_normalized(recomputed_training_corpus.get("rows", []))
    )

    promotion_gate = _promotion_gate(
        optimizer_ok=optimizer_ok,
        replay=replay,
        coverage_profile=coverage_profile,
        training_corpus_summary=training_corpus_summary,
        source_manifest=source_manifest,
    )
    factory_promotion_gate_hash = _sha256_json(factory_promotion_gate) if factory_promotion_gate else ""
    current_promotion_gate_hash = _sha256_json(promotion_gate)
    artifact_checks = {
        "policy_path_exists": policy_path.exists(),
        "policy_hash_present": bool(embedded_policy_hash),
        "policy_hash_matches_content": embedded_policy_hash == computed_policy_hash,
        "optimizer_report_provided": optimizer_report_path is not None,
        "optimizer_report_ok": optimizer_ok,
        "factory_report_provided": factory_report_path is not None,
        "factory_report_schema_valid": factory_report.get("schema") == FACTORY_SCHEMA,
        "factory_report_ok": factory_report.get("ok") is True,
        "factory_report_policy_hash_matches": factory_policy.get("policy_hash") == computed_policy_hash,
        "factory_report_policy_hash_matches_embedded": (
            factory_policy.get("policy_hash") == embedded_policy_hash
        ),
        "factory_report_source_manifest_provided": bool(factory_source_manifest),
        "factory_report_source_manifest_matches_current": (
            bool(factory_source_manifest)
            and _json_normalized(factory_source_manifest) == _json_normalized(source_manifest)
        ),
        "factory_report_replay_provided": bool(factory_replay),
        "factory_report_replay_matches_recomputed": (
            bool(factory_replay) and _json_normalized(factory_replay) == _json_normalized(replay)
        ),
        "factory_report_coverage_profile_provided": bool(factory_coverage_profile),
        "factory_report_coverage_profile_matches_recomputed": (
            bool(factory_coverage_profile)
            and _json_normalized(factory_coverage_profile) == _json_normalized(coverage_profile)
        ),
        "factory_report_training_summary_provided": bool(factory_training_summary),
        "factory_report_training_summary_matches_recomputed": (
            bool(factory_training_summary)
            and _json_normalized(factory_training_summary) == _json_normalized(training_corpus_summary)
        ),
        "factory_report_promotion_gate_provided": bool(factory_promotion_gate),
        "factory_report_promotion_gate_matches_recomputed": (
            bool(factory_promotion_gate)
            and _json_normalized(factory_promotion_gate) == _json_normalized(promotion_gate)
        ),
        "training_corpus_provided": training_corpus_path is not None,
        "training_corpus_schema_valid": provided_training_corpus.get("schema") == EBR_TRAINING_CORPUS_SCHEMA,
        "training_corpus_policy_hash_matches": provided_corpus_policy_hash == computed_policy_hash,
        "training_corpus_summary_matches_recomputed": corpus_summary_matches,
        "training_corpus_rows_match_recomputed": corpus_rows_match,
    }
    artifact_gate = {
        "ok": all(artifact_checks.values()),
        "checks": artifact_checks,
        "boundary": "Artifact checks validate frozen-policy evidence on disk; runtime authority still belongs to deterministic gates.",
    }
    report = {
        "schema": ARTIFACT_CHECK_SCHEMA,
        "generated_at": _utc_now(),
        "ok": artifact_gate["ok"] and promotion_gate["ok"],
        "artifacts": {
            "policy": str(policy_path),
            "training_corpus": str(training_corpus_path) if training_corpus_path else "",
            "optimizer_report": str(optimizer_report_path) if optimizer_report_path else "",
            "factory_report": str(factory_report_path) if factory_report_path else "",
            "check_report": str(report_output) if report_output else "",
        },
        "policy": {
            "policy_id": checked_policy.get("policy_id", ""),
            "embedded_policy_hash": embedded_policy_hash,
            "computed_policy_hash": computed_policy_hash,
            "schema": checked_policy.get("schema", ""),
        },
        "optimizer_report_summary": {
            "schema": optimizer_report.get("schema", ""),
            "ok": optimizer_report.get("ok", False),
            "state_count": optimizer_report.get("state_count"),
            "action_count": optimizer_report.get("action_count"),
            "objective": optimizer_report.get("objective", ""),
        },
        "training_corpus_artifact": {
            "provided_sha256": provided_corpus_hash,
            "recomputed_sha256": recomputed_corpus_hash,
            "provided_policy_hash": provided_corpus_policy_hash,
            "recomputed_policy_hash": computed_policy_hash,
        },
        "source_manifest_artifact": {
            "provided_sha256": factory_source_manifest_hash,
            "recomputed_sha256": current_source_manifest_hash,
            "provided_count": len(factory_source_manifest),
            "recomputed_count": len(source_manifest),
        },
        "factory_report_artifact": {
            "provided_replay_sha256": factory_replay_hash,
            "recomputed_replay_sha256": current_replay_hash,
            "provided_coverage_profile_sha256": factory_coverage_hash,
            "recomputed_coverage_profile_sha256": current_coverage_hash,
            "provided_training_summary_sha256": factory_training_summary_hash,
            "recomputed_training_summary_sha256": current_training_summary_hash,
            "provided_promotion_gate_sha256": factory_promotion_gate_hash,
            "recomputed_promotion_gate_sha256": current_promotion_gate_hash,
        },
        "replay": replay,
        "coverage_profile": coverage_profile,
        "training_corpus_summary": training_corpus_summary,
        "artifact_gate": artifact_gate,
        "promotion_gate": promotion_gate,
        "source_manifest": source_manifest,
        "non_claims": [
            "does_not_authorize_settlement",
            "does_not_replace_python_or_tau_governance_gates",
            "does_not_train_online",
            "does_not_prove_global_dynamic_optimality",
            "does_not_claim_oracle_truth",
        ],
    }
    if report_output is not None:
        _write_json(report_output, report)
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", help="directory for generated policy and replay artifacts")
    parser.add_argument("--julia-bin", default="julia", help="Julia executable to use")
    parser.add_argument("--policy-input", help="use an existing policy JSON instead of running Julia")
    parser.add_argument("--check-policy", help="validate an existing frozen policy JSON artifact")
    parser.add_argument("--training-corpus", help="EBRM training corpus JSON to compare against recomputed replay labels")
    parser.add_argument("--optimizer-report", help="optimizer report JSON associated with --check-policy")
    parser.add_argument("--factory-report", help="factory report JSON associated with --check-policy")
    parser.add_argument("--report-output", help="write the check report JSON to this path")
    parser.add_argument("--quiet", action="store_true", help="do not print the factory report JSON")
    args = parser.parse_args(argv)

    try:
        if args.check_policy:
            report = build_policy_artifact_check_report(
                policy_path=Path(args.check_policy),
                training_corpus_path=Path(args.training_corpus) if args.training_corpus else None,
                optimizer_report_path=Path(args.optimizer_report) if args.optimizer_report else None,
                factory_report_path=Path(args.factory_report) if args.factory_report else None,
                report_output=Path(args.report_output) if args.report_output else None,
            )
        else:
            if not args.out_dir:
                raise ValueError("out_dir_required_unless_check_policy_is_set")
            report = build_factory_report(
                out_dir=Path(args.out_dir),
                julia_bin=args.julia_bin,
                policy_input=Path(args.policy_input) if args.policy_input else None,
            )
    except Exception as exc:
        error = {
            "schema": ARTIFACT_CHECK_SCHEMA if args.check_policy else FACTORY_SCHEMA,
            "ok": False,
            "status": "failed",
            "errors": [str(exc)],
        }
        sys.stdout.write(json.dumps(error, indent=2, sort_keys=True) + "\n")
        return 2

    if not args.quiet:
        sys.stdout.write(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 0 if report.get("ok") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
