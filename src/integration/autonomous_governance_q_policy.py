"""Deterministic autonomous-governance policy runner.

The live path is intentionally table-driven. Offline Q-learning may produce the
table, but runtime evaluation is a pure lookup plus bounded revision check.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from src.integration.autonomous_governance_hostile_input import safe_field_label
from src.integration.tau_witness import build_revision_policy_v1_step
from src.integration.zeno_ledger_v0 import hash_v0
from src.tau_specs.governance import gov_gate

AUTONOMOUS_GOVERNANCE_Q_POLICY_SCHEMA_V1 = "zenodex.autonomous_governance.q_policy.v1"
AUTONOMOUS_GOVERNANCE_Q_RECEIPT_SCHEMA_V1 = "zenodex.autonomous_governance.q_receipt.v1"
AUTONOMOUS_GOVERNANCE_SURFACE_STEP_SCHEMA_V1 = "zenodex.autonomous_governance.q_surface_step.v1"
AUTONOMOUS_GOVERNANCE_SURFACE_CONTEXT_SCHEMA_V1 = (
    "zenodex.autonomous_governance.committed_surface_context.v1"
)
AUTONOMOUS_GOVERNANCE_SURFACE_ADMISSION_SCHEMA_V1 = (
    "zenodex.autonomous_governance.q_surface_admission.v1"
)
AUTONOMOUS_GOVERNANCE_SURFACE_EVAL_BUNDLE_SCHEMA_V1 = (
    "zenodex.autonomous_governance.q_surface_policy_eval_bundle.v1"
)
ALLOWED_SURFACE_ADMISSION_REQUEST_FIELDS_V1 = frozenset(
    {
        "schema",
        "tx_id",
        "time_ms",
        "policy",
        "expected_policy_hash",
        "expected_committed_context_hash",
        "surface_state",
        "observation",
        "current_epoch",
        "proposal_epoch",
        "last_update_epoch",
        "previous_approved_deltas",
        "trajectory_budget",
        "trajectory_used",
    }
)
FORBIDDEN_SURFACE_ADMISSION_RESULT_FIELDS_V1 = frozenset(
    {
        "action_id",
        "admission_hash",
        "applied_state",
        "gate_recheck",
        "proposed",
        "proposed_state",
        "receipt",
        "receipt_hash",
        "scores",
        "step",
        "step_hash",
    }
)

PARAMETER_NAMES_V1 = (
    "fee",
    "buyback",
    "rebate",
    "floor",
    "unit",
    "tier1",
    "tier2",
    "weight1",
    "weight2",
    "weight3",
)

SURFACE_PARAMETER_NAMES_V1 = (
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

AUTOGOVNEXT_FORBIDDEN_AUTHORITY_PARAMETERS_V1 = frozenset(
    {
        "config_digest",
        "deployment_profile",
        "governance_authority_hash",
        "module_versions_digest",
        "policy_registry_hash",
        "risc0_image_id",
        "sequencer_set_hash",
        "signature_set_root",
        "signer_set_hash",
        "threshold_bls_registry_hash",
        "verifier_image_id",
        "verifier_key_hash",
    }
)

OBSERVATION_FIELDS_V1 = frozenset(
    {
        "observed_price_bps",
        "target_price_bps",
        "deviation_bps",
        "volatility_bps",
        "divergence_bps",
        "freshness_lag_epochs",
        "liquidity_depth_bps",
        "oracle_confidence_bps",
        "liquidity_concentration_bps",
        "recent_governance_churn_bps",
        "proof_market_health_bps",
        "validator_stress_bps",
        "network_stress_bps",
    }
)

U16_MAX = (1 << 16) - 1
U32_MAX = (1 << 32) - 1
FIXED_POINT_SCALE = 1_000_000
SELECTION_BLOCKER_SCORE_PENALTY = 1_000_000_000

# Bind the trusted governance gate call surface once at import. Runtime table
# evaluation should not be able to pick up a later monkeypatch or forged wrapper.
_GOV_MASTER_REVISION = gov_gate.MasterRevision
_GOV_FEE_REVISION_OK = gov_gate.fee_revision_ok
_GOV_ROUTER_REVISION_OK = gov_gate.router_revision_ok
_GOV_COLLATERAL_RATIO_REVISION_OK = gov_gate.collateral_ratio_revision_ok
_GOV_WHALE_DEFENSE_REVISION_OK = gov_gate.whale_defense_revision_ok
_GOV_FUNDING_RATE_REVISION_OK = gov_gate.funding_rate_revision_ok


def _trusted_master_revision_ok(revision: object) -> bool:
    """Evaluate the master gate through the import-bound surface gate aliases."""

    if type(revision) is not _GOV_MASTER_REVISION:
        raise TypeError("master_revision_ok requires a MasterRevision (exact type)")
    return (
        _GOV_FEE_REVISION_OK(
            revision.approved,
            revision.exec_req,
            revision.proposal_ts,
            revision.current_ts,
            revision.fee_curr_bps,
            revision.fee_next_bps,
        )
        and _GOV_ROUTER_REVISION_OK(
            revision.approved,
            revision.exec_req,
            revision.proposal_ts,
            revision.current_ts,
            revision.buyburn_next_bps,
            revision.stakers_next_bps,
            revision.reserve_next_bps,
            revision.hosts_next_bps,
            revision.buyburn_curr_bps,
            revision.stakers_curr_bps,
            revision.reserve_curr_bps,
            revision.hosts_curr_bps,
        )
        and _GOV_COLLATERAL_RATIO_REVISION_OK(
            revision.approved,
            revision.exec_req,
            revision.proposal_ts,
            revision.current_ts,
            revision.mcr_curr_bps,
            revision.mcr_next_bps,
            revision.ccr_curr_bps,
            revision.ccr_next_bps,
        )
        and _GOV_WHALE_DEFENSE_REVISION_OK(
            revision.approved,
            revision.exec_req,
            revision.proposal_ts,
            revision.current_ts,
            revision.staker_bps_curr,
            revision.staker_bps_next,
        )
    )


_GOV_MASTER_REVISION_OK = _trusted_master_revision_ok


@dataclass(frozen=True)
class BoundedParameter:
    current: int
    minimum: int
    maximum: int
    step: int

    def __post_init__(self) -> None:
        for name in ("current", "minimum", "maximum", "step"):
            _require_nonnegative_int(getattr(self, name), name=f"BoundedParameter.{name}")

    def as_dict(self) -> dict[str, int]:
        return {
            "current": self.current,
            "minimum": self.minimum,
            "maximum": self.maximum,
            "step": self.step,
        }


def policy_content_hash_v1(policy: Mapping[str, Any]) -> str:
    """Return the canonical hash for a frozen autonomous-governance policy."""

    body = dict(policy)
    body.pop("policy_hash", None)
    return hash_v0("autonomous_governance_q_policy_v1", body)


def governance_surface_context_hash_v1(
    *,
    surface_state: Mapping[str, Any],
    current_epoch: int,
    proposal_epoch: int,
    last_update_epoch: int | None = None,
    previous_approved_deltas: Mapping[str, Any] | None = None,
    trajectory_used: Mapping[str, Any] | None = None,
) -> str:
    """Hash the committed state context consumed by a surface-policy step.

    The hash covers the committed surface values plus the epoch and trajectory
    bookkeeping that make the pointwise and long-horizon gates meaningful.
    """

    errors: list[str] = []
    state, state_errors = _normalize_surface_state(surface_state)
    errors.extend(state_errors)
    normalized_current_epoch = _require_nonnegative_int_or_error(
        current_epoch, name="current_epoch", errors=errors
    )
    normalized_proposal_epoch = _require_nonnegative_int_or_error(
        proposal_epoch, name="proposal_epoch", errors=errors
    )
    normalized_last_update_epoch = _normalize_optional_nonnegative_int(
        last_update_epoch,
        name="last_update_epoch",
        errors=errors,
    )
    normalized_trajectory_used, trajectory_used_errors = _normalize_trajectory_used(trajectory_used)
    errors.extend(trajectory_used_errors)
    normalized_previous_deltas, previous_delta_errors = _normalize_previous_approved_deltas(
        previous_approved_deltas
    )
    errors.extend(previous_delta_errors)
    if errors:
        raise ValueError(";".join(errors))
    context = _surface_context_payload(
        state=state,
        current_epoch=normalized_current_epoch,
        proposal_epoch=normalized_proposal_epoch,
        last_update_epoch=normalized_last_update_epoch,
        previous_approved_deltas=normalized_previous_deltas,
        trajectory_used=normalized_trajectory_used,
    )
    return _surface_context_hash(context)


def _is_canonical_hash_v0(value: object) -> bool:
    if not isinstance(value, str):
        return False
    if len(value) != 66 or not value.startswith("0x"):
        return False
    return all(ch in "0123456789abcdef" for ch in value[2:])


def _policy_content_hash_for_receipt(policy: object, errors: list[str]) -> str:
    if not isinstance(policy, Mapping):
        errors.append("policy_hash_unavailable")
        return ""
    try:
        return policy_content_hash_v1(policy)
    except (TypeError, ValueError):
        errors.append("policy_hash_unavailable")
        return ""


def q_learning_update_fixed_point_v1(
    *,
    q_value: int,
    reward: int,
    next_best_q: int,
    alpha_ppm: int,
    gamma_ppm: int,
) -> int:
    """Deterministic fixed-point Q-learning update for offline table training.

    Runtime governance evaluation does not call this function. It exists to make
    the training update reproducible when a table artifact is generated offline.
    """

    for name, value in {
        "q_value": q_value,
        "reward": reward,
        "next_best_q": next_best_q,
        "alpha_ppm": alpha_ppm,
        "gamma_ppm": gamma_ppm,
    }.items():
        _require_int(value, name=name)
    if not 0 <= alpha_ppm <= FIXED_POINT_SCALE:
        raise ValueError("alpha_ppm must be between 0 and 1000000")
    if not 0 <= gamma_ppm <= FIXED_POINT_SCALE:
        raise ValueError("gamma_ppm must be between 0 and 1000000")
    target = reward + ((gamma_ppm * next_best_q) // FIXED_POINT_SCALE)
    return q_value + ((alpha_ppm * (target - q_value)) // FIXED_POINT_SCALE)


def evaluate_autonomous_governance_q_policy_v1(
    *,
    policy: Mapping[str, Any],
    parameters: Mapping[str, Mapping[str, Any] | BoundedParameter],
    observation: Mapping[str, Any],
    current_epoch: int,
    proposal_epoch: int,
    min_delay_epochs: int,
    last_update_epoch: int | None = None,
    expected_policy_hash: str | None = None,
) -> dict[str, Any]:
    """Evaluate a frozen Q-table policy and build a revision-policy packet.

    The returned packet can be fed to `revision_policy_v1.tau`. A failed safety,
    table, hash, or envelope check sets `approved=0` in that packet.
    """

    errors: list[str] = []
    normalized_policy, policy_errors = _normalize_policy(policy)
    errors.extend(policy_errors)

    policy_hash = _policy_content_hash_for_receipt(policy, errors)
    if expected_policy_hash is not None and expected_policy_hash != policy_hash:
        errors.append("policy_hash_mismatch")

    params, param_errors = _normalize_parameters(parameters)
    errors.extend(param_errors)

    obs, obs_errors = _normalize_observation(observation)
    errors.extend(obs_errors)

    normalized_current_epoch = _require_nonnegative_int_or_error(
        current_epoch, name="current_epoch", errors=errors
    )
    normalized_proposal_epoch = _require_nonnegative_int_or_error(
        proposal_epoch, name="proposal_epoch", errors=errors
    )
    normalized_min_delay = _require_nonnegative_int_or_error(
        min_delay_epochs, name="min_delay_epochs", errors=errors
    )

    safety_errors = _safety_errors(
        normalized_policy,
        obs,
        current_epoch=normalized_current_epoch,
        last_update_epoch=last_update_epoch,
    )
    errors.extend(safety_errors)

    action_id = ""
    scores: dict[str, int] = {}
    state_bins: dict[str, int] = {}
    selected_action: dict[str, Any] = {"id": "", "deltas": {}}
    if normalized_policy and obs:
        action_id, selected_action, scores, state_bins, selection_errors = _select_action(
            normalized_policy, obs
        )
        errors.extend(selection_errors)

    proposed = _propose_parameters(params, selected_action)
    envelope_errors = _revision_envelope_errors(params, proposed)
    errors.extend(envelope_errors)

    approved = 1 if not errors else 0
    packet_params = {
        name: params.get(name, BoundedParameter(current=0, minimum=0, maximum=0, step=0))
        for name in PARAMETER_NAMES_V1
    }
    packet_proposed = {name: proposed.get(name, packet_params[name].current) for name in PARAMETER_NAMES_V1}
    revision_step = _build_revision_step(
        params=packet_params,
        proposed=packet_proposed,
        approved=approved,
        current_epoch=normalized_current_epoch,
        proposal_epoch=normalized_proposal_epoch,
        min_delay_epochs=normalized_min_delay,
    )

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_Q_RECEIPT_SCHEMA_V1,
        "policy_hash": policy_hash,
        "action_id": action_id,
        "state_bins": state_bins,
        "scores": scores,
        "observation": obs,
        "parameters": {name: params[name].as_dict() for name in PARAMETER_NAMES_V1 if name in params},
        "proposed": proposed,
        "revision_policy": "revision_policy_v1",
        "revision_step": revision_step,
        "approved": bool(approved),
        "ok": not errors,
        "errors": tuple(errors),
        "not_claimed": (
            "does_not_authorize_settlement",
            "does_not_change_immutable_rules",
            "does_not_claim_oracle_truth",
            "does_not_train_q_table_online",
        ),
    }
    return {**body, "receipt_hash": hash_v0("autonomous_governance_q_receipt_v1", body)}


def sample_autonomous_governance_q_policy_v1() -> dict[str, Any]:
    """Return a small deterministic policy artifact suitable for tests and demos."""

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
    """Return a Q-table policy whose actions target the verified governance surfaces."""

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
            {"id": "raise_fee_10_tighten_funding_5", "deltas": {"fee_bps": 10, "funding_cap_bps": -5}},
            {"id": "shift_router_to_reserve_100", "deltas": {"buyburn_bps": -100, "reserve_bps": 100}},
        ],
        "q_layers": [
            {
                "id": "price_deviation_pressure",
                "features": ["deviation_bps"],
                "q_table": {
                    "0": {"hold": 3},
                    "1": {"hold": 3, "raise_fee_10": 1},
                    "2": {"raise_fee_10": 5, "hold": 1},
                    "3": {"raise_fee_10_tighten_funding_5": 9, "raise_fee_10": 4},
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
    """Return a deterministic AutoGovNEXT policy candidate.

    AutoGovNEXT expands the candidate vocabulary and observation bins used to
    order governance proposals. It still uses the same frozen policy schema and
    concrete governance gates as the existing surface policy.
    """

    policy = copy.deepcopy(sample_autonomous_governance_surface_q_policy_v1())
    policy.pop("policy_hash", None)
    policy["policy_id"] = "sample_autogovnext_governance_surface_q_policy_v1"
    policy["version"] = 2
    policy["safety"] = {
        **dict(policy["safety"]),
        "min_oracle_confidence_bps": 7_000,
        "max_liquidity_concentration_bps": 9_500,
        "max_recent_governance_churn_bps": 8,
        "min_proof_market_health_bps": 1_000,
        "max_validator_stress_bps": 8_000,
        "max_network_stress_bps": 8_000,
    }
    policy["selection"] = {
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
    policy["state_bins"] = {
        **dict(policy["state_bins"]),
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
    policy["actions"] = [
        *list(policy["actions"]),
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
    policy["q_layers"] = [
        *list(policy["q_layers"]),
        {
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
        },
        {
            "id": "autogovnext_proof_market_router_rebalance_v1",
            "features": ["proof_market_health_bps", "reserve_bps", "hosts_bps"],
            "q_table": {
                "*": {},
                "0|4|0": {
                    "shift_router_reserve_to_hosts_100": 140,
                    "hold": -20,
                },
                "1|4|0": {
                    "shift_router_reserve_to_hosts_100": 120,
                    "hold": -10,
                },
                "4|4|0": {
                    "shift_router_reserve_to_buyburn_100": 90,
                    "hold": 10,
                },
                "4|1|3": {
                    "shift_router_hosts_to_reserve_100": 70,
                    "hold": 10,
                },
            },
        },
        {
            "id": "autogovnext_concentration_reserve_bias_v1",
            "features": ["liquidity_concentration_bps", "liquidity_depth_bps"],
            "q_table": {
                "*": {},
                "3|0": {"shift_router_to_reserve_100": 80, "hold": -10},
                "4|0": {"shift_router_to_reserve_100": 100, "hold": -20},
            },
        },
        {
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
        },
    ]
    return {**policy, "policy_hash": policy_content_hash_v1(policy)}


def evaluate_autonomous_governance_surface_q_policy_v1(
    *,
    policy: Mapping[str, Any],
    surface_state: Mapping[str, Any],
    observation: Mapping[str, Any],
    current_epoch: int,
    proposal_epoch: int,
    last_update_epoch: int | None = None,
    expected_policy_hash: str | None = None,
    expected_committed_context_hash: str | None = None,
    previous_approved_deltas: Mapping[str, Any] | None = None,
    trajectory_budget: Mapping[str, Any] | None = None,
    trajectory_used: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Evaluate a Q-table action against the concrete governance PR gate suite.

    This is the fully autonomous path for the new governance surfaces: the table
    proposes, and the verified Python/Tau governance gates decide admissibility.
    """

    errors: list[str] = []
    normalized_policy, policy_errors = _normalize_policy(
        policy, parameter_names=SURFACE_PARAMETER_NAMES_V1
    )
    errors.extend(policy_errors)

    policy_hash = _policy_content_hash_for_receipt(policy, errors)
    if expected_policy_hash is not None and expected_policy_hash != policy_hash:
        errors.append("policy_hash_mismatch")

    state, state_errors = _normalize_surface_state(surface_state)
    errors.extend(state_errors)

    obs, obs_errors = _normalize_observation(observation)
    errors.extend(obs_errors)
    normalized_trajectory_budget, trajectory_budget_errors = _normalize_trajectory_budget(
        trajectory_budget,
        policy=normalized_policy,
    )
    errors.extend(trajectory_budget_errors)
    normalized_trajectory_used, trajectory_used_errors = _normalize_trajectory_used(trajectory_used)
    errors.extend(trajectory_used_errors)

    normalized_current_epoch = _require_nonnegative_int_or_error(
        current_epoch, name="current_epoch", errors=errors
    )
    normalized_proposal_epoch = _require_nonnegative_int_or_error(
        proposal_epoch, name="proposal_epoch", errors=errors
    )
    normalized_last_update_epoch = _normalize_optional_nonnegative_int(
        last_update_epoch,
        name="last_update_epoch",
        errors=errors,
    )
    normalized_previous_deltas, previous_delta_errors = _normalize_previous_approved_deltas(
        previous_approved_deltas
    )
    errors.extend(previous_delta_errors)
    committed_context = _surface_context_payload(
        state=state,
        current_epoch=normalized_current_epoch,
        proposal_epoch=normalized_proposal_epoch,
        last_update_epoch=normalized_last_update_epoch,
        previous_approved_deltas=normalized_previous_deltas,
        trajectory_used=normalized_trajectory_used,
    )
    committed_context_hash = _surface_context_hash(committed_context)
    if (
        expected_committed_context_hash is not None
        and expected_committed_context_hash != committed_context_hash
    ):
        errors.append("committed_context_hash_mismatch")
    safety_errors = _safety_errors(
        normalized_policy,
        obs,
        current_epoch=normalized_current_epoch,
        last_update_epoch=normalized_last_update_epoch,
    )
    errors.extend(safety_errors)

    action_id = ""
    scores: dict[str, int] = {}
    state_bins: dict[str, int] = {}
    selected_action: dict[str, Any] = {"id": "", "deltas": {}}
    candidate_search: dict[str, Any] = {
        "mode": "top_scored",
        "checked_count": 0,
        "fallback_used": False,
        "rejected_candidates": (),
    }
    if normalized_policy and obs:
        action_id, selected_action, scores, state_bins, selection_errors = _select_action(
            normalized_policy, {**obs, **state}
        )
        errors.extend(selection_errors)

    first_admissible_mode = (
        normalized_policy
        and obs
        and state
        and normalized_policy.get("selection", {}).get("mode") == "first_admissible"
    )
    if first_admissible_mode:
        candidate_search = _select_first_admissible_surface_action(
            policy=normalized_policy,
            state=state,
            scores=scores,
            top_action_id=action_id,
            proposal_epoch=normalized_proposal_epoch,
            current_epoch=normalized_current_epoch,
            existing_errors=errors,
            previous_approved_deltas=normalized_previous_deltas,
            trajectory_budget=normalized_trajectory_budget,
            trajectory_used=normalized_trajectory_used,
        )
        selected_candidate = candidate_search.get("selected_candidate", {})
        if isinstance(selected_candidate, Mapping):
            action_id = str(selected_candidate.get("action_id", action_id))
            selected_action = dict(selected_candidate.get("action", selected_action))
            selected_proposed = selected_candidate.get("proposed", {})
            proposed = dict(selected_proposed) if isinstance(selected_proposed, Mapping) else _propose_surface_state(
                state,
                selected_action,
            )
            selected_gate_report = selected_candidate.get("gate_report", {})
            surface_report = (
                dict(selected_gate_report)
                if isinstance(selected_gate_report, Mapping)
                else _governance_surface_gate_report(
                    current=state,
                    proposed=proposed,
                    proposal_epoch=normalized_proposal_epoch,
                    current_epoch=normalized_current_epoch,
                )
            )
        else:
            proposed = _propose_surface_state(state, selected_action)
            surface_report = _governance_surface_gate_report(
                current=state,
                proposed=proposed,
                proposal_epoch=normalized_proposal_epoch,
                current_epoch=normalized_current_epoch,
            )
    else:
        proposed = _propose_surface_state(state, selected_action)
        surface_report = _governance_surface_gate_report(
            current=state,
            proposed=proposed,
            proposal_epoch=normalized_proposal_epoch,
            current_epoch=normalized_current_epoch,
        )
    trajectory_failures = _trajectory_budget_failures(
        action=selected_action,
        trajectory_budget=normalized_trajectory_budget,
        trajectory_used=normalized_trajectory_used,
    )
    errors.extend(trajectory_failures)
    for name, accepted in surface_report.items():
        if not accepted:
            errors.append(f"governance_surface_gate_rejected:{name}")
    all_gates_ok = all(surface_report.values())

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_Q_RECEIPT_SCHEMA_V1,
        "policy_hash": policy_hash,
        "action_id": action_id,
        "state_bins": state_bins,
        "scores": scores,
        "candidate_search": candidate_search,
        "committed_context": committed_context,
        "committed_context_hash": committed_context_hash,
        "expected_committed_context_hash": expected_committed_context_hash or "",
        "previous_approved_deltas": normalized_previous_deltas,
        "trajectory_budget": normalized_trajectory_budget,
        "trajectory_used": normalized_trajectory_used,
        "observation": obs,
        "surface_state": state,
        "proposed": proposed,
        "governance_surface_gate_report": surface_report,
        "governance_surface_all_gates_ok": all_gates_ok,
        "revision_policy": "governance_pointwise_revision_v1",
        "approved": not errors,
        "ok": not errors,
        "errors": tuple(errors),
        "not_claimed": (
            "does_not_authorize_settlement",
            "does_not_change_immutable_rules",
            "does_not_claim_oracle_truth",
            "does_not_train_q_table_online",
        ),
    }
    return {**body, "receipt_hash": hash_v0("autonomous_governance_q_surface_receipt_v1", body)}


def commit_autonomous_governance_surface_q_policy_v1(
    *,
    policy: Mapping[str, Any],
    surface_state: Mapping[str, Any],
    observation: Mapping[str, Any],
    current_epoch: int,
    proposal_epoch: int,
    last_update_epoch: int | None = None,
    expected_policy_hash: str | None = None,
    expected_committed_context_hash: str | None = None,
    previous_approved_deltas: Mapping[str, Any] | None = None,
    trajectory_budget: Mapping[str, Any] | None = None,
    trajectory_used: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Evaluate and apply one autonomous governance-surface step.

    The Q policy remains advisory. This function binds the current values to
    `surface_state`, asks the policy for a candidate, recomputes the concrete
    governance gates against that committed state, and applies the proposed
    state only when the receipt and the gate recheck both approve. Rejection is
    a deterministic no-op.
    """

    receipt = evaluate_autonomous_governance_surface_q_policy_v1(
        policy=policy,
        surface_state=surface_state,
        observation=observation,
        current_epoch=current_epoch,
        proposal_epoch=proposal_epoch,
        last_update_epoch=last_update_epoch,
        expected_policy_hash=expected_policy_hash,
        expected_committed_context_hash=expected_committed_context_hash,
        previous_approved_deltas=previous_approved_deltas,
        trajectory_budget=trajectory_budget,
        trajectory_used=trajectory_used,
    )
    committed, committed_errors = _normalize_surface_state(surface_state)
    proposed_raw = receipt.get("proposed", {})
    proposed_input = proposed_raw if isinstance(proposed_raw, Mapping) else {}
    proposed, proposed_errors = _normalize_surface_state(proposed_input)

    gate_recheck = _governance_surface_gate_report(
        current=committed,
        proposed=proposed,
        proposal_epoch=proposal_epoch if isinstance(proposal_epoch, int) and not isinstance(proposal_epoch, bool) else 0,
        current_epoch=current_epoch if isinstance(current_epoch, int) and not isinstance(current_epoch, bool) else 0,
    )

    commit_errors: list[str] = []
    commit_errors.extend(f"committed_{error}" for error in committed_errors)
    commit_errors.extend(f"proposed_{error}" for error in proposed_errors)
    if receipt.get("approved") is True and not all(gate_recheck.values()):
        commit_errors.append("gate_recheck_rejected")

    admitted = (
        receipt.get("ok") is True
        and receipt.get("approved") is True
        and not commit_errors
        and all(gate_recheck.values())
    )
    if admitted:
        reason = "admitted"
        applied_state = proposed
    elif receipt.get("approved") is not True:
        reason = "receipt_rejected_noop"
        applied_state = committed
    elif commit_errors:
        reason = "commit_rejected_noop"
        applied_state = committed
    else:
        reason = "gate_recheck_rejected_noop"
        applied_state = committed
    trajectory_used_after = _advance_trajectory_used_after_step(
        admitted=admitted,
        committed=committed,
        applied=applied_state,
        trajectory_used=trajectory_used,
    )

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SURFACE_STEP_SCHEMA_V1,
        "receipt": receipt,
        "receipt_hash": receipt.get("receipt_hash", ""),
        "committed_state": committed,
        "proposed_state": proposed,
        "applied_state": applied_state,
        "gate_recheck": gate_recheck,
        "admitted": admitted,
        "reason": reason,
        "trajectory_used_after": trajectory_used_after,
        "ok": not commit_errors,
        "errors": tuple(commit_errors),
        "not_claimed": (
            "does_not_authorize_settlement",
            "does_not_change_immutable_rules",
            "does_not_claim_oracle_truth",
            "does_not_train_q_table_online",
        ),
    }
    return {**body, "step_hash": hash_v0("autonomous_governance_q_surface_step_v1", body)}


def admit_autonomous_governance_surface_request_v1(request: Mapping[str, Any]) -> dict[str, Any]:
    """Fail closed at the live autonomous-governance request boundary.

    The caller supplies committed state, observations, timing, a frozen policy,
    and a pinned policy hash. Proposed states, receipts, action IDs, and other
    result fields are recomputed here and are rejected if supplied by the
    caller.
    """

    request_is_mapping = isinstance(request, Mapping)
    request_obj = request if request_is_mapping else {}
    raw_state = request_obj.get("surface_state", {})
    committed, committed_errors = _normalize_surface_state(
        raw_state if isinstance(raw_state, Mapping) else {}
    )
    errors: list[str] = []
    if not request_is_mapping:
        errors.append("request_must_be_object")
    schema = request_obj.get("schema")
    if schema is not None and schema not in {
        AUTONOMOUS_GOVERNANCE_SURFACE_ADMISSION_SCHEMA_V1,
        AUTONOMOUS_GOVERNANCE_SURFACE_EVAL_BUNDLE_SCHEMA_V1,
    }:
        errors.append("admission_schema_invalid")
    errors.extend(f"committed_{error}" for error in committed_errors)

    unknown_fields = tuple(
        sorted(
            safe_field_label(field)
            for field in request_obj
            if field not in ALLOWED_SURFACE_ADMISSION_REQUEST_FIELDS_V1
            and field not in FORBIDDEN_SURFACE_ADMISSION_RESULT_FIELDS_V1
        )
    )
    forbidden_fields = tuple(
        sorted(str(field) for field in FORBIDDEN_SURFACE_ADMISSION_RESULT_FIELDS_V1 if field in request_obj)
    )
    errors.extend(f"unknown_admission_request_field:{field}" for field in unknown_fields)
    errors.extend(f"direct_result_field_forbidden:{field}" for field in forbidden_fields)

    tx_id = request_obj.get("tx_id")
    if tx_id is not None:
        if not isinstance(tx_id, str) or not tx_id.strip() or len(tx_id) > 128:
            errors.append("tx_id_invalid")
        elif any(ord(ch) < 32 for ch in tx_id):
            errors.append("tx_id_invalid")
    time_ms = request_obj.get("time_ms")
    if time_ms is not None:
        try:
            _require_nonnegative_int(time_ms, name="time_ms")
        except ValueError as exc:
            errors.append(str(exc))

    expected_policy_hash = request_obj.get("expected_policy_hash")
    if not _is_canonical_hash_v0(expected_policy_hash):
        errors.append("expected_policy_hash_invalid")
    expected_committed_context_hash = request_obj.get("expected_committed_context_hash")
    if (
        expected_committed_context_hash is not None
        and not _is_canonical_hash_v0(expected_committed_context_hash)
    ):
        errors.append("expected_committed_context_hash_invalid")

    if errors:
        return _surface_admission_rejection(
            committed=committed,
            request_obj=request_obj,
            errors=errors,
            unknown_fields=unknown_fields,
            forbidden_fields=forbidden_fields,
        )

    step = commit_autonomous_governance_surface_q_policy_v1(
        policy=request_obj.get("policy", {}),
        surface_state=request_obj.get("surface_state", {}),
        observation=request_obj.get("observation", {}),
        current_epoch=request_obj.get("current_epoch"),
        proposal_epoch=request_obj.get("proposal_epoch"),
        last_update_epoch=request_obj.get("last_update_epoch"),
        expected_policy_hash=str(expected_policy_hash),
        expected_committed_context_hash=(
            str(expected_committed_context_hash)
            if isinstance(expected_committed_context_hash, str)
            else None
        ),
        previous_approved_deltas=request_obj.get("previous_approved_deltas"),
        trajectory_budget=request_obj.get("trajectory_budget"),
        trajectory_used=request_obj.get("trajectory_used"),
    )
    admitted = step.get("admitted") is True
    receipt = step.get("receipt", {})
    step_errors = tuple(str(error) for error in step.get("errors", ()))
    receipt_errors = (
        tuple(str(error) for error in receipt.get("errors", ()))
        if isinstance(receipt, Mapping)
        else ()
    )
    admission_errors = step_errors if admitted else step_errors + receipt_errors
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SURFACE_ADMISSION_SCHEMA_V1,
        "tx_id": tx_id if isinstance(tx_id, str) else "",
        "time_ms": time_ms if type(time_ms) is int else None,
        "step": step,
        "receipt": receipt,
        "receipt_hash": step.get("receipt_hash", ""),
        "step_hash": step.get("step_hash", ""),
        "committed_state": step.get("committed_state", committed),
        "proposed_state": step.get("proposed_state", committed),
        "applied_state": step.get("applied_state", committed),
        "gate_recheck": step.get("gate_recheck", {}),
        "trajectory_used_after": step.get("trajectory_used_after", {}),
        "admitted": admitted,
        "reason": step.get("reason", "commit_rejected_noop"),
        "ok": step.get("ok") is True and admitted,
        "errors": admission_errors,
        "unknown_fields": (),
        "forbidden_fields": (),
        "not_claimed": (
            "does_not_authorize_settlement",
            "does_not_change_immutable_rules",
            "does_not_claim_oracle_truth",
            "does_not_train_q_table_online",
        ),
    }
    return {**body, "admission_hash": hash_v0("autonomous_governance_q_surface_admission_v1", body)}


def _surface_admission_rejection(
    *,
    committed: Mapping[str, int],
    request_obj: Mapping[str, Any],
    errors: Sequence[str],
    unknown_fields: Sequence[str],
    forbidden_fields: Sequence[str],
) -> dict[str, Any]:
    trajectory_used_after, _trajectory_errors = _normalize_trajectory_used(
        request_obj.get("trajectory_used")
    )
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_SURFACE_ADMISSION_SCHEMA_V1,
        "tx_id": request_obj.get("tx_id") if isinstance(request_obj.get("tx_id"), str) else "",
        "time_ms": request_obj.get("time_ms") if type(request_obj.get("time_ms")) is int else None,
        "step": {},
        "receipt": {},
        "receipt_hash": "",
        "step_hash": "",
        "committed_state": dict(committed),
        "proposed_state": dict(committed),
        "applied_state": dict(committed),
        "gate_recheck": {},
        "trajectory_used_after": trajectory_used_after,
        "admitted": False,
        "reason": "admission_rejected_noop",
        "ok": False,
        "errors": tuple(errors),
        "unknown_fields": tuple(unknown_fields),
        "forbidden_fields": tuple(forbidden_fields),
        "not_claimed": (
            "does_not_authorize_settlement",
            "does_not_change_immutable_rules",
            "does_not_claim_oracle_truth",
            "does_not_train_q_table_online",
        ),
    }
    return {**body, "admission_hash": hash_v0("autonomous_governance_q_surface_admission_v1", body)}


def _advance_trajectory_used_after_step(
    *,
    admitted: bool,
    committed: Mapping[str, int],
    applied: Mapping[str, int],
    trajectory_used: Mapping[str, Any] | None,
) -> dict[str, int]:
    used, _errors = _normalize_trajectory_used(trajectory_used)
    out = dict(used)
    if not admitted:
        return out
    for name in SURFACE_PARAMETER_NAMES_V1:
        if name not in committed or name not in applied:
            continue
        delta = abs(int(applied[name]) - int(committed[name]))
        if delta:
            out[name] = int(out.get(name, 0)) + delta
    return out


def _select_first_admissible_surface_action(
    *,
    policy: Mapping[str, Any],
    state: Mapping[str, int],
    scores: Mapping[str, int],
    top_action_id: str,
    proposal_epoch: int,
    current_epoch: int,
    existing_errors: Sequence[str],
    previous_approved_deltas: Mapping[str, Any] | None,
    trajectory_budget: Mapping[str, int],
    trajectory_used: Mapping[str, int],
) -> dict[str, Any]:
    actions = list(policy.get("actions", ()))
    action_by_id = {str(action.get("id", "")): dict(action) for action in actions if isinstance(action, Mapping)}

    def build_candidate(action_id: str) -> dict[str, Any]:
        action = action_by_id.get(action_id, {"id": action_id, "deltas": {}})
        proposed = _propose_surface_state(state, action)
        return {
            "action_id": action_id,
            "action": action,
            "proposed": proposed,
            "gate_report": _governance_surface_gate_report(
                current=state,
                proposed=proposed,
                proposal_epoch=proposal_epoch,
                current_epoch=current_epoch,
            ),
        }

    if existing_errors:
        return {
            "mode": "first_admissible",
            "checked_count": 0,
            "gate_checked_count": 0,
            "selection_screened_count": 0,
            "selection_penalized_count": 0,
            "candidate_considered_count": 0,
            "fallback_used": False,
            "raw_top_action_id": top_action_id,
            "selection_adjusted_top_action_id": top_action_id,
            "raw_top_action_selection_screened": False,
            "disabled_by_existing_errors": tuple(existing_errors),
            "rejected_candidates": (),
            "selection_screened_candidates": (),
            "selection_penalized_candidates": (),
            "selected_candidate": build_candidate(top_action_id),
        }

    rejected_candidates: list[dict[str, Any]] = []
    selection_screened_candidates: list[dict[str, Any]] = []
    gate_checked_count = 0
    selection_adjusted_top_action_id = ""
    normalized_previous_deltas = _normalize_delta_history(previous_approved_deltas)

    raw_ranked_action_ids = _ranked_action_ids(actions, scores)
    selection_failures_by_action: dict[str, tuple[str, ...]] = {}
    for action_id in raw_ranked_action_ids:
        action = action_by_id[action_id]
        selection_failures = _anti_oscillation_failures(
            policy=policy,
            action=action,
            previous_approved_deltas=normalized_previous_deltas,
        ) + _trajectory_budget_failures(
            action=action,
            trajectory_budget=trajectory_budget,
            trajectory_used=trajectory_used,
        )
        if selection_failures:
            selection_failures_by_action[action_id] = selection_failures

    def score_with_selection_penalty(action_id: str) -> int:
        raw_score = scores.get(action_id, 0)
        score = int(raw_score) if isinstance(raw_score, int) and not isinstance(raw_score, bool) else 0
        if action_id in selection_failures_by_action:
            return score - SELECTION_BLOCKER_SCORE_PENALTY
        return score

    selection_adjusted_scores = {
        str(action.get("id", "")): score_with_selection_penalty(str(action.get("id", "")))
        for action in actions
        if isinstance(action, Mapping)
    }
    selection_adjusted_ranked_action_ids = _ranked_action_ids(actions, selection_adjusted_scores)

    for action_id in selection_adjusted_ranked_action_ids:
        action = action_by_id[action_id]
        selection_failures = selection_failures_by_action.get(action_id, ())
        if selection_failures:
            rejected = {
                "action_id": action_id,
                "failed_selection": selection_failures,
            }
            rejected_candidates.append(rejected)
            selection_screened_candidates.append(rejected)
            continue
        if not selection_adjusted_top_action_id:
            selection_adjusted_top_action_id = action_id
        proposed = _propose_surface_state(state, action)
        gate_report = _governance_surface_gate_report(
            current=state,
            proposed=proposed,
            proposal_epoch=proposal_epoch,
            current_epoch=current_epoch,
        )
        gate_checked_count += 1
        failed_gates = tuple(name for name, accepted in gate_report.items() if accepted is not True)
        if not failed_gates:
            selection_screened_count = len(selection_screened_candidates)
            selected_raw_rank = raw_ranked_action_ids.index(action_id) if action_id in raw_ranked_action_ids else len(raw_ranked_action_ids)
            selection_penalized_candidates = tuple(
                {
                    "action_id": ranked_action_id,
                    "failed_selection": selection_failures_by_action[ranked_action_id],
                }
                for ranked_action_id in raw_ranked_action_ids[:selected_raw_rank]
                if ranked_action_id in selection_failures_by_action
            )
            return {
                "mode": "first_admissible",
                "checked_count": gate_checked_count,
                "gate_checked_count": gate_checked_count,
                "selection_screened_count": selection_screened_count,
                "selection_penalized_count": len(selection_penalized_candidates),
                "candidate_considered_count": selection_screened_count + gate_checked_count,
                "fallback_used": action_id != selection_adjusted_top_action_id,
                "raw_top_action_id": top_action_id,
                "selection_adjusted_top_action_id": selection_adjusted_top_action_id,
                "raw_top_action_selection_screened": top_action_id != selection_adjusted_top_action_id,
                "rejected_candidates": tuple(rejected_candidates),
                "selection_screened_candidates": tuple(selection_screened_candidates),
                "selection_penalized_candidates": selection_penalized_candidates,
                "selected_candidate": {
                    "action_id": action_id,
                    "action": action,
                    "proposed": proposed,
                    "gate_report": gate_report,
                },
            }
        rejected_candidates.append(
            {
                "action_id": action_id,
                "failed_gates": failed_gates,
            }
        )

    selection_screened_count = len(selection_screened_candidates)
    selection_penalized_candidates = tuple(
        {
            "action_id": ranked_action_id,
            "failed_selection": selection_failures_by_action[ranked_action_id],
        }
        for ranked_action_id in raw_ranked_action_ids
        if ranked_action_id in selection_failures_by_action
    )
    return {
        "mode": "first_admissible",
        "checked_count": gate_checked_count,
        "gate_checked_count": gate_checked_count,
        "selection_screened_count": selection_screened_count,
        "selection_penalized_count": len(selection_penalized_candidates),
        "candidate_considered_count": selection_screened_count + gate_checked_count,
        "fallback_used": False,
        "raw_top_action_id": top_action_id,
        "selection_adjusted_top_action_id": selection_adjusted_top_action_id or top_action_id,
        "raw_top_action_selection_screened": bool(
            selection_adjusted_top_action_id and top_action_id != selection_adjusted_top_action_id
        ),
        "rejected_candidates": tuple(rejected_candidates),
        "selection_screened_candidates": tuple(selection_screened_candidates),
        "selection_penalized_candidates": selection_penalized_candidates,
        "selected_candidate": build_candidate(top_action_id),
    }


def _normalize_delta_history(raw: Mapping[str, Any] | None) -> dict[str, int]:
    if not isinstance(raw, Mapping):
        return {}
    out: dict[str, int] = {}
    for key, value in raw.items():
        if key not in SURFACE_PARAMETER_NAMES_V1:
            continue
        if type(value) is int:
            out[str(key)] = int(value)
    return out


def _normalize_previous_approved_deltas(
    raw: Mapping[str, Any] | None,
) -> tuple[dict[str, int], list[str]]:
    if raw is None:
        return {}, []
    if not isinstance(raw, Mapping):
        return {}, ["previous_approved_deltas_must_be_object"]
    errors: list[str] = []
    out: dict[str, int] = {}
    for key, value in raw.items():
        if key not in SURFACE_PARAMETER_NAMES_V1:
            errors.append(f"unknown_previous_approved_delta_parameter:{key}")
            continue
        if type(value) is not int:
            errors.append(f"previous_approved_deltas.{key} must be an int")
            continue
        out[str(key)] = int(value)
    return out, errors


def _anti_oscillation_failures(
    *,
    policy: Mapping[str, Any],
    action: Mapping[str, Any],
    previous_approved_deltas: Mapping[str, int],
) -> tuple[str, ...]:
    selection = policy.get("selection", {})
    if not isinstance(selection, Mapping):
        return ()
    anti = selection.get("anti_oscillation", {})
    if not isinstance(anti, Mapping) or anti.get("enabled") is not True:
        return ()
    parameters = anti.get("parameters", ())
    if not isinstance(parameters, Sequence) or isinstance(parameters, (str, bytes, bytearray)):
        return ()
    deltas = action.get("deltas", {})
    if not isinstance(deltas, Mapping):
        return ()
    failures: list[str] = []
    for name in parameters:
        if name not in SURFACE_PARAMETER_NAMES_V1:
            continue
        previous_direction = _direction(int(previous_approved_deltas.get(str(name), 0)))
        candidate_direction = _direction(int(deltas.get(str(name), 0)))
        if previous_direction != 0 and candidate_direction != 0 and candidate_direction != previous_direction:
            failures.append(f"anti_oscillation:{name}")
    return tuple(failures)


def _trajectory_budget_failures(
    *,
    action: Mapping[str, Any],
    trajectory_budget: Mapping[str, int],
    trajectory_used: Mapping[str, int],
) -> tuple[str, ...]:
    if not trajectory_budget:
        return ()
    deltas = action.get("deltas", {})
    if not isinstance(deltas, Mapping):
        return ()
    failures: list[str] = []
    for name, limit in trajectory_budget.items():
        delta = deltas.get(name, 0)
        if type(delta) is not int:
            continue
        used = trajectory_used.get(name, 0)
        if type(used) is not int:
            used = 0
        if used + abs(delta) > int(limit):
            failures.append(f"trajectory_budget_exceeded:{name}")
    return tuple(failures)


def _direction(value: int) -> int:
    if value < 0:
        return -1
    if value > 0:
        return 1
    return 0


def _require_int(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise ValueError(f"{name} must be an int")
    return int(value)


def _require_nonnegative_int(value: object, *, name: str) -> int:
    value = _require_int(value, name=name)
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    return value


def _require_nonnegative_int_or_error(value: object, *, name: str, errors: list[str]) -> int:
    try:
        return _require_nonnegative_int(value, name=name)
    except ValueError as exc:
        errors.append(str(exc))
        return 0


def _normalize_optional_nonnegative_int(
    value: object,
    *,
    name: str,
    errors: list[str],
) -> int | None:
    if value is None:
        return None
    try:
        return _require_nonnegative_int(value, name=name)
    except ValueError as exc:
        errors.append(str(exc))
        return None


def _surface_context_payload(
    *,
    state: Mapping[str, int],
    current_epoch: int,
    proposal_epoch: int,
    last_update_epoch: int | None,
    previous_approved_deltas: Mapping[str, int],
    trajectory_used: Mapping[str, int],
) -> dict[str, Any]:
    return {
        "schema": AUTONOMOUS_GOVERNANCE_SURFACE_CONTEXT_SCHEMA_V1,
        "surface_state": {
            name: int(state[name])
            for name in SURFACE_PARAMETER_NAMES_V1
            if name in state
        },
        "current_epoch": int(current_epoch),
        "proposal_epoch": int(proposal_epoch),
        "last_update_epoch": last_update_epoch,
        "previous_approved_deltas": {
            name: int(previous_approved_deltas[name])
            for name in sorted(previous_approved_deltas)
            if name in SURFACE_PARAMETER_NAMES_V1
        },
        "trajectory_used": {
            name: int(trajectory_used[name])
            for name in sorted(trajectory_used)
            if name in SURFACE_PARAMETER_NAMES_V1
        },
    }


def _surface_context_hash(context: Mapping[str, Any]) -> str:
    return hash_v0("autonomous_governance_surface_context_v1", context)


def _normalize_policy(
    policy: Mapping[str, Any],
    *,
    parameter_names: Sequence[str] = PARAMETER_NAMES_V1,
) -> tuple[dict[str, Any], list[str]]:
    errors: list[str] = []
    if not isinstance(policy, Mapping):
        return {}, ["policy_must_be_object"]
    allowed = {
        "schema",
        "policy_id",
        "version",
        "safety",
        "state_bins",
        "actions",
        "q_layers",
        "selection",
        "policy_hash",
    }
    for key in policy:
        if key not in allowed:
            errors.append(f"unknown_policy_field:{key}")
    if policy.get("schema") != AUTONOMOUS_GOVERNANCE_Q_POLICY_SCHEMA_V1:
        errors.append("policy_schema_invalid")
    if not isinstance(policy.get("policy_id"), str) or not policy.get("policy_id"):
        errors.append("policy_id_invalid")
    normalized_version = 0
    try:
        normalized_version = _require_nonnegative_int(policy.get("version"), name="version")
        if normalized_version < 1:
            errors.append("version_invalid")
    except ValueError as exc:
        errors.append(str(exc))

    safety = policy.get("safety", {})
    if not isinstance(safety, Mapping):
        errors.append("safety_must_be_object")
        safety = {}

    selection_raw = policy.get("selection", {})
    if not isinstance(selection_raw, Mapping):
        errors.append("selection_must_be_object")
        selection_raw = {}
    selection_mode = str(selection_raw.get("mode", "top_scored"))
    if selection_mode not in {"top_scored", "first_admissible"}:
        errors.append(f"selection_mode_invalid:{selection_mode}")
        selection_mode = "top_scored"
    normalized_selection: dict[str, Any] = {"mode": selection_mode}
    anti_raw = selection_raw.get("anti_oscillation", {})
    if anti_raw:
        if not isinstance(anti_raw, Mapping):
            errors.append("anti_oscillation_must_be_object")
        else:
            enabled = anti_raw.get("enabled", False)
            if not isinstance(enabled, bool):
                errors.append("anti_oscillation_enabled_must_be_bool")
                enabled = False
            parameters_raw = anti_raw.get("parameters", ())
            parameters: list[str] = []
            if not isinstance(parameters_raw, Sequence) or isinstance(
                parameters_raw, (str, bytes, bytearray)
            ):
                errors.append("anti_oscillation_parameters_must_be_sequence")
            else:
                for parameter in parameters_raw:
                    if not isinstance(parameter, str):
                        errors.append(f"anti_oscillation_parameter_invalid:{parameter}")
                    elif parameter in AUTOGOVNEXT_FORBIDDEN_AUTHORITY_PARAMETERS_V1:
                        errors.append(f"authority_anti_oscillation_parameter_forbidden:{parameter}")
                    elif parameter not in parameter_names:
                        errors.append(f"anti_oscillation_unknown_parameter:{parameter}")
                    else:
                        parameters.append(parameter)
            normalized_selection["anti_oscillation"] = {
                "enabled": bool(enabled),
                "parameters": parameters,
            }
    trajectory_raw = selection_raw.get("trajectory_budget", {})
    if trajectory_raw:
        if not isinstance(trajectory_raw, Mapping):
            errors.append("trajectory_budget_must_be_object")
        else:
            enabled = trajectory_raw.get("enabled", False)
            if not isinstance(enabled, bool):
                errors.append("trajectory_budget_enabled_must_be_bool")
                enabled = False
            limits_raw = trajectory_raw.get("limits", {})
            limits: dict[str, int] = {}
            if not isinstance(limits_raw, Mapping):
                errors.append("trajectory_budget_limits_must_be_object")
            else:
                for parameter, raw_limit in limits_raw.items():
                    if parameter in AUTOGOVNEXT_FORBIDDEN_AUTHORITY_PARAMETERS_V1:
                        errors.append(f"authority_trajectory_budget_parameter_forbidden:{parameter}")
                        continue
                    if parameter not in parameter_names:
                        errors.append(f"trajectory_budget_unknown_parameter:{parameter}")
                        continue
                    try:
                        limits[str(parameter)] = _require_nonnegative_int(
                            raw_limit,
                            name=f"trajectory_budget.{parameter}",
                        )
                    except ValueError as exc:
                        errors.append(str(exc))
            normalized_selection["trajectory_budget"] = {
                "enabled": bool(enabled),
                "limits": limits,
            }

    state_bins = policy.get("state_bins", {})
    normalized_bins: dict[str, list[int]] = {}
    allowed_bin_fields = set(OBSERVATION_FIELDS_V1).union(str(name) for name in parameter_names)
    if not isinstance(state_bins, Mapping):
        errors.append("state_bins_must_be_object")
    else:
        for field, raw_thresholds in state_bins.items():
            if field in AUTOGOVNEXT_FORBIDDEN_AUTHORITY_PARAMETERS_V1:
                errors.append(f"authority_state_bin_forbidden:{field}")
                continue
            if field not in allowed_bin_fields:
                errors.append(f"unknown_state_bin_field:{field}")
                continue
            if not isinstance(raw_thresholds, Sequence) or isinstance(raw_thresholds, (str, bytes, bytearray)):
                errors.append(f"state_bin_thresholds_invalid:{field}")
                continue
            thresholds: list[int] = []
            for index, raw in enumerate(raw_thresholds):
                try:
                    thresholds.append(_require_nonnegative_int(raw, name=f"state_bins.{field}[{index}]"))
                except ValueError as exc:
                    errors.append(str(exc))
            if thresholds != sorted(thresholds):
                errors.append(f"state_bin_thresholds_not_sorted:{field}")
            normalized_bins[str(field)] = thresholds

    actions_raw = policy.get("actions", [])
    actions: list[dict[str, Any]] = []
    action_ids: set[str] = set()
    if not isinstance(actions_raw, Sequence) or isinstance(actions_raw, (str, bytes, bytearray)):
        errors.append("actions_must_be_sequence")
    else:
        for index, raw in enumerate(actions_raw):
            if not isinstance(raw, Mapping):
                errors.append(f"action_invalid:{index}")
                continue
            action_id = raw.get("id")
            if not isinstance(action_id, str) or not action_id:
                errors.append(f"action_id_invalid:{index}")
                continue
            if action_id in action_ids:
                errors.append(f"duplicate_action_id:{action_id}")
            action_ids.add(action_id)
            deltas_raw = raw.get("deltas", {})
            if not isinstance(deltas_raw, Mapping):
                errors.append(f"action_deltas_invalid:{action_id}")
                deltas_raw = {}
            deltas: dict[str, int] = {}
            for name, raw_delta in deltas_raw.items():
                if name in AUTOGOVNEXT_FORBIDDEN_AUTHORITY_PARAMETERS_V1:
                    errors.append(f"authority_action_delta_forbidden:{name}")
                    continue
                if name not in parameter_names:
                    errors.append(f"unknown_action_delta_parameter:{name}")
                    continue
                try:
                    deltas[str(name)] = _require_int(raw_delta, name=f"action.{action_id}.{name}")
                except ValueError as exc:
                    errors.append(str(exc))
            actions.append({"id": action_id, "deltas": deltas})
    if not actions:
        errors.append("actions_empty")

    q_layers_raw = policy.get("q_layers", [])
    q_layers: list[dict[str, Any]] = []
    if not isinstance(q_layers_raw, Sequence) or isinstance(q_layers_raw, (str, bytes, bytearray)):
        errors.append("q_layers_must_be_sequence")
    else:
        for index, raw in enumerate(q_layers_raw):
            if not isinstance(raw, Mapping):
                errors.append(f"q_layer_invalid:{index}")
                continue
            layer_id = raw.get("id")
            if not isinstance(layer_id, str) or not layer_id:
                errors.append(f"q_layer_id_invalid:{index}")
                layer_id = f"layer_{index}"
            features_raw = raw.get("features", [])
            features: list[str] = []
            if not isinstance(features_raw, Sequence) or isinstance(features_raw, (str, bytes, bytearray)):
                errors.append(f"q_layer_features_invalid:{layer_id}")
            else:
                for feature in features_raw:
                    if feature not in normalized_bins:
                        errors.append(f"q_layer_feature_not_binned:{layer_id}:{feature}")
                    else:
                        features.append(str(feature))
            table_raw = raw.get("q_table", {})
            table: dict[str, dict[str, int]] = {}
            if not isinstance(table_raw, Mapping):
                errors.append(f"q_table_invalid:{layer_id}")
            else:
                for key, row_raw in table_raw.items():
                    if not isinstance(key, str) or not key:
                        errors.append(f"q_table_key_invalid:{layer_id}")
                        continue
                    if not isinstance(row_raw, Mapping):
                        errors.append(f"q_table_row_invalid:{layer_id}:{key}")
                        continue
                    row: dict[str, int] = {}
                    for action_id, raw_score in row_raw.items():
                        if action_id not in action_ids:
                            errors.append(f"q_table_unknown_action:{layer_id}:{key}:{action_id}")
                            continue
                        try:
                            row[str(action_id)] = _require_int(raw_score, name=f"q_table.{layer_id}.{key}.{action_id}")
                        except ValueError as exc:
                            errors.append(str(exc))
                    table[str(key)] = row
            q_layers.append({"id": layer_id, "features": features, "q_table": table})
    if not q_layers:
        errors.append("q_layers_empty")

    return {
        "schema": AUTONOMOUS_GOVERNANCE_Q_POLICY_SCHEMA_V1,
        "policy_id": str(policy.get("policy_id", "")),
        "version": normalized_version,
        "safety": dict(safety),
        "selection": normalized_selection,
        "state_bins": normalized_bins,
        "actions": actions,
        "q_layers": q_layers,
    }, errors


def _normalize_parameters(
    raw: Mapping[str, Mapping[str, Any] | BoundedParameter],
) -> tuple[dict[str, BoundedParameter], list[str]]:
    errors: list[str] = []
    params: dict[str, BoundedParameter] = {}
    if not isinstance(raw, Mapping):
        return {}, ["parameters_must_be_object"]
    for name in raw:
        if name not in PARAMETER_NAMES_V1:
            errors.append(f"unknown_parameter:{name}")
    for name in PARAMETER_NAMES_V1:
        value = raw.get(name)
        if value is None:
            errors.append(f"parameter_missing:{name}")
            continue
        try:
            if isinstance(value, BoundedParameter):
                param = value
            elif isinstance(value, Mapping):
                param = BoundedParameter(
                    current=_require_nonnegative_int(value.get("current"), name=f"{name}.current"),
                    minimum=_require_nonnegative_int(value.get("minimum"), name=f"{name}.minimum"),
                    maximum=_require_nonnegative_int(value.get("maximum"), name=f"{name}.maximum"),
                    step=_require_nonnegative_int(value.get("step"), name=f"{name}.step"),
                )
            else:
                errors.append(f"parameter_invalid:{name}")
                continue
            limit = U32_MAX if name == "floor" else U16_MAX
            if param.maximum > limit:
                errors.append(f"{name}_maximum_exceeds_width")
            if param.minimum > param.maximum:
                errors.append(f"{name}_minimum_exceeds_maximum")
            if not param.minimum <= param.current <= param.maximum:
                errors.append(f"{name}_current_out_of_bounds")
            if param.step > limit:
                errors.append(f"{name}_step_exceeds_width")
            params[name] = param
        except ValueError as exc:
            errors.append(str(exc))
    return params, errors


def _normalize_surface_state(raw: Mapping[str, Any]) -> tuple[dict[str, int], list[str]]:
    errors: list[str] = []
    state: dict[str, int] = {}
    if not isinstance(raw, Mapping):
        return {}, ["surface_state_must_be_object"]
    for key in raw:
        if key not in SURFACE_PARAMETER_NAMES_V1:
            errors.append(f"unknown_surface_parameter:{key}")
    for name in SURFACE_PARAMETER_NAMES_V1:
        try:
            value = _require_nonnegative_int(raw.get(name), name=name)
            if value > U16_MAX:
                errors.append(f"{name}_exceeds_u16")
            state[name] = value
        except ValueError as exc:
            errors.append(str(exc))
    return state, errors


def _normalize_trajectory_budget(
    raw: Mapping[str, Any] | None,
    *,
    policy: Mapping[str, Any],
) -> tuple[dict[str, int], list[str]]:
    if raw is None:
        selection = policy.get("selection", {}) if isinstance(policy, Mapping) else {}
        trajectory = selection.get("trajectory_budget", {}) if isinstance(selection, Mapping) else {}
        if not isinstance(trajectory, Mapping) or trajectory.get("enabled") is not True:
            return {}, []
        raw = trajectory.get("limits", {})
    return _normalize_surface_int_map(raw, name="trajectory_budget")


def _normalize_trajectory_used(raw: Mapping[str, Any] | None) -> tuple[dict[str, int], list[str]]:
    if raw is None:
        return {}, []
    return _normalize_surface_int_map(raw, name="trajectory_used")


def _normalize_surface_int_map(raw: Mapping[str, Any], *, name: str) -> tuple[dict[str, int], list[str]]:
    errors: list[str] = []
    out: dict[str, int] = {}
    if not isinstance(raw, Mapping):
        return {}, [f"{name}_must_be_object"]
    for key, raw_value in raw.items():
        if key not in SURFACE_PARAMETER_NAMES_V1:
            errors.append(f"unknown_{name}_parameter:{key}")
            continue
        try:
            out[str(key)] = _require_nonnegative_int(raw_value, name=f"{name}.{key}")
        except ValueError as exc:
            errors.append(str(exc))
    return out, errors


def _propose_surface_state(
    state: Mapping[str, int],
    action: Mapping[str, Any],
) -> dict[str, int]:
    deltas = action.get("deltas", {}) if isinstance(action, Mapping) else {}
    if not isinstance(deltas, Mapping):
        deltas = {}
    return {name: value + int(deltas.get(name, 0)) for name, value in state.items()}


def _governance_surface_gate_report(
    *,
    current: Mapping[str, int],
    proposed: Mapping[str, int],
    proposal_epoch: int,
    current_epoch: int,
) -> dict[str, bool]:
    if any(name not in current or name not in proposed for name in SURFACE_PARAMETER_NAMES_V1):
        return {
            "fee": False,
            "router": False,
            "collateral": False,
            "whale": False,
            "funding": False,
            "master": False,
        }
    master = _GOV_MASTER_REVISION(
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
        "fee": _GOV_FEE_REVISION_OK(
            True, True, proposal_epoch, current_epoch, current["fee_bps"], proposed["fee_bps"]
        ),
        "router": _GOV_ROUTER_REVISION_OK(
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
        "collateral": _GOV_COLLATERAL_RATIO_REVISION_OK(
            True,
            True,
            proposal_epoch,
            current_epoch,
            current["mcr_bps"],
            proposed["mcr_bps"],
            current["ccr_bps"],
            proposed["ccr_bps"],
        ),
        "whale": _GOV_WHALE_DEFENSE_REVISION_OK(
            True, True, proposal_epoch, current_epoch, current["staker_bps"], proposed["staker_bps"]
        ),
        "funding": _GOV_FUNDING_RATE_REVISION_OK(
            True,
            True,
            proposal_epoch,
            current_epoch,
            current["funding_cap_bps"],
            proposed["funding_cap_bps"],
        ),
        "master": _GOV_MASTER_REVISION_OK(master),
    }


def _normalize_observation(raw: Mapping[str, Any]) -> tuple[dict[str, int], list[str]]:
    errors: list[str] = []
    if not isinstance(raw, Mapping):
        return {}, ["observation_must_be_object"]
    for key in raw:
        if key not in OBSERVATION_FIELDS_V1:
            errors.append(f"unknown_observation_field:{key}")
    obs: dict[str, int] = {}
    try:
        observed = _require_nonnegative_int(raw.get("observed_price_bps"), name="observed_price_bps")
        target = _require_nonnegative_int(raw.get("target_price_bps"), name="target_price_bps")
        obs["observed_price_bps"] = observed
        obs["target_price_bps"] = target
        obs["deviation_bps"] = abs(observed - target)
    except ValueError as exc:
        errors.append(str(exc))
    for field in ("volatility_bps", "divergence_bps", "freshness_lag_epochs", "liquidity_depth_bps"):
        try:
            obs[field] = _require_nonnegative_int(raw.get(field), name=field)
        except ValueError as exc:
            errors.append(str(exc))
    for field in (
        "oracle_confidence_bps",
        "liquidity_concentration_bps",
        "recent_governance_churn_bps",
        "proof_market_health_bps",
        "validator_stress_bps",
        "network_stress_bps",
    ):
        if field not in raw:
            continue
        try:
            obs[field] = _require_nonnegative_int(raw.get(field), name=field)
        except ValueError as exc:
            errors.append(str(exc))
    if "deviation_bps" in raw:
        try:
            explicit = _require_nonnegative_int(raw.get("deviation_bps"), name="deviation_bps")
            if "deviation_bps" in obs and explicit != obs["deviation_bps"]:
                errors.append("deviation_bps_mismatch")
        except ValueError as exc:
            errors.append(str(exc))
    return obs, errors


def _safety_errors(
    policy: Mapping[str, Any],
    observation: Mapping[str, int],
    *,
    current_epoch: int,
    last_update_epoch: int | None,
) -> list[str]:
    if not policy or not observation:
        return []
    errors: list[str] = []
    safety = policy.get("safety", {})
    if not isinstance(safety, Mapping):
        return ["safety_must_be_object"]
    if safety.get("emergency_pause") is True:
        errors.append("emergency_pause")
    _check_max(observation, safety, errors, field="freshness_lag_epochs", setting="max_freshness_lag_epochs")
    _check_max(observation, safety, errors, field="divergence_bps", setting="max_divergence_bps")
    _check_max(observation, safety, errors, field="volatility_bps", setting="max_volatility_bps")
    _check_min(observation, safety, errors, field="oracle_confidence_bps", setting="min_oracle_confidence_bps")
    _check_max(
        observation,
        safety,
        errors,
        field="liquidity_concentration_bps",
        setting="max_liquidity_concentration_bps",
    )
    _check_max(
        observation,
        safety,
        errors,
        field="recent_governance_churn_bps",
        setting="max_recent_governance_churn_bps",
    )
    _check_min(
        observation,
        safety,
        errors,
        field="proof_market_health_bps",
        setting="min_proof_market_health_bps",
    )
    _check_max(observation, safety, errors, field="validator_stress_bps", setting="max_validator_stress_bps")
    _check_max(observation, safety, errors, field="network_stress_bps", setting="max_network_stress_bps")
    try:
        min_liquidity = _require_nonnegative_int(
            safety.get("min_liquidity_depth_bps", 0), name="min_liquidity_depth_bps"
        )
        if observation.get("liquidity_depth_bps", 0) < min_liquidity:
            errors.append("liquidity_depth_below_minimum")
    except ValueError as exc:
        errors.append(str(exc))
    if last_update_epoch is not None:
        try:
            last = _require_nonnegative_int(last_update_epoch, name="last_update_epoch")
            cooldown = _require_nonnegative_int(safety.get("min_cooldown_epochs", 0), name="min_cooldown_epochs")
            if current_epoch < last + cooldown:
                errors.append("cooldown_not_elapsed")
        except ValueError as exc:
            errors.append(str(exc))
    return errors


def _check_max(
    observation: Mapping[str, int],
    safety: Mapping[str, Any],
    errors: list[str],
    *,
    field: str,
    setting: str,
) -> None:
    if setting not in safety:
        return
    try:
        maximum = _require_nonnegative_int(safety.get(setting), name=setting)
        if observation.get(field, 0) > maximum:
            errors.append(f"{field}_exceeds_{setting}")
    except ValueError as exc:
        errors.append(str(exc))


def _check_min(
    observation: Mapping[str, int],
    safety: Mapping[str, Any],
    errors: list[str],
    *,
    field: str,
    setting: str,
) -> None:
    if setting not in safety:
        return
    try:
        minimum = _require_nonnegative_int(safety.get(setting), name=setting)
        if observation.get(field, 0) < minimum:
            errors.append(f"{field}_below_{setting}")
    except ValueError as exc:
        errors.append(str(exc))


def _select_action(
    policy: Mapping[str, Any],
    observation: Mapping[str, int],
) -> tuple[str, dict[str, Any], dict[str, int], dict[str, int], list[str]]:
    errors: list[str] = []
    bins = {
        field: _bin_index(observation[field], thresholds)
        for field, thresholds in policy["state_bins"].items()
        if field in observation
    }
    actions = list(policy["actions"])
    action_by_id = {str(action["id"]): dict(action) for action in actions}
    scores = {str(action["id"]): 0 for action in actions}
    for layer in policy["q_layers"]:
        features = list(layer["features"])
        key = "|".join(str(bins[feature]) for feature in features if feature in bins)
        row = layer["q_table"].get(key)
        if row is None:
            row = layer["q_table"].get("*")
        if row is None:
            errors.append(f"q_row_missing:{layer['id']}:{key}")
            continue
        for action_id, score in row.items():
            scores[action_id] += int(score)

    selected_id = _ranked_action_ids(actions, scores)[0]
    return selected_id, action_by_id[selected_id], scores, bins, errors


def _ranked_action_ids(actions: Sequence[Mapping[str, Any]], scores: Mapping[str, int]) -> list[str]:
    ordered_ids = [str(action["id"]) for action in actions]
    order_index = {action_id: index for index, action_id in enumerate(ordered_ids)}
    return sorted(
        ordered_ids,
        key=lambda action_id: (int(scores.get(action_id, 0)), -order_index[action_id]),
        reverse=True,
    )


def _bin_index(value: int, thresholds: Sequence[int]) -> int:
    index = 0
    for threshold in thresholds:
        if value > threshold:
            index += 1
    return index


def _propose_parameters(
    params: Mapping[str, BoundedParameter],
    action: Mapping[str, Any],
) -> dict[str, int]:
    deltas = action.get("deltas", {}) if isinstance(action, Mapping) else {}
    if not isinstance(deltas, Mapping):
        deltas = {}
    proposed: dict[str, int] = {}
    for name, param in params.items():
        proposed[name] = param.current + int(deltas.get(name, 0))
    return proposed


def _revision_envelope_errors(
    params: Mapping[str, BoundedParameter],
    proposed: Mapping[str, int],
) -> list[str]:
    errors: list[str] = []
    for name, param in params.items():
        next_value = proposed.get(name)
        if next_value is None:
            errors.append(f"{name}_next_missing")
            continue
        limit = U32_MAX if name == "floor" else U16_MAX
        if not 0 <= next_value <= limit:
            errors.append(f"{name}_next_exceeds_width")
        if next_value < param.minimum or next_value > param.maximum:
            errors.append(f"{name}_next_out_of_bounds")
        if abs(next_value - param.current) > param.step:
            errors.append(f"{name}_step_exceeded")
    if "tier1" in proposed and "tier2" in proposed and proposed["tier1"] >= proposed["tier2"]:
        errors.append("tier_order_invalid")
    if all(name in proposed for name in ("weight1", "weight2", "weight3")):
        if not proposed["weight1"] <= proposed["weight2"] <= proposed["weight3"]:
            errors.append("weight_order_invalid")
    return errors


def _build_revision_step(
    *,
    params: Mapping[str, BoundedParameter],
    proposed: Mapping[str, int],
    approved: int,
    current_epoch: int,
    proposal_epoch: int,
    min_delay_epochs: int,
) -> dict[str, int]:
    def curr(name: str) -> int:
        return params[name].current

    def nxt(name: str) -> int:
        return int(proposed.get(name, params[name].current))

    def mn(name: str) -> int:
        return params[name].minimum

    def mx(name: str) -> int:
        return params[name].maximum

    def step(name: str) -> int:
        return params[name].step

    return build_revision_policy_v1_step(
        approved=approved,
        exec_req=1,
        proposal_ts=proposal_epoch,
        current_ts=current_epoch,
        min_delay=min_delay_epochs,
        fee_curr=curr("fee"),
        fee_next=nxt("fee"),
        fee_min=mn("fee"),
        fee_max=mx("fee"),
        fee_step=step("fee"),
        buyback_curr=curr("buyback"),
        buyback_next=nxt("buyback"),
        buyback_min=mn("buyback"),
        buyback_max=mx("buyback"),
        buyback_step=step("buyback"),
        rebate_curr=curr("rebate"),
        rebate_next=nxt("rebate"),
        rebate_min=mn("rebate"),
        rebate_max=mx("rebate"),
        rebate_step=step("rebate"),
        floor_curr=curr("floor"),
        floor_next=nxt("floor"),
        floor_min=mn("floor"),
        floor_max=mx("floor"),
        floor_step=step("floor"),
        unit_curr=curr("unit"),
        unit_next=nxt("unit"),
        unit_min=mn("unit"),
        unit_max=mx("unit"),
        unit_step=step("unit"),
        tier1_curr=curr("tier1"),
        tier1_next=nxt("tier1"),
        tier1_min=mn("tier1"),
        tier1_max=mx("tier1"),
        tier1_step=step("tier1"),
        tier2_curr=curr("tier2"),
        tier2_next=nxt("tier2"),
        tier2_min=mn("tier2"),
        tier2_max=mx("tier2"),
        tier2_step=step("tier2"),
        weight1_curr=curr("weight1"),
        weight1_next=nxt("weight1"),
        weight1_min=mn("weight1"),
        weight1_max=mx("weight1"),
        weight1_step=step("weight1"),
        weight2_curr=curr("weight2"),
        weight2_next=nxt("weight2"),
        weight2_min=mn("weight2"),
        weight2_max=mx("weight2"),
        weight2_step=step("weight2"),
        weight3_curr=curr("weight3"),
        weight3_next=nxt("weight3"),
        weight3_min=mn("weight3"),
        weight3_max=mx("weight3"),
        weight3_step=step("weight3"),
    )
