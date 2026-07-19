"""Frozen EBRM-policy artifact runtime for autonomous governance.

EBRM here means an energy-based reasoning model over structured governance
state. The artifact bins configured state features, uses a hash-pinned integer
energy model to score the exact bounded candidate band for one scalar
governance surface, and proposes the minimum-energy candidate. The proposal has
no authority: the exact Python/Tau governance gate for the surface decides
admissibility, and any rejection is a total no-op.

The runtime does not train online, sample probabilistically, or use energy as
an acceptance predicate. Energy orders candidates; gates authorize commits.
"""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from src.integration.autonomous_governance_q_policy import (
    OBSERVATION_FIELDS_V1,
    SURFACE_PARAMETER_NAMES_V1,
    _is_canonical_hash_v0,
    _normalize_surface_state,
    governance_surface_context_hash_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.tau_specs.governance import gov_gate, gov_proposers

AUTONOMOUS_GOVERNANCE_EBRM_POLICY_SCHEMA_V1 = (
    "zenodex.autonomous_governance.ebrm_policy.v1"
)
AUTONOMOUS_GOVERNANCE_EBRM_STEP_SCHEMA_V1 = (
    "zenodex.autonomous_governance.ebrm_surface_step.v1"
)

_EBRM_POLICY_HASH_TAG = "autonomous_governance_ebrm_policy_v1"
_EBRM_STEP_HASH_TAG = "autonomous_governance_ebrm_surface_step_v1"

_BIN_INDEX = gov_proposers.bin_index
_STATE_KEY = gov_proposers.state_key
_ENERGY_MODEL_HASH = gov_proposers.energy_model_hash
_ENERGY_PROPOSE = gov_proposers.energy_propose

_SURFACE_GUARDS = {
    "fee_bps": {
        "lo": 0,
        "hi": gov_gate.FEE_MAX_BPS,
        "step": gov_gate.FEE_STEP_BPS,
        "gate": gov_gate.fee_revision_ok,
    },
    "funding_cap_bps": {
        "lo": 0,
        "hi": gov_gate.FUNDING_CAP_MAX_BPS,
        "step": gov_gate.FUNDING_STEP_BPS,
        "gate": gov_gate.funding_rate_revision_ok,
    },
    "staker_bps": {
        "lo": 0,
        "hi": gov_gate.WHALE_STAKER_BPS_MAX,
        "step": gov_gate.WHALE_STEP_BPS,
        "gate": gov_gate.whale_defense_revision_ok,
    },
}

_ALLOWED_FEATURES = frozenset(OBSERVATION_FIELDS_V1) | frozenset(
    SURFACE_PARAMETER_NAMES_V1
)
_ALLOWED_POLICY_KEYS = frozenset(
    {
        "schema",
        "policy_id",
        "version",
        "surface",
        "features",
        "feature_bounds",
        "state_bins",
        "energy_model",
    }
)

_NOT_CLAIMED = (
    "does_not_authorize_settlement",
    "does_not_claim_observation_truth",
    "does_not_train_ebrm_online",
    "does_not_use_energy_as_acceptance_predicate",
    "does_not_bypass_exact_gates",
)


def _is_plain_int(value: object) -> bool:
    return type(value) is int


def _normalize_edges(raw: object, *, field: str) -> tuple[tuple[int, ...], list[str]]:
    if not isinstance(raw, Sequence) or isinstance(raw, (str, bytes, bytearray)):
        return (), [f"ebrm_state_bins_{field}_must_be_sequence"]
    errors: list[str] = []
    edges: list[int] = []
    previous: int | None = None
    for index, value in enumerate(raw):
        if not _is_plain_int(value):
            errors.append(f"ebrm_state_bins_{field}_{index}_must_be_plain_int")
            continue
        if value < 0:
            errors.append(f"ebrm_state_bins_{field}_{index}_must_be_nonnegative")
            continue
        if previous is not None and value <= previous:
            errors.append(f"ebrm_state_bins_{field}_must_be_strictly_ascending")
            continue
        edges.append(value)
        previous = value
    return tuple(edges), errors


def _snapshot_energy_model(raw: object) -> tuple[dict[str, object], list[str]]:
    if type(raw) is not dict:
        return {}, ["ebrm_energy_model_must_be_plain_dict"]
    try:
        _ENERGY_MODEL_HASH(raw)
    except (TypeError, ValueError):
        return {}, ["ebrm_energy_model_invalid"]
    targets = raw.get("targets")
    if type(targets) is not dict:
        return {}, ["ebrm_energy_model_invalid"]
    return {
        "targets": dict(targets),
        "w_track": raw["w_track"],
        "w_move": raw["w_move"],
    }, []


def _normalize_feature_bounds(
    raw: object,
    *,
    features: Sequence[str],
) -> tuple[dict[str, dict[str, int]], list[str]]:
    if not isinstance(raw, Mapping):
        return {}, ["ebrm_feature_bounds_must_be_object"]
    errors: list[str] = []
    bounds: dict[str, dict[str, int]] = {}
    for key in raw:
        if key not in features:
            errors.append(f"ebrm_feature_bounds_unknown_feature:{key}")
    for feature in features:
        item = raw.get(feature)
        if not isinstance(item, Mapping):
            errors.append(f"ebrm_feature_bounds_missing:{feature}")
            continue
        lo = item.get("min")
        hi = item.get("max")
        if not _is_plain_int(lo):
            errors.append(f"ebrm_feature_bounds_{feature}_min_must_be_plain_int")
            continue
        if not _is_plain_int(hi):
            errors.append(f"ebrm_feature_bounds_{feature}_max_must_be_plain_int")
            continue
        if lo < 0 or hi < 0:
            errors.append(f"ebrm_feature_bounds_{feature}_must_be_nonnegative")
            continue
        if lo > hi:
            errors.append(f"ebrm_feature_bounds_{feature}_min_exceeds_max")
            continue
        bounds[feature] = {"min": int(lo), "max": int(hi)}
    return bounds, errors


def normalize_autonomous_governance_ebrm_policy_v1(
    policy: object,
) -> tuple[dict[str, Any], list[str]]:
    """Validate and snapshot an EBRM policy artifact."""

    if not isinstance(policy, Mapping):
        return {}, ["ebrm_policy_must_be_object"]
    errors: list[str] = []
    for key in policy:
        if key not in _ALLOWED_POLICY_KEYS:
            errors.append(f"ebrm_policy_unknown_key:{key}")
    if policy.get("schema") != AUTONOMOUS_GOVERNANCE_EBRM_POLICY_SCHEMA_V1:
        errors.append("ebrm_policy_schema_mismatch")
    policy_id = policy.get("policy_id")
    if type(policy_id) is not str or not policy_id:
        errors.append("ebrm_policy_id_invalid")
        policy_id = ""
    version = policy.get("version")
    if not _is_plain_int(version) or version < 1:
        errors.append("ebrm_policy_version_invalid")
        version = 0
    surface = policy.get("surface")
    if type(surface) is not str or surface not in _SURFACE_GUARDS:
        errors.append("ebrm_policy_surface_unsupported")
        surface = ""

    raw_features = policy.get("features")
    features: list[str] = []
    if not isinstance(raw_features, Sequence) or isinstance(
        raw_features, (str, bytes, bytearray)
    ):
        errors.append("ebrm_features_must_be_sequence")
    else:
        seen: set[str] = set()
        for feature in raw_features:
            if type(feature) is not str:
                errors.append("ebrm_feature_must_be_plain_str")
                continue
            if feature not in _ALLOWED_FEATURES:
                errors.append(f"ebrm_feature_unknown:{feature}")
                continue
            if feature in seen:
                errors.append(f"ebrm_feature_duplicate:{feature}")
                continue
            seen.add(feature)
            features.append(feature)
        if not features:
            errors.append("ebrm_features_empty")

    feature_bounds, bound_errors = _normalize_feature_bounds(
        policy.get("feature_bounds"),
        features=features,
    )
    errors.extend(bound_errors)

    bins_raw = policy.get("state_bins")
    bins: dict[str, list[int]] = {}
    if not isinstance(bins_raw, Mapping):
        errors.append("ebrm_state_bins_must_be_object")
    else:
        for key in bins_raw:
            if key not in features:
                errors.append(f"ebrm_state_bins_unknown_feature:{key}")
        for feature in features:
            if feature not in bins_raw:
                errors.append(f"ebrm_state_bins_missing:{feature}")
                continue
            edges, edge_errors = _normalize_edges(bins_raw.get(feature), field=feature)
            errors.extend(edge_errors)
            bins[feature] = list(edges)

    energy_model, energy_errors = _snapshot_energy_model(policy.get("energy_model"))
    errors.extend(energy_errors)

    if errors:
        return {}, errors
    return {
        "schema": AUTONOMOUS_GOVERNANCE_EBRM_POLICY_SCHEMA_V1,
        "policy_id": policy_id,
        "version": version,
        "surface": surface,
        "features": tuple(features),
        "feature_bounds": {
            feature: dict(feature_bounds[feature]) for feature in features
        },
        "state_bins": {feature: tuple(bins[feature]) for feature in features},
        "energy_model": energy_model,
    }, []


def ebrm_policy_content_hash_v1(policy: object) -> str:
    normalized, errors = normalize_autonomous_governance_ebrm_policy_v1(policy)
    if errors:
        raise ValueError(f"invalid ebrm policy artifact: {errors}")
    body = {
        **normalized,
        "features": list(normalized["features"]),
        "feature_bounds": {
            key: dict(value) for key, value in normalized["feature_bounds"].items()
        },
        "state_bins": {
            key: list(value) for key, value in normalized["state_bins"].items()
        },
    }
    return hash_v0(_EBRM_POLICY_HASH_TAG, body)


def _feature_value(
    *,
    feature: str,
    state: Mapping[str, int],
    observation: Mapping[str, Any],
    errors: list[str],
) -> int:
    if feature in state:
        return int(state[feature])
    if feature not in observation:
        errors.append(f"ebrm_observation_missing_feature:{feature}")
        return 0
    value = observation.get(feature)
    if not _is_plain_int(value):
        errors.append(f"ebrm_observation_{feature}_must_be_plain_int")
        return 0
    if value < 0:
        errors.append(f"ebrm_observation_{feature}_must_be_nonnegative")
        return 0
    return value


def evaluate_autonomous_governance_ebrm_policy_step_v1(
    *,
    policy: object,
    committed_surface_state: Mapping[str, Any],
    observation: Mapping[str, Any],
    approved: object,
    proposal_epoch: object,
    current_epoch: object,
    last_update_epoch: object = None,
    expected_policy_hash: object = None,
    expected_committed_context_hash: object = None,
) -> dict[str, Any]:
    """Evaluate one frozen EBRM step and gate the candidate."""

    errors: list[str] = []
    normalized_policy, policy_errors = normalize_autonomous_governance_ebrm_policy_v1(policy)
    errors.extend(policy_errors)
    policy_hash = ""
    if not policy_errors:
        policy_hash = ebrm_policy_content_hash_v1(policy)

    expected_hash = expected_policy_hash if type(expected_policy_hash) is str else ""
    if not expected_hash:
        errors.append("ebrm_expected_policy_hash_required")
    elif not _is_canonical_hash_v0(expected_hash):
        errors.append("ebrm_expected_policy_hash_invalid")
    elif policy_hash and policy_hash != expected_hash:
        errors.append("ebrm_expected_policy_hash_mismatch")

    state, state_errors = _normalize_surface_state(committed_surface_state)
    errors.extend(f"ebrm_committed_{error}" for error in state_errors)
    if not isinstance(observation, Mapping):
        errors.append("ebrm_observation_must_be_object")
        observation = {}
    if type(approved) is not bool:
        errors.append("ebrm_approved_must_be_bool")
        approved = False
    context_inputs_ok = True
    if not _is_plain_int(proposal_epoch):
        errors.append("ebrm_proposal_epoch_must_be_plain_int")
        proposal_epoch = 0
        context_inputs_ok = False
    elif proposal_epoch < 0:
        errors.append("ebrm_proposal_epoch_must_be_nonnegative")
        proposal_epoch = 0
        context_inputs_ok = False
    if not _is_plain_int(current_epoch):
        errors.append("ebrm_current_epoch_must_be_plain_int")
        current_epoch = 0
        context_inputs_ok = False
    elif current_epoch < 0:
        errors.append("ebrm_current_epoch_must_be_nonnegative")
        current_epoch = 0
        context_inputs_ok = False
    if last_update_epoch is not None:
        if not _is_plain_int(last_update_epoch):
            errors.append("ebrm_last_update_epoch_must_be_plain_int")
            last_update_epoch = None
            context_inputs_ok = False
        elif last_update_epoch < 0:
            errors.append("ebrm_last_update_epoch_must_be_nonnegative")
            last_update_epoch = None
            context_inputs_ok = False

    context_hash = ""
    if not state_errors and context_inputs_ok:
        context_hash = governance_surface_context_hash_v1(
            surface_state=state,
            current_epoch=int(current_epoch),
            proposal_epoch=int(proposal_epoch),
            last_update_epoch=last_update_epoch
            if last_update_epoch is None
            else int(last_update_epoch),
        )
    expected_context = (
        expected_committed_context_hash
        if type(expected_committed_context_hash) is str
        else ""
    )
    if not expected_context:
        errors.append("ebrm_expected_committed_context_hash_required")
    elif not _is_canonical_hash_v0(expected_context):
        errors.append("ebrm_expected_committed_context_hash_invalid")
    elif context_hash and context_hash != expected_context:
        errors.append("ebrm_committed_context_hash_mismatch")

    surface = normalized_policy.get("surface", "") if normalized_policy else ""
    curr = int(state.get(surface, 0)) if surface else 0
    candidate = curr
    final_state = dict(state)
    gate_admitted = False
    energy_hit = False
    energy_value: int | None = None
    target: int | None = None
    state_key = ""
    state_bins: dict[str, int] = {}

    if not errors:
        features = normalized_policy["features"]
        bin_values: list[int] = []
        for feature in features:
            value = _feature_value(
                feature=feature,
                state=state,
                observation=observation,
                errors=errors,
            )
            bounds = normalized_policy["feature_bounds"][feature]
            if value < bounds["min"] or value > bounds["max"]:
                errors.append(f"ebrm_feature_out_of_training_domain:{feature}")
            edges = normalized_policy["state_bins"][feature]
            idx = _BIN_INDEX(value, edges)
            state_bins[feature] = idx
            bin_values.append(idx)
        if not errors:
            bin_tuple = tuple(bin_values)
            state_key = _STATE_KEY(bin_tuple)
            guard = _SURFACE_GUARDS[surface]
            energy_model = normalized_policy["energy_model"]
            energy_pin = _ENERGY_MODEL_HASH(energy_model)
            result = _ENERGY_PROPOSE(
                bin_tuple,
                energy_model,
                curr,
                lo=guard["lo"],
                hi=guard["hi"],
                step=guard["step"],
                expected_hash=energy_pin,
            )
            candidate = result.proposed
            target = result.target
            energy_value = result.energy
            energy_hit = result.hit
            if not result.hit:
                errors.append("ebrm_energy_target_missing")
            else:
                gate = guard["gate"]
                verdict = gate(
                    approved,
                    True,
                    proposal_epoch,
                    current_epoch,
                    curr,
                    candidate,
                )
                if type(verdict) is not bool:
                    errors.append("ebrm_gate_verdict_must_be_bool")
                else:
                    gate_admitted = verdict

    admitted = gate_admitted and not errors
    if admitted and surface:
        final_state[surface] = candidate

    body = {
        "schema": AUTONOMOUS_GOVERNANCE_EBRM_STEP_SCHEMA_V1,
        "ok": admitted,
        "admitted": admitted,
        "errors": tuple(errors),
        "policy_hash": policy_hash,
        "expected_policy_hash": expected_hash,
        "surface": surface,
        "features": tuple(normalized_policy.get("features", ()))
        if normalized_policy
        else (),
        "state_bins": state_bins,
        "state_key": state_key,
        "curr": curr,
        "candidate": int(candidate),
        "target": target,
        "energy": energy_value,
        "energy_hit": energy_hit,
        "gate_admitted": gate_admitted,
        "approved": bool(approved),
        "proposal_epoch": int(proposal_epoch),
        "current_epoch": int(current_epoch),
        "committed_context_hash": context_hash,
        "expected_committed_context_hash": expected_context,
        "committed_state": dict(state),
        "final_state": final_state,
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "step_hash": hash_v0(_EBRM_STEP_HASH_TAG, body)}
