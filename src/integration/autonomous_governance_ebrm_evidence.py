"""Verifier-labeled EBRM corpus and ranking evidence for autonomous governance.

This module is offline evidence tooling. It generates deterministic synthetic
governance contexts, labels candidate revisions with the exact `gov_gate.py`
surface gates, compares deterministic energy scorers, and can train a small
integer ranker from the train split.

The generated report is training and search-efficiency evidence only. It does
not train online, authorize governance updates, mutate ledger state, or replace
the Tau/Python gate labels.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from typing import Any, Callable, Mapping, Sequence, cast

from src.integration.zeno_ledger_v0 import hash_v0
from src.tau_specs.governance import gov_gate


AUTONOMOUS_GOVERNANCE_EBRM_CORPUS_SCHEMA_V1 = (
    "zenodex.autonomous_governance.ebrm_labeled_corpus.v1"
)
AUTONOMOUS_GOVERNANCE_EBRM_EVIDENCE_SCHEMA_V1 = (
    "zenodex.autonomous_governance.ebrm_evidence_report.v1"
)
AUTONOMOUS_GOVERNANCE_EBRM_TRAINED_RANKER_SCHEMA_V1 = (
    "zenodex.autonomous_governance.ebrm_trained_ranker.v1"
)
AUTONOMOUS_GOVERNANCE_EBRM_TRAINING_REPORT_SCHEMA_V1 = (
    "zenodex.autonomous_governance.ebrm_training_report.v1"
)

_CORPUS_HASH_TAG = "autonomous_governance_ebrm_labeled_corpus_v1"
_EVIDENCE_HASH_TAG = "autonomous_governance_ebrm_evidence_report_v1"
_TRAINED_RANKER_HASH_TAG = "autonomous_governance_ebrm_trained_ranker_v1"
_TRAINING_REPORT_HASH_TAG = "autonomous_governance_ebrm_training_report_v1"
_ROW_HASH_TAG = "autonomous_governance_ebrm_labeled_row_v1"
_GROUP_HASH_TAG = "autonomous_governance_ebrm_candidate_group_v1"

_REPLAY_COMMAND = "python3 tools/autonomous_governance_q_policy.py ebrm-evidence"
_TRAIN_REPLAY_COMMAND = "python3 tools/autonomous_governance_q_policy.py ebrm-train"

_NOT_CLAIMED = (
    "does_not_authorize_governance_update",
    "does_not_authorize_settlement",
    "does_not_replace_tau_or_gov_gate",
    "does_not_use_energy_as_acceptance_predicate",
    "does_not_train_ebrm_online",
    "does_not_claim_live_distribution_coverage",
    "does_not_claim_production_promotion",
)

_OBSERVATION_GRID = {
    "deviation_bps": (0, 25, 100, 300, 500, 800, 1_000),
    "volatility_bps": (25, 250, 750, 1_000),
    "liquidity_depth_bps": (1_000, 5_000, 9_000),
}

_BASE_SURFACE_STATE = {
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

_PROPOSAL_EPOCH = 10
_CURRENT_EPOCH = 34

_MODEL_FEATURE_NAMES = (
    "structural_guard_pressure",
    "target_tracking",
    "movement",
    "wrong_direction",
    "thin_liquidity_underreaction",
)

_HAND_COMPOSITIONAL_WEIGHTS = {
    "structural_guard_pressure": 1_000_000,
    "target_tracking": 100,
    "movement": 2,
    "wrong_direction": 20,
    "thin_liquidity_underreaction": 10,
}

_TRAINING_GRID = {
    "structural_guard_pressure": (100_000, 1_000_000),
    "target_tracking": (50, 100, 200),
    "movement": (0, 2),
    "wrong_direction": (0, 20),
    "thin_liquidity_underreaction": (0, 10),
}


GateFn = Callable[[bool, bool, int, int, int, int], bool]


@dataclass(frozen=True)
class SurfaceSpec:
    name: str
    lo: int
    hi: int
    step: int
    current_values: tuple[int, ...]
    gate: GateFn
    target_scale_num: int
    target_scale_den: int


_SURFACES: tuple[SurfaceSpec, ...] = (
    SurfaceSpec(
        name="fee_bps",
        lo=0,
        hi=gov_gate.FEE_MAX_BPS,
        step=gov_gate.FEE_STEP_BPS,
        current_values=(0, 30, 980),
        gate=gov_gate.fee_revision_ok,
        target_scale_num=1,
        target_scale_den=1,
    ),
    SurfaceSpec(
        name="funding_cap_bps",
        lo=0,
        hi=gov_gate.FUNDING_CAP_MAX_BPS,
        step=gov_gate.FUNDING_STEP_BPS,
        current_values=(0, 100, 190),
        gate=gov_gate.funding_rate_revision_ok,
        target_scale_num=1,
        target_scale_den=2,
    ),
    SurfaceSpec(
        name="staker_bps",
        lo=0,
        hi=gov_gate.WHALE_STAKER_BPS_MAX,
        step=gov_gate.WHALE_STEP_BPS,
        current_values=(0, 5_000, 6_800),
        gate=gov_gate.whale_defense_revision_ok,
        target_scale_num=10,
        target_scale_den=1,
    ),
)


def _clamp(value: int, lo: int, hi: int) -> int:
    return lo if value < lo else hi if value > hi else value


def _surface_state(surface: str, curr: int) -> dict[str, int]:
    state = dict(_BASE_SURFACE_STATE)
    state[surface] = curr
    return state


def _observation(*, deviation_bps: int, volatility_bps: int, liquidity_depth_bps: int) -> dict[str, int]:
    return {
        "observed_price_bps": 10_000 + deviation_bps,
        "target_price_bps": 10_000,
        "deviation_bps": deviation_bps,
        "volatility_bps": volatility_bps,
        "divergence_bps": deviation_bps // 10,
        "freshness_lag_epochs": 0,
        "liquidity_depth_bps": liquidity_depth_bps,
    }


def _stress_signal(observation: Mapping[str, int]) -> int:
    deviation = int(observation["deviation_bps"])
    volatility = int(observation["volatility_bps"])
    liquidity = int(observation["liquidity_depth_bps"])
    stress = deviation // 20 + volatility // 50 + max(0, 5_000 - liquidity) // 100
    calm_relief = max(0, liquidity - 5_000) // 500 + max(0, 200 - volatility) // 25
    return stress - calm_relief


def _target_for(surface: SurfaceSpec, curr: int, observation: Mapping[str, int]) -> int:
    signal = _stress_signal(observation)
    raw_delta = (signal * surface.target_scale_num) // surface.target_scale_den
    return _clamp(curr + raw_delta, surface.lo, surface.hi)


def _candidate_values(surface: SurfaceSpec, curr: int, target: int) -> tuple[int, ...]:
    band_lo = max(surface.lo, curr - surface.step)
    band_hi = min(surface.hi, curr + surface.step)
    stride = max(1, surface.step // 5)
    candidates = {band_lo, band_hi, curr, target}
    value = band_lo
    while value <= band_hi:
        candidates.add(value)
        value += stride
    candidates.update(
        {
            curr - surface.step - 1,
            curr + surface.step + 1,
            surface.lo - 1,
            surface.hi + 1,
            target - 1,
            target + 1,
        }
    )
    return tuple(sorted(candidates))


def _gate_admitted(surface: SurfaceSpec, curr: int, candidate: int) -> bool:
    verdict = surface.gate(
        True,
        True,
        _PROPOSAL_EPOCH,
        _CURRENT_EPOCH,
        curr,
        candidate,
    )
    return type(verdict) is bool and verdict


def _objective_cost(
    *,
    surface: SurfaceSpec,
    curr: int,
    candidate: int,
    target: int,
    observation: Mapping[str, int],
) -> int:
    tracking = abs(candidate - target) * 100
    churn = abs(candidate - curr) * 2
    signal = _stress_signal(observation)
    wrong_direction = 0
    if signal > 0 and candidate < curr:
        wrong_direction = abs(candidate - curr) * 20
    elif signal < 0 and candidate > curr:
        wrong_direction = abs(candidate - curr) * 20
    thin_liquidity_underreaction = 0
    if observation["liquidity_depth_bps"] <= 1_000 and candidate < target:
        thin_liquidity_underreaction = abs(target - candidate) * 10
    surface_weight = 1 if surface.name != "staker_bps" else 2
    return surface_weight * (tracking + churn + wrong_direction + thin_liquidity_underreaction)


def _structural_guard_pressure(surface: SurfaceSpec, curr: int, candidate: int) -> int:
    """Pre-label guard distance from immutable bounds and step constants.

    This does not read `gate_admitted`. It is the local hard-term feature an
    energy ranker can compute before the exact gate labels the candidate.
    """

    pressure = 0
    if candidate < surface.lo:
        pressure += surface.lo - candidate
    if candidate > surface.hi:
        pressure += candidate - surface.hi
    step_overflow = abs(candidate - curr) - surface.step
    if step_overflow > 0:
        pressure += step_overflow
    return pressure


def _model_feature_values(
    *,
    surface: SurfaceSpec,
    curr: int,
    candidate: int,
    target: int,
    observation: Mapping[str, int],
) -> dict[str, int]:
    signal = _stress_signal(observation)
    wrong_direction = 0
    if signal > 0 and candidate < curr:
        wrong_direction = abs(candidate - curr)
    elif signal < 0 and candidate > curr:
        wrong_direction = abs(candidate - curr)
    thin_liquidity_underreaction = 0
    if observation["liquidity_depth_bps"] <= 1_000 and candidate < target:
        thin_liquidity_underreaction = target - candidate
    return {
        "structural_guard_pressure": _structural_guard_pressure(surface, curr, candidate),
        "target_tracking": abs(candidate - target),
        "movement": abs(candidate - curr),
        "wrong_direction": wrong_direction,
        "thin_liquidity_underreaction": thin_liquidity_underreaction,
    }


def _energy_from_weights(
    feature_values: Mapping[str, int],
    weights: Mapping[str, int],
) -> int:
    return sum(int(feature_values[name]) * int(weights[name]) for name in _MODEL_FEATURE_NAMES)


def _baseline_energy(feature_values: Mapping[str, int]) -> int:
    return (
        int(feature_values["target_tracking"]) * 100
        + int(feature_values["movement"]) * 2
    )


def _compositional_energy(feature_values: Mapping[str, int]) -> int:
    return _energy_from_weights(feature_values, _HAND_COMPOSITIONAL_WEIGHTS)


def _split_for_group(group_id: str) -> str:
    digest = group_id[2:] if group_id.startswith("0x") else group_id
    bucket = int(digest[-8:], 16) % 5
    return "heldout" if bucket == 0 else "train"


def _group_id(
    *,
    surface: SurfaceSpec,
    curr: int,
    observation: Mapping[str, int],
) -> str:
    return hash_v0(
        _GROUP_HASH_TAG,
        {
            "schema": "zenodex.autonomous_governance.ebrm_candidate_group.v1",
            "surface": surface.name,
            "curr": curr,
            "observation": dict(observation),
            "proposal_epoch": _PROPOSAL_EPOCH,
            "current_epoch": _CURRENT_EPOCH,
        },
    )


def _row_id(row: Mapping[str, Any]) -> str:
    return hash_v0(_ROW_HASH_TAG, row)


def _rows_for_group(
    *,
    surface: SurfaceSpec,
    curr: int,
    observation: Mapping[str, int],
) -> list[dict[str, Any]]:
    target = _target_for(surface, curr, observation)
    group_id = _group_id(surface=surface, curr=curr, observation=observation)
    split = _split_for_group(group_id)
    state = _surface_state(surface.name, curr)
    rows: list[dict[str, Any]] = []
    for rank, candidate in enumerate(_candidate_values(surface, curr, target)):
        admitted = _gate_admitted(surface, curr, candidate)
        objective_cost = _objective_cost(
            surface=surface,
            curr=curr,
            candidate=candidate,
            target=target,
            observation=observation,
        )
        model_features = _model_feature_values(
            surface=surface,
            curr=curr,
            candidate=candidate,
            target=target,
            observation=observation,
        )
        baseline = _baseline_energy(model_features)
        compositional = _compositional_energy(model_features)
        gate_errors = () if admitted else (f"gov_gate_rejected:{surface.name}",)
        row = {
            "schema": "zenodex.autonomous_governance.ebrm_labeled_row.v1",
            "group_id": group_id,
            "split": split,
            "candidate_index": rank,
            "surface": surface.name,
            "curr": curr,
            "candidate": candidate,
            "target": target,
            "delta": candidate - curr,
            "surface_state": state,
            "observation": dict(observation),
            "proposal_epoch": _PROPOSAL_EPOCH,
            "current_epoch": _CURRENT_EPOCH,
            "gate_admitted": admitted,
            "gate_errors": gate_errors,
            "objective_cost": objective_cost,
            "model_features": model_features,
            "baseline_energy": baseline,
            "compositional_energy": compositional,
            "energy_terms": {
                "structural_guard_penalty": (
                    model_features["structural_guard_pressure"]
                    * _HAND_COMPOSITIONAL_WEIGHTS["structural_guard_pressure"]
                ),
                "target_tracking": (
                    model_features["target_tracking"]
                    * _HAND_COMPOSITIONAL_WEIGHTS["target_tracking"]
                ),
                "movement": (
                    model_features["movement"]
                    * _HAND_COMPOSITIONAL_WEIGHTS["movement"]
                ),
                "wrong_direction": (
                    model_features["wrong_direction"]
                    * _HAND_COMPOSITIONAL_WEIGHTS["wrong_direction"]
                ),
                "thin_liquidity_underreaction": (
                    model_features["thin_liquidity_underreaction"]
                    * _HAND_COMPOSITIONAL_WEIGHTS["thin_liquidity_underreaction"]
                ),
            },
        }
        rows.append({**row, "row_id": _row_id(row)})
    admitted_costs = [
        int(row["objective_cost"]) for row in rows if row["gate_admitted"] is True
    ]
    frontier_cost = min(admitted_costs) if admitted_costs else None
    for row in rows:
        if row["gate_admitted"] is not True:
            row["target_class"] = "gate_rejected"
            row["utility_regret_to_frontier"] = None
        elif frontier_cost is not None and row["objective_cost"] == frontier_cost:
            row["target_class"] = "accepted_frontier"
            row["utility_regret_to_frontier"] = 0
        else:
            row["target_class"] = "accepted_dominated"
            row["utility_regret_to_frontier"] = int(row["objective_cost"]) - int(frontier_cost)
    return rows


def _corpus_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for surface in _SURFACES:
        for curr in surface.current_values:
            for deviation in _OBSERVATION_GRID["deviation_bps"]:
                for volatility in _OBSERVATION_GRID["volatility_bps"]:
                    for liquidity in _OBSERVATION_GRID["liquidity_depth_bps"]:
                        rows.extend(
                            _rows_for_group(
                                surface=surface,
                                curr=curr,
                                observation=_observation(
                                    deviation_bps=deviation,
                                    volatility_bps=volatility,
                                    liquidity_depth_bps=liquidity,
                                ),
                            )
                        )
    rows.sort(key=lambda row: (str(row["group_id"]), int(row["candidate_index"])))
    return rows


def _group_rows(rows: Sequence[Mapping[str, Any]]) -> dict[str, list[Mapping[str, Any]]]:
    grouped: dict[str, list[Mapping[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[str(row["group_id"])].append(row)
    return dict(sorted(grouped.items()))


def _surface_counts(rows: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = defaultdict(int)
    for row in rows:
        counts[str(row["surface"])] += 1
    return dict(sorted(counts.items()))


def _target_class_counts(rows: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = defaultdict(int)
    for row in rows:
        counts[str(row["target_class"])] += 1
    return dict(sorted(counts.items()))


def _row_energy(
    row: Mapping[str, Any],
    *,
    energy_field: str | None = None,
    weights: Mapping[str, int] | None = None,
) -> int:
    if weights is not None:
        features = row.get("model_features")
        if not isinstance(features, Mapping):
            raise ValueError("row_missing_model_features")
        feature_values = {
            name: int(features[name])
            for name in _MODEL_FEATURE_NAMES
        }
        return _energy_from_weights(feature_values, weights)
    if energy_field is None:
        raise ValueError("energy_field_or_weights_required")
    return int(row[energy_field])


def _score_group(
    rows: Sequence[Mapping[str, Any]],
    *,
    energy_field: str | None = None,
    weights: Mapping[str, int] | None = None,
) -> dict[str, int | bool]:
    ranked = sorted(
        rows,
        key=lambda row: (
            _row_energy(row, energy_field=energy_field, weights=weights),
            int(row["candidate"]),
            str(row["row_id"]),
        ),
    )
    frontier = min(
        (int(row["objective_cost"]) for row in ranked if row["gate_admitted"] is True),
        default=None,
    )
    if frontier is None:
        return {
            "has_admitted": False,
            "first_admitted_rank": 0,
            "invalid_before_first_admitted": len(ranked),
            "selected_regret": 0,
            "rank1_gate_admitted": False,
            "rank1_frontier": False,
        }
    first_admitted_rank = 0
    invalid_before = 0
    selected_regret = 0
    for index, row in enumerate(ranked, start=1):
        if row["gate_admitted"] is True:
            first_admitted_rank = index
            selected_regret = int(row["objective_cost"]) - int(frontier)
            break
        invalid_before += 1
    return {
        "has_admitted": True,
        "first_admitted_rank": first_admitted_rank,
        "invalid_before_first_admitted": invalid_before,
        "selected_regret": selected_regret,
        "rank1_gate_admitted": ranked[0]["gate_admitted"] is True,
        "rank1_frontier": ranked[0]["gate_admitted"] is True
        and int(ranked[0]["objective_cost"]) == int(frontier),
    }


def _aggregate_scores(
    grouped: Mapping[str, Sequence[Mapping[str, Any]]],
    *,
    energy_field: str | None = None,
    weights: Mapping[str, int] | None = None,
    split: str | None,
) -> dict[str, Any]:
    selected = [
        group_rows
        for group_rows in grouped.values()
        if split is None or str(group_rows[0]["split"]) == split
    ]
    scores = [
        _score_group(group_rows, energy_field=energy_field, weights=weights)
        for group_rows in selected
    ]
    groups_total = len(scores)
    first_rank_total = sum(int(score["first_admitted_rank"]) for score in scores)
    groups_with_admitted = sum(1 for score in scores if score["has_admitted"] is True)
    return {
        "groups_total": groups_total,
        "groups_with_admitted": groups_with_admitted,
        "groups_without_admitted": groups_total - groups_with_admitted,
        "first_admitted_rank_total": first_rank_total,
        "first_admitted_rank_mean_numer": first_rank_total,
        "first_admitted_rank_mean_denom": groups_total,
        "invalid_before_first_admitted_total": sum(
            int(score["invalid_before_first_admitted"]) for score in scores
        ),
        "selected_regret_total": sum(int(score["selected_regret"]) for score in scores),
        "rank1_gate_admitted_count": sum(
            1 for score in scores if score["rank1_gate_admitted"] is True
        ),
        "rank1_frontier_count": sum(
            1 for score in scores if score["rank1_frontier"] is True
        ),
    }


def _ranking_metrics(
    rows: Sequence[Mapping[str, Any]],
    *,
    learned_weights: Mapping[str, int] | None = None,
) -> dict[str, Any]:
    grouped = _group_rows(rows)
    metrics: dict[str, Any] = {}
    for scorer_name, energy_field in (
        ("target_only_baseline", "baseline_energy"),
        ("compositional_ebrm", "compositional_energy"),
    ):
        metrics[scorer_name] = {
            "all": _aggregate_scores(grouped, energy_field=energy_field, split=None),
            "train": _aggregate_scores(grouped, energy_field=energy_field, split="train"),
            "heldout": _aggregate_scores(
                grouped, energy_field=energy_field, split="heldout"
            ),
        }
    if learned_weights is not None:
        metrics["learned_ebrm"] = {
            "all": _aggregate_scores(grouped, weights=learned_weights, split=None),
            "train": _aggregate_scores(grouped, weights=learned_weights, split="train"),
            "heldout": _aggregate_scores(
                grouped, weights=learned_weights, split="heldout"
            ),
        }
    base = metrics["target_only_baseline"]["heldout"]
    comp = metrics["compositional_ebrm"]["heldout"]
    metrics["comparison"] = {
        "heldout_regret_delta_baseline_minus_compositional": int(
            base["selected_regret_total"]
        )
        - int(comp["selected_regret_total"]),
        "heldout_invalid_before_first_delta_baseline_minus_compositional": int(
            base["invalid_before_first_admitted_total"]
        )
        - int(comp["invalid_before_first_admitted_total"]),
        "compositional_beats_or_ties_baseline": (
            int(comp["selected_regret_total"]) <= int(base["selected_regret_total"])
            and int(comp["invalid_before_first_admitted_total"])
            <= int(base["invalid_before_first_admitted_total"])
            and int(comp["rank1_gate_admitted_count"])
            >= int(base["rank1_gate_admitted_count"])
        ),
    }
    if learned_weights is not None:
        learned = metrics["learned_ebrm"]["heldout"]
        metrics["comparison"]["heldout_regret_delta_baseline_minus_learned"] = (
            int(base["selected_regret_total"])
            - int(learned["selected_regret_total"])
        )
        metrics["comparison"][
            "heldout_invalid_before_first_delta_baseline_minus_learned"
        ] = (
            int(base["invalid_before_first_admitted_total"])
            - int(learned["invalid_before_first_admitted_total"])
        )
        metrics["comparison"]["learned_beats_or_ties_baseline"] = (
            int(learned["selected_regret_total"])
            <= int(base["selected_regret_total"])
            and int(learned["invalid_before_first_admitted_total"])
            <= int(base["invalid_before_first_admitted_total"])
            and int(learned["rank1_gate_admitted_count"])
            >= int(base["rank1_gate_admitted_count"])
        )
    return metrics


def _corpus_summary(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    grouped = _group_rows(rows)
    split_counts: dict[str, int] = defaultdict(int)
    group_split_counts: dict[str, int] = defaultdict(int)
    for row in rows:
        split_counts[str(row["split"])] += 1
    for group_rows in grouped.values():
        group_split_counts[str(group_rows[0]["split"])] += 1
    return {
        "schema": "zenodex.autonomous_governance.ebrm_labeled_corpus_summary.v1",
        "rows_total": len(rows),
        "groups_total": len(grouped),
        "rows_by_split": dict(sorted(split_counts.items())),
        "groups_by_split": dict(sorted(group_split_counts.items())),
        "rows_by_surface": _surface_counts(rows),
        "rows_by_target_class": _target_class_counts(rows),
        "observation_grid": {key: list(values) for key, values in _OBSERVATION_GRID.items()},
        "surfaces": [
            {
                "surface": surface.name,
                "lo": surface.lo,
                "hi": surface.hi,
                "step": surface.step,
                "current_values": list(surface.current_values),
            }
            for surface in _SURFACES
        ],
        "labeler": "src.tau_specs.governance.gov_gate",
        "labeler_claim": "exact Python mirror of Tau governance gates labels every row",
        "split_rule": "group_hash_mod_5_zero_is_heldout",
        "feature_sources": (
            "surface",
            "curr",
            "candidate",
            "delta",
            "target_candidate_from_policy_objective",
            "observation.deviation_bps",
            "observation.volatility_bps",
            "observation.liquidity_depth_bps",
            "surface_state",
            "structural_guard_pressure_from_static_bounds_and_step",
        ),
        "forbidden_feature_sources": (
            "gate_admitted",
            "gate_errors",
            "target_class",
            "objective_cost",
            "utility_regret_to_frontier",
            "split",
        ),
        "model_feature_names": _MODEL_FEATURE_NAMES,
    }


def _weight_candidates() -> Sequence[dict[str, int]]:
    names = _MODEL_FEATURE_NAMES
    values = [_TRAINING_GRID[name] for name in names]
    candidates: list[dict[str, int]] = [
        dict(_HAND_COMPOSITIONAL_WEIGHTS),
    ]
    for combo in product(*values):
        candidates.append({name: int(value) for name, value in zip(names, combo)})
    unique: dict[tuple[int, ...], dict[str, int]] = {}
    for weights in candidates:
        key = tuple(int(weights[name]) for name in names)
        unique[key] = weights
    return [unique[key] for key in sorted(unique)]


def _training_objective(score: Mapping[str, Any]) -> tuple[int, int, int, int]:
    groups_total = int(score["groups_total"])
    rank1_frontier = int(score["rank1_frontier_count"])
    invalid_before = int(score["invalid_before_first_admitted_total"])
    regret = int(score["selected_regret_total"])
    missed_frontier = groups_total - rank1_frontier
    return (
        invalid_before * 10_000 + regret + missed_frontier * 100,
        invalid_before,
        regret,
        missed_frontier,
    )


def _train_weight_vector(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    grouped = _group_rows(rows)
    best_weights: dict[str, int] | None = None
    best_score: dict[str, Any] | None = None
    best_objective: tuple[int, int, int, int] | None = None
    evaluated = 0
    for weights in _weight_candidates():
        evaluated += 1
        score = _aggregate_scores(grouped, weights=weights, split="train")
        objective = _training_objective(score)
        tie_key = tuple(int(weights[name]) for name in _MODEL_FEATURE_NAMES)
        best_tie_key = (
            tuple(int(best_weights[name]) for name in _MODEL_FEATURE_NAMES)
            if best_weights is not None
            else None
        )
        if (
            best_objective is None
            or objective < best_objective
            or (
                objective == best_objective
                and best_tie_key is not None
                and tie_key < best_tie_key
            )
        ):
            best_weights = dict(weights)
            best_score = dict(score)
            best_objective = objective
    if best_weights is None or best_score is None or best_objective is None:
        raise ValueError("training_grid_empty")
    return {
        "weights": best_weights,
        "train_score": best_score,
        "training_objective": {
            "value": best_objective[0],
            "invalid_before_first_admitted_total": best_objective[1],
            "selected_regret_total": best_objective[2],
            "missed_frontier_count": best_objective[3],
        },
        "grid_points_evaluated": evaluated,
    }


def _trained_model(corpus_hash: str, training_result: Mapping[str, Any]) -> dict[str, Any]:
    weights = training_result.get("weights")
    if not isinstance(weights, Mapping):
        raise ValueError("training_result_missing_weights")
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_EBRM_TRAINED_RANKER_SCHEMA_V1,
        "model_id": "synthetic_linear_guard_energy_ranker_v1",
        "model_family": "integer_linear_energy_ranker",
        "feature_names": _MODEL_FEATURE_NAMES,
        "weights": {name: int(weights[name]) for name in _MODEL_FEATURE_NAMES},
        "training_corpus_hash": corpus_hash,
        "training_method": "deterministic_grid_search_on_grouped_train_split_v1",
        "objective": (
            "minimize invalid candidates before first admitted candidate, then "
            "regret, then missed frontier count"
        ),
        "authority": "candidate_ordering_only",
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "model_hash": hash_v0(_TRAINED_RANKER_HASH_TAG, body)}


def build_autonomous_governance_ebrm_corpus_v1() -> dict[str, Any]:
    """Build the deterministic verifier-labeled synthetic EBRM corpus."""

    rows = _corpus_rows()
    body = {
        "schema": AUTONOMOUS_GOVERNANCE_EBRM_CORPUS_SCHEMA_V1,
        "summary": _corpus_summary(rows),
        "rows": rows,
        "replay_command": _REPLAY_COMMAND,
        "not_claimed": _NOT_CLAIMED,
    }
    return {**body, "corpus_hash": hash_v0(_CORPUS_HASH_TAG, body)}


def build_autonomous_governance_ebrm_evidence_report_v1(
    *,
    include_corpus: bool = False,
) -> dict[str, Any]:
    """Build a deterministic EBRM evidence report with heldout ranking metrics."""

    corpus = build_autonomous_governance_ebrm_corpus_v1()
    rows_obj = corpus.get("rows")
    if not isinstance(rows_obj, Sequence):
        raise ValueError("corpus_rows_must_be_sequence")
    rows = cast(Sequence[Mapping[str, Any]], rows_obj)
    metrics = _ranking_metrics(rows)
    summary = corpus.get("summary")
    if not isinstance(summary, Mapping):
        raise ValueError("corpus_summary_must_be_mapping")
    comp_all = metrics["compositional_ebrm"]["all"]
    comparison = metrics["comparison"]
    evidence_ok = (
        int(comp_all["groups_without_admitted"]) == 0
        and bool(comparison["compositional_beats_or_ties_baseline"])
    )
    body: dict[str, Any] = {
        "schema": AUTONOMOUS_GOVERNANCE_EBRM_EVIDENCE_SCHEMA_V1,
        "ok": evidence_ok,
        "corpus_schema": AUTONOMOUS_GOVERNANCE_EBRM_CORPUS_SCHEMA_V1,
        "corpus_hash": corpus["corpus_hash"],
        "corpus_summary": summary,
        "ranking_metrics": metrics,
        "production_promotion_claim": False,
        "promotion_ready": False,
        "promotion_blockers": (
            "synthetic_corpus_only",
            "learned_ebrm_not_trained_or_cross_seed_validated",
            "no_live_distribution_or_adversarial_replay_claim",
            "runtime_authority_remains_exact_gov_gate",
        ),
        "determinism": {
            "uses_randomness": False,
            "uses_floats": False,
            "uses_online_learning": False,
            "split_rule": "group_hash_mod_5_zero_is_heldout",
        },
        "authority_boundary": {
            "model_role": "candidate_ordering_only",
            "label_authority": "src.tau_specs.governance.gov_gate",
            "admission_authority": "exact_gate_and_integration_admission_wrappers",
        },
        "replay_command": _REPLAY_COMMAND,
        "not_claimed": _NOT_CLAIMED,
    }
    if include_corpus:
        body["corpus"] = corpus
    return {**body, "evidence_hash": hash_v0(_EVIDENCE_HASH_TAG, body)}


def build_autonomous_governance_ebrm_training_report_v1(
    *,
    include_corpus: bool = False,
) -> dict[str, Any]:
    """Train and evaluate a deterministic integer EBRM ranker offline."""

    corpus = build_autonomous_governance_ebrm_corpus_v1()
    rows_obj = corpus["rows"]
    if not isinstance(rows_obj, Sequence):
        raise ValueError("corpus_rows_must_be_sequence")
    rows = cast(Sequence[Mapping[str, Any]], rows_obj)
    training_result = _train_weight_vector(rows)
    model = _trained_model(str(corpus["corpus_hash"]), training_result)
    weights_obj = model["weights"]
    if not isinstance(weights_obj, Mapping):
        raise ValueError("trained_model_weights_must_be_mapping")
    learned_weights = {name: int(weights_obj[name]) for name in _MODEL_FEATURE_NAMES}
    metrics = _ranking_metrics(rows, learned_weights=learned_weights)
    learned = metrics["learned_ebrm"]["heldout"]
    baseline = metrics["target_only_baseline"]["heldout"]
    comparison = metrics["comparison"]
    ok = (
        bool(comparison["learned_beats_or_ties_baseline"])
        and int(learned["groups_without_admitted"]) == 0
        and int(learned["rank1_gate_admitted_count"])
        >= int(baseline["rank1_gate_admitted_count"])
    )
    body: dict[str, Any] = {
        "schema": AUTONOMOUS_GOVERNANCE_EBRM_TRAINING_REPORT_SCHEMA_V1,
        "ok": ok,
        "corpus_hash": corpus["corpus_hash"],
        "corpus_summary": corpus["summary"],
        "trained_model": model,
        "training_result": training_result,
        "ranking_metrics": metrics,
        "production_promotion_claim": False,
        "promotion_ready": False,
        "promotion_blockers": (
            "synthetic_corpus_only",
            "cross_seed_learned_model_validation_not_yet_run",
            "adversarial_hard_negative_mining_not_yet_run",
            "no_live_distribution_replay_claim",
            "runtime_authority_remains_exact_gov_gate",
        ),
        "determinism": {
            "uses_randomness": False,
            "uses_floats": False,
            "uses_online_learning": False,
            "training_grid_points": int(training_result["grid_points_evaluated"]),
        },
        "authority_boundary": {
            "model_role": "candidate_ordering_only",
            "label_authority": "src.tau_specs.governance.gov_gate",
            "admission_authority": "exact_gate_and_integration_admission_wrappers",
        },
        "replay_command": _TRAIN_REPLAY_COMMAND,
        "not_claimed": _NOT_CLAIMED,
    }
    if include_corpus:
        body["corpus"] = corpus
    return {**body, "training_report_hash": hash_v0(_TRAINING_REPORT_HASH_TAG, body)}
