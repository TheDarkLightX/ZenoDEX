"""Zeno UX symbolic certificates.

This module is an advisory UX layer. It does not authorize settlement or mutate
state. It turns verifier-backed trade facts into a small symbolic object that a
wallet, agent, or design workflow can compare deterministically.
"""

from __future__ import annotations

import hashlib
import re
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from typing import cast

from ..state.canonical import canonical_json_bytes
from .domain_limits import is_strict_int

CERT_SCHEMA = "zenodex.ux.certificate.v1"
POLICY_SCHEMA = "zenodex.ux.policy.v1"
REGRET_POLICY_SCHEMA = "zenodex.ux.regret_policy.v1"
REGRET_CERT_SCHEMA = "zenodex.ux.regret_certificate.v1"
MINIMAX_REGRET_POLICY_SCHEMA = "zenodex.ux.minimax_regret_policy.v1"
MINIMAX_REGRET_CERT_SCHEMA = "zenodex.ux.minimax_regret_certificate.v1"
_BPS_SCALE = 10_000
_EXPLANATION_RE = re.compile(r"^[a-z][a-z0-9_]{0,95}$")

DECISION_CLASS_RANK: dict[str, int] = {
    "unknown": 0,
    "rejected": 1,
    "deferred": 2,
    "certified_approx": 3,
    "exact": 4,
}

HIGHER_IS_BETTER_AXES = frozenset({"decision_rank"})
LOWER_IS_BETTER_AXES = frozenset(
    {
        "latency_bound_ms",
        "value_loss_bound_bps",
        "mev_exposure_bound_bps",
        "finality_bound_blocks",
        "capital_at_risk_bps",
        "privacy_leakage_bits",
        "cognitive_steps",
    }
)
UX_AXES = HIGHER_IS_BETTER_AXES | LOWER_IS_BETTER_AXES
DEFAULT_POLICY_AXES = (
    "decision_rank",
    "value_loss_bound_bps",
    "mev_exposure_bound_bps",
    "latency_bound_ms",
    "finality_bound_blocks",
    "capital_at_risk_bps",
    "privacy_leakage_bits",
    "cognitive_steps",
)
REGRET_COST_AXES = (
    "decision_uncertainty",
    "value_loss_bound_bps",
    "mev_exposure_bound_bps",
    "latency_bound_ms",
    "finality_bound_blocks",
    "capital_at_risk_bps",
    "privacy_leakage_bits",
    "cognitive_steps",
)
DEFAULT_REGRET_WEIGHTS = (
    ("decision_uncertainty", 10_000),
    ("value_loss_bound_bps", 100),
    ("mev_exposure_bound_bps", 100),
    ("capital_at_risk_bps", 100),
    ("latency_bound_ms", 1),
    ("finality_bound_blocks", 250),
    ("privacy_leakage_bits", 20),
    ("cognitive_steps", 250),
)
DEFAULT_MINIMAX_SAFETY_AXES = (
    "decision_uncertainty",
    "value_loss_bound_bps",
    "mev_exposure_bound_bps",
    "capital_at_risk_bps",
    "privacy_leakage_bits",
)
DEFAULT_MINIMAX_FRICTION_WEIGHTS = (
    ("latency_bound_ms", 1),
    ("finality_bound_blocks", 250),
    ("cognitive_steps", 250),
)
_MINIMAX_BUDGET_VIOLATION_PENALTY = 10_001
_MAX_DECISION_RANK = max(DECISION_CLASS_RANK.values())


@dataclass(frozen=True)
class ZenoUXCertificate:
    schema: str
    certificate_id: str
    surface: str
    scenario_id: str
    decision_class: str
    latency_bound_ms: int
    value_loss_bound_bps: int
    mev_exposure_bound_bps: int
    finality_bound_blocks: int
    capital_at_risk_bps: int
    privacy_leakage_bits: int
    cognitive_steps: int
    explanation_code: str
    next_action: str
    evidence_refs: tuple[str, ...]

    def __post_init__(self) -> None:
        if self.schema != CERT_SCHEMA:
            raise ValueError("invalid Zeno UX certificate schema")
        _require_text_id(self.certificate_id, name="certificate_id")
        _require_text_id(self.surface, name="surface")
        _require_text_id(self.scenario_id, name="scenario_id")
        if self.decision_class not in DECISION_CLASS_RANK:
            raise ValueError("unknown decision_class")
        _require_non_negative_int(self.latency_bound_ms, name="latency_bound_ms")
        _require_bps(self.value_loss_bound_bps, name="value_loss_bound_bps")
        _require_bps(self.mev_exposure_bound_bps, name="mev_exposure_bound_bps")
        _require_non_negative_int(
            self.finality_bound_blocks,
            name="finality_bound_blocks",
        )
        _require_bps(self.capital_at_risk_bps, name="capital_at_risk_bps")
        _require_non_negative_int(
            self.privacy_leakage_bits,
            name="privacy_leakage_bits",
        )
        _require_non_negative_int(self.cognitive_steps, name="cognitive_steps")
        _require_explanation_code(self.explanation_code)
        _require_text_id(self.next_action, name="next_action")
        evidence = _require_evidence_refs(self.evidence_refs)
        object.__setattr__(self, "evidence_refs", evidence)
        if self.decision_class in {"exact", "certified_approx"} and not evidence:
            raise ValueError("verifier-backed decision requires evidence_refs")
        if self.decision_class == "exact" and self.value_loss_bound_bps != 0:
            raise ValueError("exact decision requires zero value_loss_bound_bps")


@dataclass(frozen=True)
class ZenoUXComparison:
    relation: str
    better_axes: tuple[str, ...]
    worse_axes: tuple[str, ...]
    reasons: tuple[str, ...]

    def __post_init__(self) -> None:
        if self.relation not in {
            "dominates",
            "dominated_by",
            "equivalent",
            "incomparable",
        }:
            raise ValueError("invalid comparison relation")


@dataclass(frozen=True)
class ZenoUXPolicy:
    schema: str
    policy_id: str
    priority_axes: tuple[str, ...] = DEFAULT_POLICY_AXES

    def __post_init__(self) -> None:
        if self.schema != POLICY_SCHEMA:
            raise ValueError("invalid Zeno UX policy schema")
        _require_text_id(self.policy_id, name="policy_id")
        axes = _require_axes(self.priority_axes)
        object.__setattr__(self, "priority_axes", axes)


@dataclass(frozen=True)
class ZenoUXRegretPolicy:
    schema: str
    policy_id: str
    weights: object = DEFAULT_REGRET_WEIGHTS
    max_regret_score: int = 0
    top_term_count: int = 3

    def __post_init__(self) -> None:
        if self.schema != REGRET_POLICY_SCHEMA:
            raise ValueError("invalid Zeno UX regret policy schema")
        _require_text_id(self.policy_id, name="policy_id")
        weights = _require_regret_weights(self.weights)
        object.__setattr__(self, "weights", weights)
        _require_non_negative_int(
            self.max_regret_score,
            name="max_regret_score",
        )
        _require_positive_int(self.top_term_count, name="top_term_count")


@dataclass(frozen=True)
class ZenoUXRegretCertificate:
    schema: str
    certificate_id: str
    policy_id: str
    surface: str
    scenario_id: str
    chosen_certificate_id: str
    best_certificate_id: str
    chosen_score: int
    best_score: int
    regret_score: int
    regret_threshold: int
    regret_ok: bool
    top_regret_terms: tuple[tuple[str, int], ...]
    candidate_hashes: tuple[str, ...]
    evidence_refs: tuple[str, ...]

    def __post_init__(self) -> None:
        if self.schema != REGRET_CERT_SCHEMA:
            raise ValueError("invalid Zeno UX regret certificate schema")
        _require_text_id(self.certificate_id, name="certificate_id")
        _require_text_id(self.policy_id, name="policy_id")
        _require_text_id(self.surface, name="surface")
        _require_text_id(self.scenario_id, name="scenario_id")
        _require_text_id(
            self.chosen_certificate_id,
            name="chosen_certificate_id",
        )
        _require_text_id(self.best_certificate_id, name="best_certificate_id")
        chosen_score = _require_non_negative_int(
            self.chosen_score,
            name="chosen_score",
        )
        best_score = _require_non_negative_int(self.best_score, name="best_score")
        regret_score = _require_non_negative_int(
            self.regret_score,
            name="regret_score",
        )
        regret_threshold = _require_non_negative_int(
            self.regret_threshold,
            name="regret_threshold",
        )
        if chosen_score < best_score:
            raise ValueError("chosen_score must be >= best_score")
        if regret_score != chosen_score - best_score:
            raise ValueError("regret_score must equal chosen_score - best_score")
        regret_ok = _require_bool(self.regret_ok, name="regret_ok")
        if regret_ok != (regret_score <= regret_threshold):
            raise ValueError("regret_ok must match regret_score <= threshold")
        terms = _require_regret_terms(self.top_regret_terms)
        object.__setattr__(self, "top_regret_terms", terms)
        candidate_hashes = _require_hash_refs(
            self.candidate_hashes,
            name="candidate_hashes",
        )
        if not candidate_hashes:
            raise ValueError("candidate_hashes must be non-empty")
        object.__setattr__(self, "candidate_hashes", candidate_hashes)
        evidence = _require_evidence_refs(self.evidence_refs)
        object.__setattr__(self, "evidence_refs", evidence)


@dataclass(frozen=True)
class ZenoUXMinimaxRegretPolicy:
    schema: str
    policy_id: str
    safety_axes: object = DEFAULT_MINIMAX_SAFETY_AXES
    safety_budgets: object = ()
    friction_weights: object = DEFAULT_MINIMAX_FRICTION_WEIGHTS
    max_safety_regret: int = 0
    max_friction_score: int = 0
    top_term_count: int = 3

    def __post_init__(self) -> None:
        if self.schema != MINIMAX_REGRET_POLICY_SCHEMA:
            raise ValueError("invalid Zeno UX minimax regret policy schema")
        _require_text_id(self.policy_id, name="policy_id")
        safety_axes = _require_regret_axes(self.safety_axes, name="safety_axes")
        object.__setattr__(self, "safety_axes", safety_axes)
        budgets = _require_regret_bounds(
            self.safety_budgets,
            allowed_axes=safety_axes,
        )
        object.__setattr__(self, "safety_budgets", budgets)
        friction_weights = _require_regret_weights(self.friction_weights)
        object.__setattr__(self, "friction_weights", friction_weights)
        _require_non_negative_int(self.max_safety_regret, name="max_safety_regret")
        _require_non_negative_int(self.max_friction_score, name="max_friction_score")
        _require_positive_int(self.top_term_count, name="top_term_count")


@dataclass(frozen=True)
class ZenoUXMinimaxRegretCertificate:
    schema: str
    certificate_id: str
    policy_id: str
    surface: str
    scenario_id: str
    chosen_certificate_id: str
    best_certificate_id: str
    chosen_safety_regret: int
    best_safety_regret: int
    safety_regret_delta: int
    safety_regret_threshold: int
    chosen_friction_score: int
    best_friction_score: int
    friction_score_delta: int
    friction_score_threshold: int
    regret_ok: bool
    top_regret_terms: tuple[tuple[str, int], ...]
    rejected_candidate_ids: tuple[str, ...]
    candidate_hashes: tuple[str, ...]
    evidence_refs: tuple[str, ...]

    def __post_init__(self) -> None:
        if self.schema != MINIMAX_REGRET_CERT_SCHEMA:
            raise ValueError("invalid Zeno UX minimax regret certificate schema")
        _require_text_id(self.certificate_id, name="certificate_id")
        _require_text_id(self.policy_id, name="policy_id")
        _require_text_id(self.surface, name="surface")
        _require_text_id(self.scenario_id, name="scenario_id")
        _require_text_id(
            self.chosen_certificate_id,
            name="chosen_certificate_id",
        )
        _require_text_id(self.best_certificate_id, name="best_certificate_id")
        chosen_safety = _require_non_negative_int(
            self.chosen_safety_regret,
            name="chosen_safety_regret",
        )
        best_safety = _require_non_negative_int(
            self.best_safety_regret,
            name="best_safety_regret",
        )
        safety_delta = _require_non_negative_int(
            self.safety_regret_delta,
            name="safety_regret_delta",
        )
        safety_threshold = _require_non_negative_int(
            self.safety_regret_threshold,
            name="safety_regret_threshold",
        )
        chosen_friction = _require_non_negative_int(
            self.chosen_friction_score,
            name="chosen_friction_score",
        )
        best_friction = _require_non_negative_int(
            self.best_friction_score,
            name="best_friction_score",
        )
        friction_delta = _require_non_negative_int(
            self.friction_score_delta,
            name="friction_score_delta",
        )
        friction_threshold = _require_non_negative_int(
            self.friction_score_threshold,
            name="friction_score_threshold",
        )
        if chosen_safety < best_safety:
            raise ValueError("chosen_safety_regret must be >= best_safety_regret")
        if safety_delta != chosen_safety - best_safety:
            raise ValueError("safety_regret_delta must equal chosen - best safety")
        expected_friction_delta = max(0, chosen_friction - best_friction)
        if friction_delta != expected_friction_delta:
            raise ValueError("friction_score_delta must equal positive friction gap")
        regret_ok = _require_bool(self.regret_ok, name="regret_ok")
        expected_ok = (
            safety_delta <= safety_threshold
            and friction_delta <= friction_threshold
        )
        if regret_ok != expected_ok:
            raise ValueError("regret_ok must match minimax thresholds")
        terms = _require_regret_terms(self.top_regret_terms)
        object.__setattr__(self, "top_regret_terms", terms)
        rejected = _require_text_refs(
            self.rejected_candidate_ids,
            name="rejected_candidate_ids",
        )
        object.__setattr__(self, "rejected_candidate_ids", rejected)
        candidate_hashes = _require_hash_refs(
            self.candidate_hashes,
            name="candidate_hashes",
        )
        if not candidate_hashes:
            raise ValueError("candidate_hashes must be non-empty")
        object.__setattr__(self, "candidate_hashes", candidate_hashes)
        evidence = _require_evidence_refs(self.evidence_refs)
        object.__setattr__(self, "evidence_refs", evidence)


def _require_text_id(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    if not value:
        raise ValueError(f"{name} must be non-empty")
    if "\x00" in value:
        raise ValueError(f"{name} must not contain NUL")
    return value


def _require_non_negative_int(value: object, *, name: str) -> int:
    if not is_strict_int(value):
        raise TypeError(f"{name} must be an int")
    out = cast(int, value)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _require_positive_int(value: object, *, name: str) -> int:
    out = _require_non_negative_int(value, name=name)
    if out <= 0:
        raise ValueError(f"{name} must be positive")
    return out


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_bps(value: object, *, name: str) -> int:
    out = _require_non_negative_int(value, name=name)
    if out > _BPS_SCALE:
        raise ValueError(f"{name} must be <= 10000")
    return out


def _require_explanation_code(value: object) -> str:
    out = _require_text_id(value, name="explanation_code")
    if _EXPLANATION_RE.fullmatch(out) is None:
        raise ValueError("explanation_code must be lower snake case")
    return out


def _require_evidence_refs(value: object) -> tuple[str, ...]:
    if isinstance(value, (str, bytes)) or not isinstance(value, Sequence):
        raise TypeError("evidence_refs must be a sequence")
    out: list[str] = []
    seen: set[str] = set()
    for idx, item in enumerate(value):
        ref = _require_text_id(item, name=f"evidence_refs[{idx}]")
        if ref in seen:
            raise ValueError("evidence_refs must be unique")
        seen.add(ref)
        out.append(ref)
    return tuple(out)


def _require_text_refs(value: object, *, name: str) -> tuple[str, ...]:
    if isinstance(value, (str, bytes)) or not isinstance(value, Sequence):
        raise TypeError(f"{name} must be a sequence")
    out: list[str] = []
    seen: set[str] = set()
    for idx, item in enumerate(value):
        ref = _require_text_id(item, name=f"{name}[{idx}]")
        if ref in seen:
            raise ValueError(f"{name} must be unique")
        seen.add(ref)
        out.append(ref)
    return tuple(out)


def _require_hash_refs(value: object, *, name: str) -> tuple[str, ...]:
    if isinstance(value, (str, bytes)) or not isinstance(value, Sequence):
        raise TypeError(f"{name} must be a sequence")
    out: list[str] = []
    seen: set[str] = set()
    for idx, item in enumerate(value):
        ref = _require_text_id(item, name=f"{name}[{idx}]")
        if not ref.startswith("sha256:"):
            raise ValueError(f"{name}[{idx}] must be a sha256 reference")
        if ref in seen:
            raise ValueError(f"{name} must be unique")
        seen.add(ref)
        out.append(ref)
    return tuple(out)


def _require_axes(value: object) -> tuple[str, ...]:
    if isinstance(value, (str, bytes)) or not isinstance(value, Sequence):
        raise TypeError("priority_axes must be a sequence")
    axes: list[str] = []
    seen: set[str] = set()
    for idx, raw in enumerate(value):
        axis = _require_text_id(raw, name=f"priority_axes[{idx}]")
        if axis not in UX_AXES:
            raise ValueError(f"unsupported UX axis: {axis}")
        if axis in seen:
            raise ValueError("priority_axes must be unique")
        seen.add(axis)
        axes.append(axis)
    if not axes:
        raise ValueError("priority_axes must be non-empty")
    return tuple(axes)


def _require_regret_weights(value: object) -> tuple[tuple[str, int], ...]:
    if isinstance(value, Mapping):
        raw_items = tuple(value.items())
    elif isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        raw_items = tuple(value)
    else:
        raise TypeError("weights must be a mapping or sequence of pairs")

    rows: list[tuple[str, int]] = []
    seen: set[str] = set()
    positive_weight = False
    for idx, raw in enumerate(raw_items):
        if not isinstance(raw, Sequence) or isinstance(raw, (str, bytes)):
            raise TypeError(f"weights[{idx}] must be a pair")
        if len(raw) != 2:
            raise ValueError(f"weights[{idx}] must have length 2")
        axis = _require_text_id(raw[0], name=f"weights[{idx}].axis")
        if axis not in REGRET_COST_AXES:
            raise ValueError(f"unsupported regret axis: {axis}")
        if axis in seen:
            raise ValueError("weights must be unique by axis")
        weight = _require_non_negative_int(raw[1], name=f"weights[{idx}].weight")
        positive_weight = positive_weight or weight > 0
        seen.add(axis)
        rows.append((axis, weight))
    if not rows:
        raise ValueError("weights must be non-empty")
    if not positive_weight:
        raise ValueError("at least one regret weight must be positive")
    return tuple(sorted(rows, key=lambda row: row[0]))


def _require_regret_axes(value: object, *, name: str) -> tuple[str, ...]:
    if isinstance(value, (str, bytes)) or not isinstance(value, Sequence):
        raise TypeError(f"{name} must be a sequence")
    axes: list[str] = []
    seen: set[str] = set()
    for idx, raw in enumerate(value):
        axis = _require_text_id(raw, name=f"{name}[{idx}]")
        if axis not in REGRET_COST_AXES:
            raise ValueError(f"unsupported regret axis: {axis}")
        if axis in seen:
            raise ValueError(f"{name} must be unique")
        seen.add(axis)
        axes.append(axis)
    if not axes:
        raise ValueError(f"{name} must be non-empty")
    return tuple(axes)


def _require_regret_bounds(
    value: object,
    *,
    allowed_axes: Sequence[str],
) -> tuple[tuple[str, int], ...]:
    if isinstance(value, Mapping):
        raw_items = tuple(value.items())
    elif isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        raw_items = tuple(value)
    else:
        raise TypeError("safety_budgets must be a mapping or sequence of pairs")

    allowed = set(allowed_axes)
    rows: list[tuple[str, int]] = []
    seen: set[str] = set()
    for idx, raw in enumerate(raw_items):
        if not isinstance(raw, Sequence) or isinstance(raw, (str, bytes)):
            raise TypeError(f"safety_budgets[{idx}] must be a pair")
        if len(raw) != 2:
            raise ValueError(f"safety_budgets[{idx}] must have length 2")
        axis = _require_text_id(raw[0], name=f"safety_budgets[{idx}].axis")
        if axis not in REGRET_COST_AXES:
            raise ValueError(f"unsupported regret axis: {axis}")
        if axis not in allowed:
            raise ValueError("safety_budgets axis must be in safety_axes")
        if axis in seen:
            raise ValueError("safety_budgets must be unique by axis")
        bound = _require_non_negative_int(
            raw[1],
            name=f"safety_budgets[{idx}].bound",
        )
        seen.add(axis)
        rows.append((axis, bound))
    return tuple(sorted(rows, key=lambda row: row[0]))


def _require_regret_terms(value: object) -> tuple[tuple[str, int], ...]:
    if isinstance(value, Mapping):
        raw_items = tuple(value.items())
    elif isinstance(value, Sequence) and not isinstance(value, (str, bytes)):
        raw_items = tuple(value)
    else:
        raise TypeError("top_regret_terms must be a mapping or sequence of pairs")

    rows: list[tuple[str, int]] = []
    seen: set[str] = set()
    for idx, raw in enumerate(raw_items):
        if not isinstance(raw, Sequence) or isinstance(raw, (str, bytes)):
            raise TypeError(f"top_regret_terms[{idx}] must be a pair")
        if len(raw) != 2:
            raise ValueError(f"top_regret_terms[{idx}] must have length 2")
        axis = _require_text_id(raw[0], name=f"top_regret_terms[{idx}].axis")
        if axis not in REGRET_COST_AXES:
            raise ValueError(f"unsupported regret axis: {axis}")
        if axis in seen:
            raise ValueError("top_regret_terms must be unique by axis")
        score = _require_positive_int(
            raw[1],
            name=f"top_regret_terms[{idx}].score",
        )
        seen.add(axis)
        rows.append((axis, score))
    return tuple(rows)


def _require_payload(payload: object) -> Mapping[str, object]:
    if not isinstance(payload, Mapping):
        raise TypeError("payload must be an object")
    return payload


def _regret_policy_weights(
    policy: ZenoUXRegretPolicy,
) -> tuple[tuple[str, int], ...]:
    return cast(tuple[tuple[str, int], ...], policy.weights)


def _minimax_safety_axes(policy: ZenoUXMinimaxRegretPolicy) -> tuple[str, ...]:
    return cast(tuple[str, ...], policy.safety_axes)


def _minimax_safety_budgets(
    policy: ZenoUXMinimaxRegretPolicy,
) -> tuple[tuple[str, int], ...]:
    return cast(tuple[tuple[str, int], ...], policy.safety_budgets)


def _minimax_friction_weights(
    policy: ZenoUXMinimaxRegretPolicy,
) -> tuple[tuple[str, int], ...]:
    return cast(tuple[tuple[str, int], ...], policy.friction_weights)


def _axis_value(certificate: ZenoUXCertificate, axis: str) -> int:
    if axis == "decision_rank":
        return int(DECISION_CLASS_RANK[certificate.decision_class])
    if axis not in LOWER_IS_BETTER_AXES:
        raise ValueError(f"unsupported UX axis: {axis}")
    return int(getattr(certificate, axis))


def _axis_no_worse(left: ZenoUXCertificate, right: ZenoUXCertificate, axis: str) -> bool:
    left_value = _axis_value(left, axis)
    right_value = _axis_value(right, axis)
    if axis in HIGHER_IS_BETTER_AXES:
        return left_value >= right_value
    return left_value <= right_value


def _axis_strictly_better(left: ZenoUXCertificate, right: ZenoUXCertificate, axis: str) -> bool:
    left_value = _axis_value(left, axis)
    right_value = _axis_value(right, axis)
    if axis in HIGHER_IS_BETTER_AXES:
        return left_value > right_value
    return left_value < right_value


def _same_scope(left: ZenoUXCertificate, right: ZenoUXCertificate) -> bool:
    return left.surface == right.surface and left.scenario_id == right.scenario_id


def compare_zeno_ux(
    left: ZenoUXCertificate,
    right: ZenoUXCertificate,
    *,
    axes: Sequence[str] = DEFAULT_POLICY_AXES,
) -> ZenoUXComparison:
    checked_axes = _require_axes(tuple(axes))
    if not _same_scope(left, right):
        return ZenoUXComparison(
            relation="incomparable",
            better_axes=(),
            worse_axes=(),
            reasons=("different_scope",),
        )

    left_better = tuple(
        axis for axis in checked_axes if _axis_strictly_better(left, right, axis)
    )
    right_better = tuple(
        axis for axis in checked_axes if _axis_strictly_better(right, left, axis)
    )
    left_no_worse = all(_axis_no_worse(left, right, axis) for axis in checked_axes)
    right_no_worse = all(_axis_no_worse(right, left, axis) for axis in checked_axes)

    if left_no_worse and right_no_worse:
        return ZenoUXComparison("equivalent", (), (), ())
    if left_no_worse and left_better:
        return ZenoUXComparison("dominates", left_better, (), ())
    if right_no_worse and right_better:
        return ZenoUXComparison("dominated_by", (), right_better, ())
    return ZenoUXComparison(
        relation="incomparable",
        better_axes=left_better,
        worse_axes=right_better,
        reasons=("tradeoff",),
    )


def pareto_frontier_zeno_ux(
    certificates: Iterable[ZenoUXCertificate],
    *,
    axes: Sequence[str] = DEFAULT_POLICY_AXES,
) -> tuple[ZenoUXCertificate, ...]:
    items = tuple(certificates)
    if not items:
        return ()
    _require_same_scope(items)
    frontier: list[ZenoUXCertificate] = []
    for candidate in items:
        dominated = False
        for other in items:
            if other is candidate:
                continue
            if compare_zeno_ux(other, candidate, axes=axes).relation == "dominates":
                dominated = True
                break
        if not dominated:
            frontier.append(candidate)
    return tuple(sorted(frontier, key=lambda cert: cert.certificate_id))


def choose_zeno_ux_certificate(
    certificates: Iterable[ZenoUXCertificate],
    *,
    policy: ZenoUXPolicy | None = None,
) -> ZenoUXCertificate:
    items = tuple(certificates)
    if not items:
        raise ValueError("certificates must be non-empty")
    _require_same_scope(items)
    active_policy = policy or ZenoUXPolicy(
        schema=POLICY_SCHEMA,
        policy_id="default_trade_ux",
    )
    return min(items, key=lambda cert: _policy_sort_key(cert, active_policy))


def choose_min_regret_zeno_ux_certificate(
    certificates: Iterable[ZenoUXCertificate],
    *,
    policy: ZenoUXRegretPolicy | None = None,
) -> ZenoUXCertificate:
    items = tuple(certificates)
    if not items:
        raise ValueError("certificates must be non-empty")
    _require_same_scope(items)
    active_policy = policy or ZenoUXRegretPolicy(
        schema=REGRET_POLICY_SCHEMA,
        policy_id="default_regret_ux",
    )
    return min(
        items,
        key=lambda cert: (
            zeno_ux_regret_score(cert, policy=active_policy),
            cert.certificate_id,
        ),
    )


def choose_minimax_regret_zeno_ux_certificate(
    certificates: Iterable[ZenoUXCertificate],
    *,
    policy: ZenoUXMinimaxRegretPolicy | None = None,
) -> ZenoUXCertificate:
    items = tuple(certificates)
    if not items:
        raise ValueError("certificates must be non-empty")
    _require_same_scope(items)
    active_policy = policy or ZenoUXMinimaxRegretPolicy(
        schema=MINIMAX_REGRET_POLICY_SCHEMA,
        policy_id="default_minimax_regret_ux",
    )
    admissible = tuple(
        cert for cert in items if not _violated_safety_budgets(cert, active_policy)
    )
    if not admissible:
        raise ValueError("no admissible Zeno UX candidates under safety budgets")
    return min(
        admissible,
        key=lambda cert: _minimax_policy_sort_key(cert, active_policy),
    )


def build_zeno_ux_regret_certificate(
    certificates: Iterable[ZenoUXCertificate],
    *,
    chosen_certificate_id: str,
    policy: ZenoUXRegretPolicy | None = None,
    certificate_id: str | None = None,
    evidence_refs: Sequence[str] = (),
) -> ZenoUXRegretCertificate:
    items = tuple(certificates)
    if not items:
        raise ValueError("certificates must be non-empty")
    _require_same_scope(items)
    chosen_id = _require_text_id(
        chosen_certificate_id,
        name="chosen_certificate_id",
    )
    active_policy = policy or ZenoUXRegretPolicy(
        schema=REGRET_POLICY_SCHEMA,
        policy_id="default_regret_ux",
    )
    chosen = _find_certificate_by_id(items, chosen_id)
    best = choose_min_regret_zeno_ux_certificate(items, policy=active_policy)
    chosen_score = zeno_ux_regret_score(chosen, policy=active_policy)
    best_score = zeno_ux_regret_score(best, policy=active_policy)
    regret_score = int(chosen_score - best_score)
    cert_id = certificate_id or (
        f"{active_policy.policy_id}:{chosen.surface}:{chosen.scenario_id}:"
        f"{chosen.certificate_id}:regret"
    )
    return ZenoUXRegretCertificate(
        schema=REGRET_CERT_SCHEMA,
        certificate_id=cert_id,
        policy_id=active_policy.policy_id,
        surface=chosen.surface,
        scenario_id=chosen.scenario_id,
        chosen_certificate_id=chosen.certificate_id,
        best_certificate_id=best.certificate_id,
        chosen_score=chosen_score,
        best_score=best_score,
        regret_score=regret_score,
        regret_threshold=active_policy.max_regret_score,
        regret_ok=regret_score <= active_policy.max_regret_score,
        top_regret_terms=_top_regret_terms(
            chosen,
            best,
            policy=active_policy,
        ),
        candidate_hashes=tuple(
            sorted(zeno_ux_certificate_hash(cert) for cert in items)
        ),
        evidence_refs=tuple(evidence_refs),
    )


def build_zeno_ux_minimax_regret_certificate(
    certificates: Iterable[ZenoUXCertificate],
    *,
    chosen_certificate_id: str,
    policy: ZenoUXMinimaxRegretPolicy | None = None,
    certificate_id: str | None = None,
    evidence_refs: Sequence[str] = (),
) -> ZenoUXMinimaxRegretCertificate:
    items = tuple(certificates)
    if not items:
        raise ValueError("certificates must be non-empty")
    _require_same_scope(items)
    chosen_id = _require_text_id(
        chosen_certificate_id,
        name="chosen_certificate_id",
    )
    active_policy = policy or ZenoUXMinimaxRegretPolicy(
        schema=MINIMAX_REGRET_POLICY_SCHEMA,
        policy_id="default_minimax_regret_ux",
    )
    chosen = _find_certificate_by_id(items, chosen_id)
    best = choose_minimax_regret_zeno_ux_certificate(items, policy=active_policy)
    chosen_safety = _minimax_safety_regret(chosen, active_policy)
    best_safety = _minimax_safety_regret(best, active_policy)
    chosen_friction = _minimax_friction_score(chosen, active_policy)
    best_friction = _minimax_friction_score(best, active_policy)
    safety_delta = int(chosen_safety - best_safety)
    friction_delta = int(max(0, chosen_friction - best_friction))
    cert_id = certificate_id or (
        f"{active_policy.policy_id}:{chosen.surface}:{chosen.scenario_id}:"
        f"{chosen.certificate_id}:minimax_regret"
    )
    return ZenoUXMinimaxRegretCertificate(
        schema=MINIMAX_REGRET_CERT_SCHEMA,
        certificate_id=cert_id,
        policy_id=active_policy.policy_id,
        surface=chosen.surface,
        scenario_id=chosen.scenario_id,
        chosen_certificate_id=chosen.certificate_id,
        best_certificate_id=best.certificate_id,
        chosen_safety_regret=chosen_safety,
        best_safety_regret=best_safety,
        safety_regret_delta=safety_delta,
        safety_regret_threshold=active_policy.max_safety_regret,
        chosen_friction_score=chosen_friction,
        best_friction_score=best_friction,
        friction_score_delta=friction_delta,
        friction_score_threshold=active_policy.max_friction_score,
        regret_ok=(
            safety_delta <= active_policy.max_safety_regret
            and friction_delta <= active_policy.max_friction_score
        ),
        top_regret_terms=_top_minimax_regret_terms(
            chosen,
            best,
            policy=active_policy,
        ),
        rejected_candidate_ids=tuple(
            sorted(
                cert.certificate_id
                for cert in items
                if _violated_safety_budgets(cert, active_policy)
            )
        ),
        candidate_hashes=tuple(
            sorted(zeno_ux_certificate_hash(cert) for cert in items)
        ),
        evidence_refs=tuple(evidence_refs),
    )


def _require_same_scope(certificates: Sequence[ZenoUXCertificate]) -> None:
    first = certificates[0]
    for cert in certificates[1:]:
        if not _same_scope(first, cert):
            raise ValueError("Zeno UX certificates must share surface and scenario_id")


def _find_certificate_by_id(
    certificates: Sequence[ZenoUXCertificate],
    certificate_id: str,
) -> ZenoUXCertificate:
    matches = tuple(
        cert for cert in certificates if cert.certificate_id == certificate_id
    )
    if len(matches) != 1:
        raise ValueError("chosen_certificate_id must identify exactly one certificate")
    return matches[0]


def _policy_sort_key(
    certificate: ZenoUXCertificate,
    policy: ZenoUXPolicy,
) -> tuple[int | str, ...]:
    values: list[int | str] = []
    for axis in policy.priority_axes:
        value = _axis_value(certificate, axis)
        values.append(-value if axis in HIGHER_IS_BETTER_AXES else value)
    values.append(certificate.certificate_id)
    return tuple(values)


def _regret_axis_cost(certificate: ZenoUXCertificate, axis: str) -> int:
    if axis == "decision_uncertainty":
        return int(
            _MAX_DECISION_RANK - DECISION_CLASS_RANK[certificate.decision_class]
        )
    if axis in LOWER_IS_BETTER_AXES:
        return _axis_value(certificate, axis)
    raise ValueError(f"unsupported regret axis: {axis}")


def zeno_ux_regret_cost_terms(
    certificate: ZenoUXCertificate,
    *,
    policy: ZenoUXRegretPolicy | None = None,
) -> dict[str, int]:
    active_policy = policy or ZenoUXRegretPolicy(
        schema=REGRET_POLICY_SCHEMA,
        policy_id="default_regret_ux",
    )
    return {
        axis: _regret_axis_cost(certificate, axis)
        for axis, weight in _regret_policy_weights(active_policy)
        if weight > 0
    }


def zeno_ux_regret_score(
    certificate: ZenoUXCertificate,
    *,
    policy: ZenoUXRegretPolicy | None = None,
) -> int:
    active_policy = policy or ZenoUXRegretPolicy(
        schema=REGRET_POLICY_SCHEMA,
        policy_id="default_regret_ux",
    )
    return int(
        sum(
            _regret_axis_cost(certificate, axis) * weight
            for axis, weight in _regret_policy_weights(active_policy)
        )
    )


def _minimax_safety_regret(
    certificate: ZenoUXCertificate,
    policy: ZenoUXMinimaxRegretPolicy,
) -> int:
    base = max(
        _regret_axis_cost(certificate, axis)
        for axis in _minimax_safety_axes(policy)
    )
    violation_excess = max(
        (
            _regret_axis_cost(certificate, axis) - bound
            for axis, bound in _minimax_safety_budgets(policy)
            if _regret_axis_cost(certificate, axis) > bound
        ),
        default=0,
    )
    if violation_excess == 0:
        return base
    return _MINIMAX_BUDGET_VIOLATION_PENALTY + base + violation_excess


def _minimax_friction_score(
    certificate: ZenoUXCertificate,
    policy: ZenoUXMinimaxRegretPolicy,
) -> int:
    return int(
        sum(
            _regret_axis_cost(certificate, axis) * weight
            for axis, weight in _minimax_friction_weights(policy)
        )
    )


def _violated_safety_budgets(
    certificate: ZenoUXCertificate,
    policy: ZenoUXMinimaxRegretPolicy,
) -> tuple[str, ...]:
    return tuple(
        axis
        for axis, bound in _minimax_safety_budgets(policy)
        if _regret_axis_cost(certificate, axis) > bound
    )


def _minimax_policy_sort_key(
    certificate: ZenoUXCertificate,
    policy: ZenoUXMinimaxRegretPolicy,
) -> tuple[int | str, ...]:
    safety_regret = _minimax_safety_regret(certificate, policy)
    safety_vector = tuple(
        _regret_axis_cost(certificate, axis)
        for axis in _minimax_safety_axes(policy)
    )
    return (
        safety_regret,
        *safety_vector,
        _minimax_friction_score(certificate, policy),
        certificate.certificate_id,
    )


def _top_regret_terms(
    chosen: ZenoUXCertificate,
    best: ZenoUXCertificate,
    *,
    policy: ZenoUXRegretPolicy,
) -> tuple[tuple[str, int], ...]:
    terms: list[tuple[str, int]] = []
    for axis, weight in _regret_policy_weights(policy):
        if weight == 0:
            continue
        delta = _regret_axis_cost(chosen, axis) - _regret_axis_cost(best, axis)
        contribution = delta * weight
        if contribution > 0:
            terms.append((axis, int(contribution)))
    terms.sort(key=lambda row: (-row[1], row[0]))
    return tuple(terms[: policy.top_term_count])


def _top_minimax_regret_terms(
    chosen: ZenoUXCertificate,
    best: ZenoUXCertificate,
    *,
    policy: ZenoUXMinimaxRegretPolicy,
) -> tuple[tuple[str, int], ...]:
    terms: list[tuple[str, int]] = []
    for axis in _minimax_safety_axes(policy):
        delta = _regret_axis_cost(chosen, axis) - _regret_axis_cost(best, axis)
        if delta > 0:
            terms.append((axis, int(delta)))
    for axis, weight in _minimax_friction_weights(policy):
        delta = _regret_axis_cost(chosen, axis) - _regret_axis_cost(best, axis)
        contribution = delta * weight
        if contribution > 0:
            terms.append((axis, int(contribution)))
    terms.sort(key=lambda row: (-row[1], row[0]))
    return tuple(terms[: policy.top_term_count])


def zeno_ux_certificate_to_payload(certificate: ZenoUXCertificate) -> dict[str, object]:
    return {
        "schema": certificate.schema,
        "certificate_id": certificate.certificate_id,
        "surface": certificate.surface,
        "scenario_id": certificate.scenario_id,
        "decision_class": certificate.decision_class,
        "latency_bound_ms": certificate.latency_bound_ms,
        "value_loss_bound_bps": certificate.value_loss_bound_bps,
        "mev_exposure_bound_bps": certificate.mev_exposure_bound_bps,
        "finality_bound_blocks": certificate.finality_bound_blocks,
        "capital_at_risk_bps": certificate.capital_at_risk_bps,
        "privacy_leakage_bits": certificate.privacy_leakage_bits,
        "cognitive_steps": certificate.cognitive_steps,
        "explanation_code": certificate.explanation_code,
        "next_action": certificate.next_action,
        "evidence_refs": list(certificate.evidence_refs),
    }


def zeno_ux_certificate_from_payload(payload: object) -> ZenoUXCertificate:
    data = _require_payload(payload)
    return ZenoUXCertificate(
        schema=_require_text_id(data.get("schema"), name="schema"),
        certificate_id=_require_text_id(data.get("certificate_id"), name="certificate_id"),
        surface=_require_text_id(data.get("surface"), name="surface"),
        scenario_id=_require_text_id(data.get("scenario_id"), name="scenario_id"),
        decision_class=_require_text_id(data.get("decision_class"), name="decision_class"),
        latency_bound_ms=_require_non_negative_int(
            data.get("latency_bound_ms"),
            name="latency_bound_ms",
        ),
        value_loss_bound_bps=_require_bps(
            data.get("value_loss_bound_bps"),
            name="value_loss_bound_bps",
        ),
        mev_exposure_bound_bps=_require_bps(
            data.get("mev_exposure_bound_bps"),
            name="mev_exposure_bound_bps",
        ),
        finality_bound_blocks=_require_non_negative_int(
            data.get("finality_bound_blocks"),
            name="finality_bound_blocks",
        ),
        capital_at_risk_bps=_require_bps(
            data.get("capital_at_risk_bps"),
            name="capital_at_risk_bps",
        ),
        privacy_leakage_bits=_require_non_negative_int(
            data.get("privacy_leakage_bits"),
            name="privacy_leakage_bits",
        ),
        cognitive_steps=_require_non_negative_int(
            data.get("cognitive_steps"),
            name="cognitive_steps",
        ),
        explanation_code=_require_text_id(
            data.get("explanation_code"),
            name="explanation_code",
        ),
        next_action=_require_text_id(data.get("next_action"), name="next_action"),
        evidence_refs=_require_evidence_refs(data.get("evidence_refs")),
    )


def zeno_ux_regret_policy_to_payload(policy: ZenoUXRegretPolicy) -> dict[str, object]:
    return {
        "schema": policy.schema,
        "policy_id": policy.policy_id,
        "weights": {
            axis: weight for axis, weight in _regret_policy_weights(policy)
        },
        "max_regret_score": policy.max_regret_score,
        "top_term_count": policy.top_term_count,
    }


def zeno_ux_regret_policy_from_payload(payload: object) -> ZenoUXRegretPolicy:
    data = _require_payload(payload)
    return ZenoUXRegretPolicy(
        schema=_require_text_id(data.get("schema"), name="schema"),
        policy_id=_require_text_id(data.get("policy_id"), name="policy_id"),
        weights=data.get("weights"),
        max_regret_score=_require_non_negative_int(
            data.get("max_regret_score"),
            name="max_regret_score",
        ),
        top_term_count=_require_positive_int(
            data.get("top_term_count"),
            name="top_term_count",
        ),
    )


def zeno_ux_regret_certificate_to_payload(
    certificate: ZenoUXRegretCertificate,
) -> dict[str, object]:
    return {
        "schema": certificate.schema,
        "certificate_id": certificate.certificate_id,
        "policy_id": certificate.policy_id,
        "surface": certificate.surface,
        "scenario_id": certificate.scenario_id,
        "chosen_certificate_id": certificate.chosen_certificate_id,
        "best_certificate_id": certificate.best_certificate_id,
        "chosen_score": certificate.chosen_score,
        "best_score": certificate.best_score,
        "regret_score": certificate.regret_score,
        "regret_threshold": certificate.regret_threshold,
        "regret_ok": certificate.regret_ok,
        "top_regret_terms": [
            [axis, score] for axis, score in certificate.top_regret_terms
        ],
        "candidate_hashes": list(certificate.candidate_hashes),
        "evidence_refs": list(certificate.evidence_refs),
    }


def zeno_ux_regret_certificate_from_payload(
    payload: object,
) -> ZenoUXRegretCertificate:
    data = _require_payload(payload)
    return ZenoUXRegretCertificate(
        schema=_require_text_id(data.get("schema"), name="schema"),
        certificate_id=_require_text_id(data.get("certificate_id"), name="certificate_id"),
        policy_id=_require_text_id(data.get("policy_id"), name="policy_id"),
        surface=_require_text_id(data.get("surface"), name="surface"),
        scenario_id=_require_text_id(data.get("scenario_id"), name="scenario_id"),
        chosen_certificate_id=_require_text_id(
            data.get("chosen_certificate_id"),
            name="chosen_certificate_id",
        ),
        best_certificate_id=_require_text_id(
            data.get("best_certificate_id"),
            name="best_certificate_id",
        ),
        chosen_score=_require_non_negative_int(
            data.get("chosen_score"),
            name="chosen_score",
        ),
        best_score=_require_non_negative_int(
            data.get("best_score"),
            name="best_score",
        ),
        regret_score=_require_non_negative_int(
            data.get("regret_score"),
            name="regret_score",
        ),
        regret_threshold=_require_non_negative_int(
            data.get("regret_threshold"),
            name="regret_threshold",
        ),
        regret_ok=_require_bool(data.get("regret_ok"), name="regret_ok"),
        top_regret_terms=_require_regret_terms(data.get("top_regret_terms")),
        candidate_hashes=_require_hash_refs(
            data.get("candidate_hashes"),
            name="candidate_hashes",
        ),
        evidence_refs=_require_evidence_refs(data.get("evidence_refs")),
    )


def zeno_ux_minimax_regret_policy_to_payload(
    policy: ZenoUXMinimaxRegretPolicy,
) -> dict[str, object]:
    return {
        "schema": policy.schema,
        "policy_id": policy.policy_id,
        "safety_axes": list(_minimax_safety_axes(policy)),
        "safety_budgets": {
            axis: bound for axis, bound in _minimax_safety_budgets(policy)
        },
        "friction_weights": {
            axis: weight for axis, weight in _minimax_friction_weights(policy)
        },
        "max_safety_regret": policy.max_safety_regret,
        "max_friction_score": policy.max_friction_score,
        "top_term_count": policy.top_term_count,
    }


def zeno_ux_minimax_regret_policy_from_payload(
    payload: object,
) -> ZenoUXMinimaxRegretPolicy:
    data = _require_payload(payload)
    return ZenoUXMinimaxRegretPolicy(
        schema=_require_text_id(data.get("schema"), name="schema"),
        policy_id=_require_text_id(data.get("policy_id"), name="policy_id"),
        safety_axes=data.get("safety_axes"),
        safety_budgets=data.get("safety_budgets"),
        friction_weights=data.get("friction_weights"),
        max_safety_regret=_require_non_negative_int(
            data.get("max_safety_regret"),
            name="max_safety_regret",
        ),
        max_friction_score=_require_non_negative_int(
            data.get("max_friction_score"),
            name="max_friction_score",
        ),
        top_term_count=_require_positive_int(
            data.get("top_term_count"),
            name="top_term_count",
        ),
    )


def zeno_ux_minimax_regret_certificate_to_payload(
    certificate: ZenoUXMinimaxRegretCertificate,
) -> dict[str, object]:
    return {
        "schema": certificate.schema,
        "certificate_id": certificate.certificate_id,
        "policy_id": certificate.policy_id,
        "surface": certificate.surface,
        "scenario_id": certificate.scenario_id,
        "chosen_certificate_id": certificate.chosen_certificate_id,
        "best_certificate_id": certificate.best_certificate_id,
        "chosen_safety_regret": certificate.chosen_safety_regret,
        "best_safety_regret": certificate.best_safety_regret,
        "safety_regret_delta": certificate.safety_regret_delta,
        "safety_regret_threshold": certificate.safety_regret_threshold,
        "chosen_friction_score": certificate.chosen_friction_score,
        "best_friction_score": certificate.best_friction_score,
        "friction_score_delta": certificate.friction_score_delta,
        "friction_score_threshold": certificate.friction_score_threshold,
        "regret_ok": certificate.regret_ok,
        "top_regret_terms": [
            [axis, score] for axis, score in certificate.top_regret_terms
        ],
        "rejected_candidate_ids": list(certificate.rejected_candidate_ids),
        "candidate_hashes": list(certificate.candidate_hashes),
        "evidence_refs": list(certificate.evidence_refs),
    }


def zeno_ux_minimax_regret_certificate_from_payload(
    payload: object,
) -> ZenoUXMinimaxRegretCertificate:
    data = _require_payload(payload)
    return ZenoUXMinimaxRegretCertificate(
        schema=_require_text_id(data.get("schema"), name="schema"),
        certificate_id=_require_text_id(data.get("certificate_id"), name="certificate_id"),
        policy_id=_require_text_id(data.get("policy_id"), name="policy_id"),
        surface=_require_text_id(data.get("surface"), name="surface"),
        scenario_id=_require_text_id(data.get("scenario_id"), name="scenario_id"),
        chosen_certificate_id=_require_text_id(
            data.get("chosen_certificate_id"),
            name="chosen_certificate_id",
        ),
        best_certificate_id=_require_text_id(
            data.get("best_certificate_id"),
            name="best_certificate_id",
        ),
        chosen_safety_regret=_require_non_negative_int(
            data.get("chosen_safety_regret"),
            name="chosen_safety_regret",
        ),
        best_safety_regret=_require_non_negative_int(
            data.get("best_safety_regret"),
            name="best_safety_regret",
        ),
        safety_regret_delta=_require_non_negative_int(
            data.get("safety_regret_delta"),
            name="safety_regret_delta",
        ),
        safety_regret_threshold=_require_non_negative_int(
            data.get("safety_regret_threshold"),
            name="safety_regret_threshold",
        ),
        chosen_friction_score=_require_non_negative_int(
            data.get("chosen_friction_score"),
            name="chosen_friction_score",
        ),
        best_friction_score=_require_non_negative_int(
            data.get("best_friction_score"),
            name="best_friction_score",
        ),
        friction_score_delta=_require_non_negative_int(
            data.get("friction_score_delta"),
            name="friction_score_delta",
        ),
        friction_score_threshold=_require_non_negative_int(
            data.get("friction_score_threshold"),
            name="friction_score_threshold",
        ),
        regret_ok=_require_bool(data.get("regret_ok"), name="regret_ok"),
        top_regret_terms=_require_regret_terms(data.get("top_regret_terms")),
        rejected_candidate_ids=_require_text_refs(
            data.get("rejected_candidate_ids"),
            name="rejected_candidate_ids",
        ),
        candidate_hashes=_require_hash_refs(
            data.get("candidate_hashes"),
            name="candidate_hashes",
        ),
        evidence_refs=_require_evidence_refs(data.get("evidence_refs")),
    )


def zeno_ux_certificate_hash(certificate: ZenoUXCertificate) -> str:
    payload = zeno_ux_certificate_to_payload(certificate)
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def zeno_ux_regret_certificate_hash(certificate: ZenoUXRegretCertificate) -> str:
    payload = zeno_ux_regret_certificate_to_payload(certificate)
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def zeno_ux_minimax_regret_certificate_hash(
    certificate: ZenoUXMinimaxRegretCertificate,
) -> str:
    payload = zeno_ux_minimax_regret_certificate_to_payload(certificate)
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def zeno_ux_status_label(certificate: ZenoUXCertificate) -> str:
    return str(certificate.decision_class).upper()


def zeno_ux_from_cow_quality(
    *,
    certificate_id: str,
    scenario_id: str,
    achieved_netted_volume: int,
    upper_bound: int,
    latency_bound_ms: int,
    finality_bound_blocks: int,
    evidence_refs: Sequence[str],
    mev_exposure_bound_bps: int = 0,
    capital_at_risk_bps: int = 0,
    privacy_leakage_bits: int = 0,
    cognitive_steps: int = 1,
) -> ZenoUXCertificate:
    achieved = _require_non_negative_int(
        achieved_netted_volume,
        name="achieved_netted_volume",
    )
    bound = _require_non_negative_int(upper_bound, name="upper_bound")
    if achieved > bound:
        raise ValueError("achieved_netted_volume exceeds upper_bound")
    quality_floor_bps = _BPS_SCALE if bound == 0 else int(achieved * _BPS_SCALE // bound)
    value_loss_bound_bps = int(_BPS_SCALE - quality_floor_bps)
    decision_class = "exact" if value_loss_bound_bps == 0 else "certified_approx"
    explanation = (
        "cow_exact_quality"
        if decision_class == "exact"
        else "cow_certified_approx_quality"
    )
    next_action = "settle" if decision_class == "exact" else "show_quality_floor"
    return ZenoUXCertificate(
        schema=CERT_SCHEMA,
        certificate_id=certificate_id,
        surface="cow_trade",
        scenario_id=scenario_id,
        decision_class=decision_class,
        latency_bound_ms=latency_bound_ms,
        value_loss_bound_bps=value_loss_bound_bps,
        mev_exposure_bound_bps=mev_exposure_bound_bps,
        finality_bound_blocks=finality_bound_blocks,
        capital_at_risk_bps=capital_at_risk_bps,
        privacy_leakage_bits=privacy_leakage_bits,
        cognitive_steps=cognitive_steps,
        explanation_code=explanation,
        next_action=next_action,
        evidence_refs=tuple(evidence_refs),
    )
