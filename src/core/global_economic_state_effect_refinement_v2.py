"""Exact global state/effect refinement for GlobalSettlementABI V2.

The checker owns and compares one candidate epoch endpoint.  It creates an
opaque structural witness only after lane roots, economic rows, per-asset
conservation, replay, terminal liabilities, and Oracle occurrences agree.
It verifies no proof and grants no publication or settlement authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Final

from .global_economic_proof_v2 import (
    EconomicCommandOccurrenceV2,
    _snapshot_occurrence_v2,
)
from .global_economic_refinement_checks_v2 import (
    require_global_economic_tables_v2,
    require_global_oracle_refinement_v2,
    require_global_terminal_refinement_v2,
)
from .global_economic_state_v2 import (
    GlobalEconomicStateV2,
    ReplayStateV2,
    snapshot_global_economic_state_v2,
)
from .global_settlement_types_v2 import (
    MAX_U64_V2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    hash_global_v2,
)

GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V2: Final = (
    "zenodex/global-economic-state-effect-refinement/v2"
)
GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_AUTHORITY_V2: Final = "NONE"

_REFINEMENT_TOKEN_V2 = object()


@dataclass(frozen=True, slots=True)
class GlobalEconomicStateEffectRefinementCandidateV2:
    pre_state: GlobalEconomicStateV2
    post_state: GlobalEconomicStateV2
    effect_plan: GlobalEconomicEffectPlanV2
    consumed_occurrences: tuple[EconomicCommandOccurrenceV2, ...]
    terminal_plan: GlobalTerminalObligationPlanV2
    oracle_plan: GlobalOracleOccurrencePlanV2

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "pre_state",
            snapshot_global_economic_state_v2(self.pre_state),
        )
        object.__setattr__(
            self,
            "post_state",
            snapshot_global_economic_state_v2(self.post_state),
        )
        if type(self.effect_plan) is not GlobalEconomicEffectPlanV2:
            raise TypeError("global refinement effect plan must be exact")
        object.__setattr__(self, "effect_plan", replace(self.effect_plan))
        if type(self.consumed_occurrences) is not tuple or any(
            type(item) is not EconomicCommandOccurrenceV2
            for item in self.consumed_occurrences
        ):
            raise TypeError("global refinement occurrences must be an exact typed tuple")
        object.__setattr__(
            self,
            "consumed_occurrences",
            tuple(_snapshot_occurrence_v2(item) for item in self.consumed_occurrences),
        )
        if type(self.terminal_plan) is not GlobalTerminalObligationPlanV2:
            raise TypeError("global refinement terminal plan must be exact")
        if type(self.oracle_plan) is not GlobalOracleOccurrencePlanV2:
            raise TypeError("global refinement Oracle plan must be exact")
        object.__setattr__(self, "terminal_plan", replace(self.terminal_plan))
        object.__setattr__(self, "oracle_plan", replace(self.oracle_plan))


@dataclass(frozen=True, slots=True)
class _RefinementFieldsV2:
    pre_state_root: str
    post_state_root: str
    effect_plan_root: str
    terminal_plan_root: str
    oracle_plan_root: str
    state_delta_root: str


class GlobalEconomicStateEffectRefinementV2:
    """Opaque witness constructed only by the exact refinement checker."""

    _fields: _RefinementFieldsV2
    __slots__ = ("_fields",)

    def __init__(self, token: object, fields: _RefinementFieldsV2) -> None:
        if token is not _REFINEMENT_TOKEN_V2:
            raise TypeError("global ABI V2 refinement is checker-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("global ABI V2 refinement is immutable")

    @property
    def pre_state_root(self) -> str:
        return self._fields.pre_state_root

    @property
    def post_state_root(self) -> str:
        return self._fields.post_state_root

    @property
    def effect_plan_root(self) -> str:
        return self._fields.effect_plan_root

    @property
    def terminal_plan_root(self) -> str:
        return self._fields.terminal_plan_root

    @property
    def oracle_plan_root(self) -> str:
        return self._fields.oracle_plan_root

    @property
    def state_delta_root(self) -> str:
        return self._fields.state_delta_root

    @property
    def production_authority(self) -> str:
        return GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_AUTHORITY_V2

    @property
    def refinement_root(self) -> str:
        return hash_global_v2(
            "global-economic-state-effect-refinement-v2",
            {
                "schema": GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V2,
                "pre_state_root": self.pre_state_root,
                "post_state_root": self.post_state_root,
                "effect_plan_root": self.effect_plan_root,
                "terminal_plan_root": self.terminal_plan_root,
                "oracle_plan_root": self.oracle_plan_root,
                "state_delta_root": self.state_delta_root,
            },
        )


def _require_fixed_context_v2(
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
) -> None:
    for field_name in (
        "chain_id",
        "deployment_root",
        "writer_epoch",
        "profile_root",
        "history_root",
        "outbox",
    ):
        if getattr(pre_state, field_name) != getattr(post_state, field_name):
            raise ValueError("global refinement fixed context changed")


def _require_lane_refinement_v2(
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
) -> None:
    pre = {row.lane_id: row for row in pre_state.lane_roots}
    post = {row.lane_id: row for row in post_state.lane_roots}
    if any(
        (pre[lane].module_release_id, pre[lane].enabled)
        != (post[lane].module_release_id, post[lane].enabled)
        for lane in pre
    ):
        raise ValueError("global refinement lane ownership changed outside migration")
    changed = {
        lane
        for lane in pre
        if pre[lane].state_root != post[lane].state_root
    }
    writes = {row.lane_id: row for row in effect_plan.lane_writes}
    if set(writes) != changed:
        raise ValueError("global refinement lane write coverage mismatch")
    if any(
        (writes[lane].pre_root, writes[lane].post_root)
        != (pre[lane].state_root, post[lane].state_root)
        for lane in changed
    ):
        raise ValueError("global refinement lane write root mismatch")


def _require_replay_refinement_v2(
    candidate: GlobalEconomicStateEffectRefinementCandidateV2,
) -> tuple[ReplayStateV2, ...]:
    occurrences = candidate.consumed_occurrences
    occurrence_ids = tuple(item.occurrence_id for item in occurrences)
    if occurrence_ids != tuple(sorted(set(occurrence_ids))):
        raise ValueError("global refinement occurrences must be ordered and unique")
    if candidate.effect_plan.occurrence_consumptions != occurrence_ids:
        raise ValueError("global refinement replay consumption mismatch")
    expected = {row.replay_id: row for row in candidate.pre_state.replay_state}
    existing_occurrences = {row.occurrence_id for row in expected.values()}
    for occurrence in occurrences:
        if (
            occurrence.chain_id != candidate.pre_state.chain_id
            or occurrence.deployment_root != candidate.pre_state.deployment_root
            or occurrence.profile_root != candidate.pre_state.profile_root
            or occurrence.pre_state_root != candidate.pre_state.state_root
        ):
            raise ValueError("global refinement occurrence context mismatch")
        if occurrence.replay_id in expected or occurrence.occurrence_id in existing_occurrences:
            raise ValueError("global refinement replay already consumed")
        expected[occurrence.replay_id] = ReplayStateV2(
            occurrence.replay_id,
            occurrence.occurrence_id,
        )
        existing_occurrences.add(occurrence.occurrence_id)
    expected_rows = tuple(expected[key] for key in sorted(expected))
    if candidate.post_state.replay_state != expected_rows:
        raise ValueError("global refinement replay post-state mismatch")
    expected_height = candidate.pre_state.height + int(bool(occurrences))
    if expected_height > MAX_U64_V2 or candidate.post_state.height != expected_height:
        raise ValueError("global refinement height progression mismatch")
    if any(item.height != candidate.post_state.height for item in occurrences):
        raise ValueError("global refinement occurrence height mismatch")
    return tuple(
        ReplayStateV2(item.replay_id, item.occurrence_id) for item in occurrences
    )


def refine_global_economic_state_effects_v2(
    candidate: GlobalEconomicStateEffectRefinementCandidateV2,
) -> GlobalEconomicStateEffectRefinementV2:
    """Return an opaque witness after exact global V2 reconciliation."""

    if type(candidate) is not GlobalEconomicStateEffectRefinementCandidateV2:
        raise TypeError("global refinement candidate must be exact")
    snapshot = replace(candidate)
    if snapshot.effect_plan.external_outbox_enqueue:
        raise ValueError("global refinement external outbox requires the O-009 publisher")
    if not snapshot.consumed_occurrences and (
        not snapshot.effect_plan.is_empty
        or snapshot.terminal_plan.deltas
        or snapshot.oracle_plan.deltas
        or snapshot.pre_state != snapshot.post_state
    ):
        raise ValueError("global refinement zero-occurrence relation must be static")
    _require_fixed_context_v2(snapshot.pre_state, snapshot.post_state)
    _require_lane_refinement_v2(snapshot.pre_state, snapshot.post_state, snapshot.effect_plan)
    require_global_economic_tables_v2(
        snapshot.pre_state,
        snapshot.post_state,
        snapshot.effect_plan,
    )
    require_global_terminal_refinement_v2(
        snapshot.pre_state,
        snapshot.post_state,
        snapshot.effect_plan,
        snapshot.terminal_plan,
    )
    require_global_oracle_refinement_v2(
        snapshot.pre_state,
        snapshot.post_state,
        snapshot.effect_plan,
        snapshot.oracle_plan,
    )
    replay_insertions = _require_replay_refinement_v2(snapshot)
    state_delta_root = hash_global_v2(
        "global-economic-state-delta-v2",
        {
            "pre_state_root": snapshot.pre_state.state_root,
            "post_state_root": snapshot.post_state.state_root,
            "effect_plan_root": snapshot.effect_plan.effect_plan_root,
            "lane_writes": snapshot.effect_plan.lane_writes,
            "replay_insertions": replay_insertions,
            "terminal_plan_root": snapshot.terminal_plan.plan_root,
            "oracle_plan_root": snapshot.oracle_plan.plan_root,
        },
    )
    return GlobalEconomicStateEffectRefinementV2(
        _REFINEMENT_TOKEN_V2,
        _RefinementFieldsV2(
            pre_state_root=snapshot.pre_state.state_root,
            post_state_root=snapshot.post_state.state_root,
            effect_plan_root=snapshot.effect_plan.effect_plan_root,
            terminal_plan_root=snapshot.terminal_plan.plan_root,
            oracle_plan_root=snapshot.oracle_plan.plan_root,
            state_delta_root=state_delta_root,
        ),
    )


__all__ = [
    "GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V2",
    "GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_AUTHORITY_V2",
    "GlobalEconomicStateEffectRefinementCandidateV2",
    "GlobalEconomicStateEffectRefinementV2",
    "refine_global_economic_state_effects_v2",
]
