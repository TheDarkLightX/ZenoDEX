"""Exact state/effect refinement for the supported GlobalSettlementABI V1 fields.

This deterministic checker binds full pre/post global economic states to the
canonical effect plan.  It is deliberately incomplete: replay insertion,
Oracle occurrences, terminal obligations, history, and external outbox commit
binding remain outside this refinement and therefore cannot change here.

The returned value is an opaque structural witness.  It verifies no receipt,
selects no active profile, applies no durable write, and grants no settlement
or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any, Final

from .global_economic_state_delta_v1 import (
    _derive_global_economic_state_delta_v1,
    _DerivedGlobalEconomicStateDeltaV1,
)
from .global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    AssetConservationRowV1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    ExternalOutboxEnqueueV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneStateRootV1,
    LaneWriteV1,
    OracleOccurrenceStateV1,
    OutboxStateV1,
    ReplayStateV1,
    TerminalObligationV1,
    hash_global_v1,
)

GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V1: Final = (
    "zenodex/global-economic-state-effect-refinement/v1"
)
_REFINEMENT_TOKEN = object()
_STATE_BEARING_FEE_KINDS: Final = frozenset(
    {
        EconomicEffectKindV1.ACCOUNT_MOVEMENT,
        EconomicEffectKindV1.CUSTODY,
        EconomicEffectKindV1.RESERVE,
    }
)


@dataclass(frozen=True, slots=True)
class GlobalEconomicStateEffectRefinementCandidateV1:
    pre_state: GlobalEconomicStateV1
    post_state: GlobalEconomicStateV1
    effect_plan: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        if type(self.pre_state) is not GlobalEconomicStateV1:
            raise TypeError("economic refinement pre-state must be typed")
        if type(self.post_state) is not GlobalEconomicStateV1:
            raise TypeError("economic refinement post-state must be typed")
        if type(self.effect_plan) is not GlobalEconomicEffectPlanV1:
            raise TypeError("economic refinement effect plan must be typed")


@dataclass(frozen=True, slots=True)
class _RefinementFieldsV1:
    pre_state_root: str
    post_state_root: str
    effect_plan_root: str
    state_delta_root: str


class GlobalEconomicStateEffectRefinementV1:
    """Opaque witness produced only after exact state/effect checks pass."""

    _fields: _RefinementFieldsV1
    __slots__ = ("_fields",)

    def __init__(self, token: object, fields: _RefinementFieldsV1) -> None:
        if token is not _REFINEMENT_TOKEN:
            raise TypeError("GlobalEconomicStateEffectRefinementV1 is checker-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("GlobalEconomicStateEffectRefinementV1 is immutable")

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
    def state_delta_root(self) -> str:
        return self._fields.state_delta_root

    @property
    def refinement_root(self) -> str:
        return hash_global_v1(
            "global-economic-state-effect-refinement-v1",
            {
                "schema": GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V1,
                "pre_state_root": self._fields.pre_state_root,
                "post_state_root": self._fields.post_state_root,
                "effect_plan_root": self._fields.effect_plan_root,
                "state_delta_root": self._fields.state_delta_root,
            },
        )


def _require_exact_tuple_items(
    values: object,
    expected_type: type[Any],
    name: str,
) -> tuple[Any, ...]:
    if type(values) is not tuple:
        raise TypeError(f"economic refinement {name} must be an exact tuple")
    items = values
    if any(type(value) is not expected_type for value in items):
        raise TypeError(f"economic refinement {name} must contain exact typed values")
    return items


def _snapshot_dataclass_tuple_v1(
    values: object,
    expected_type: type[Any],
    name: str,
) -> tuple[Any, ...]:
    return tuple(
        replace(value)
        for value in _require_exact_tuple_items(values, expected_type, name)
    )


def _snapshot_state_v1(state: GlobalEconomicStateV1) -> GlobalEconomicStateV1:
    return replace(
        state,
        lane_roots=_snapshot_dataclass_tuple_v1(
            state.lane_roots, LaneStateRootV1, "state lane_roots"
        ),
        balances=_snapshot_dataclass_tuple_v1(
            state.balances, EconomicAmountV1, "state balances"
        ),
        supplies=_snapshot_dataclass_tuple_v1(
            state.supplies, AssetSupplyV1, "state supplies"
        ),
        custody=_snapshot_dataclass_tuple_v1(
            state.custody, EconomicAmountV1, "state custody"
        ),
        liabilities=_snapshot_dataclass_tuple_v1(
            state.liabilities, EconomicAmountV1, "state liabilities"
        ),
        reserves=_snapshot_dataclass_tuple_v1(
            state.reserves, EconomicAmountV1, "state reserves"
        ),
        oracle_occurrences=_snapshot_dataclass_tuple_v1(
            state.oracle_occurrences,
            OracleOccurrenceStateV1,
            "state oracle_occurrences",
        ),
        replay_state=_snapshot_dataclass_tuple_v1(
            state.replay_state, ReplayStateV1, "state replay_state"
        ),
        terminal_obligations=_snapshot_dataclass_tuple_v1(
            state.terminal_obligations,
            TerminalObligationV1,
            "state terminal_obligations",
        ),
        outbox=_snapshot_dataclass_tuple_v1(
            state.outbox, OutboxStateV1, "state outbox"
        ),
    )


def _snapshot_effect_plan_v1(
    effect_plan: GlobalEconomicEffectPlanV1,
) -> GlobalEconomicEffectPlanV1:
    consumptions = _require_exact_tuple_items(
        effect_plan.occurrence_consumptions,
        str,
        "effect plan occurrence consumptions",
    )
    return replace(
        effect_plan,
        rows=_snapshot_dataclass_tuple_v1(
            effect_plan.rows, EconomicEffectRowV1, "effect plan rows"
        ),
        asset_conservation=_snapshot_dataclass_tuple_v1(
            effect_plan.asset_conservation,
            AssetConservationRowV1,
            "effect plan asset_conservation",
        ),
        fee_conservation=_snapshot_dataclass_tuple_v1(
            effect_plan.fee_conservation,
            FeeConservationRowV1,
            "effect plan fee_conservation",
        ),
        lane_writes=_snapshot_dataclass_tuple_v1(
            effect_plan.lane_writes, LaneWriteV1, "effect plan lane_writes"
        ),
        occurrence_consumptions=tuple(consumptions),
        external_outbox_enqueue=_snapshot_dataclass_tuple_v1(
            effect_plan.external_outbox_enqueue,
            ExternalOutboxEnqueueV1,
            "effect plan external_outbox_enqueue",
        ),
    )


def _snapshot_candidate_v1(
    candidate: GlobalEconomicStateEffectRefinementCandidateV1,
) -> GlobalEconomicStateEffectRefinementCandidateV1:
    return GlobalEconomicStateEffectRefinementCandidateV1(
        pre_state=_snapshot_state_v1(candidate.pre_state),
        post_state=_snapshot_state_v1(candidate.post_state),
        effect_plan=_snapshot_effect_plan_v1(candidate.effect_plan),
    )


def _require_fixed_context_v1(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
) -> None:
    fixed_fields = (
        "chain_id",
        "deployment_root",
        "writer_epoch",
        "height",
        "profile_root",
        "oracle_occurrences",
        "replay_state",
        "terminal_obligations",
        "history_root",
        "outbox",
    )
    if any(getattr(pre_state, field) != getattr(post_state, field) for field in fixed_fields):
        raise ValueError("economic refinement unsupported global field changed")


def _require_nonzero_sparse_amounts_v1(state: GlobalEconomicStateV1) -> None:
    for field in ("balances", "custody", "liabilities", "reserves"):
        if any(row.amount_atoms == 0 for row in getattr(state, field)):
            raise ValueError("economic refinement zero economic amount is non-canonical")


def _require_supported_effects_v1(effect_plan: GlobalEconomicEffectPlanV1) -> None:
    if effect_plan.occurrence_consumptions:
        raise ValueError("economic refinement replay occurrence refinement is unavailable")
    if effect_plan.external_outbox_enqueue:
        raise ValueError("economic refinement external outbox refinement is unavailable")
    if any(
        row.kind in {EconomicEffectKindV1.REWARD, EconomicEffectKindV1.SLASH}
        for row in effect_plan.rows
    ):
        raise ValueError("economic refinement reward and slash labels are unmapped")


def _require_fee_mirror_v1(effect_plan: GlobalEconomicEffectPlanV1) -> None:
    state_rows = {
        (row.principal, row.asset, row.custody_domain, row.delta_atoms)
        for row in effect_plan.rows
        if row.kind in _STATE_BEARING_FEE_KINDS
    }
    for row in effect_plan.rows:
        if row.kind is EconomicEffectKindV1.FEE_ALLOCATION and (
            row.principal,
            row.asset,
            row.custody_domain,
            row.delta_atoms,
        ) not in state_rows:
            raise ValueError("economic refinement fee allocation is not mirrored")
    if any(row.fee_charged_atoms == 0 for row in effect_plan.fee_conservation):
        raise ValueError("economic refinement zero fee conservation row is non-canonical")
    if any(row.carried_residue_atoms != 0 for row in effect_plan.fee_conservation):
        raise ValueError("economic refinement fee residue has no state-bearing mapping")


def _amount_totals_by_asset_v1(
    state: GlobalEconomicStateV1,
) -> dict[str, int]:
    totals: dict[str, int] = {}
    for field in ("balances", "custody", "reserves"):
        for row in getattr(state, field):
            total = totals.get(row.asset, 0) + row.amount_atoms
            if total > MAX_ATOMS_V1:
                raise ValueError("economic refinement owned total exceeds unsigned 128-bit bounds")
            totals[row.asset] = total
    return totals


def _require_conservation_refinement_v1(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    effect_plan: GlobalEconomicEffectPlanV1,
    state_delta: _DerivedGlobalEconomicStateDeltaV1,
) -> None:
    pre_owned = _amount_totals_by_asset_v1(pre_state)
    post_owned = _amount_totals_by_asset_v1(post_state)
    pre_supply = {row.asset: row.amount_atoms for row in pre_state.supplies}
    post_supply = {row.asset: row.amount_atoms for row in post_state.supplies}
    all_state_assets = set(pre_owned) | set(post_owned) | set(pre_supply) | set(post_supply)
    if any(
        pre_owned.get(asset, 0) != pre_supply.get(asset, 0)
        or post_owned.get(asset, 0) != post_supply.get(asset, 0)
        for asset in all_state_assets
    ):
        raise ValueError("economic refinement owned total does not equal supply")
    touched_assets = set(state_delta.touched_assets) | {
        row.asset
        for row in effect_plan.rows
        if row.kind in {EconomicEffectKindV1.ISSUE, EconomicEffectKindV1.BURN}
    }
    conservation = {row.asset: row for row in effect_plan.asset_conservation}
    if set(conservation) != touched_assets:
        raise ValueError("economic refinement conservation asset set mismatch")
    for asset in touched_assets:
        row = conservation[asset]
        expected = (
            pre_owned.get(asset, 0),
            post_owned.get(asset, 0),
            pre_supply.get(asset, 0),
            post_supply.get(asset, 0),
        )
        actual = (
            row.owned_and_custodied_pre_atoms,
            row.owned_and_custodied_post_atoms,
            row.supply_pre_atoms,
            row.supply_post_atoms,
        )
        if actual != expected:
            raise ValueError("economic refinement conservation state mismatch")


def refine_global_economic_state_effects_v1(
    candidate: GlobalEconomicStateEffectRefinementCandidateV1,
) -> GlobalEconomicStateEffectRefinementV1:
    """Return an opaque witness after exact supported-field refinement checks."""

    if type(candidate) is not GlobalEconomicStateEffectRefinementCandidateV1:
        raise TypeError("economic refinement candidate must be typed")
    snapshot = _snapshot_candidate_v1(candidate)
    pre_state = snapshot.pre_state
    post_state = snapshot.post_state
    effect_plan = snapshot.effect_plan
    _require_fixed_context_v1(pre_state, post_state)
    _require_nonzero_sparse_amounts_v1(pre_state)
    _require_nonzero_sparse_amounts_v1(post_state)
    _require_supported_effects_v1(effect_plan)
    _require_fee_mirror_v1(effect_plan)
    state_delta = _derive_global_economic_state_delta_v1(
        pre_state, post_state, effect_plan
    )
    _require_conservation_refinement_v1(
        pre_state,
        post_state,
        effect_plan,
        state_delta,
    )
    return GlobalEconomicStateEffectRefinementV1(
        _REFINEMENT_TOKEN,
        _RefinementFieldsV1(
            pre_state_root=pre_state.state_root,
            post_state_root=post_state.state_root,
            effect_plan_root=effect_plan.effect_plan_root,
            state_delta_root=state_delta.delta_root,
        ),
    )


__all__ = [
    "GLOBAL_ECONOMIC_STATE_EFFECT_REFINEMENT_SCHEMA_V1",
    "GlobalEconomicStateEffectRefinementCandidateV1",
    "GlobalEconomicStateEffectRefinementV1",
    "refine_global_economic_state_effects_v1",
]
