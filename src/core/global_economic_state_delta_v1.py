"""Derive exact supported GlobalSettlementABI V1 state deltas."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_ATOMS_V1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    LaneWriteV1,
    ReplayStateV1,
    hash_global_v1,
)

_AMOUNT_EFFECT_KIND_BY_TABLE: Final = {
    "balances": EconomicEffectKindV1.ACCOUNT_MOVEMENT,
    "custody": EconomicEffectKindV1.CUSTODY,
    "liabilities": EconomicEffectKindV1.LIABILITY,
    "reserves": EconomicEffectKindV1.RESERVE,
}


@dataclass(frozen=True, slots=True, order=True)
class _AmountDeltaRowV1:
    table: str
    owner: str
    asset: str
    custody_domain: str
    delta_atoms: int

    def to_canonical(self) -> dict[str, object]:
        return {
            "table": self.table,
            "owner": self.owner,
            "asset": self.asset,
            "custody_domain": self.custody_domain,
            "delta_atoms": self.delta_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class _SupplyDeltaRowV1:
    asset: str
    delta_atoms: int

    def to_canonical(self) -> dict[str, object]:
        return {"asset": self.asset, "delta_atoms": self.delta_atoms}


@dataclass(frozen=True, slots=True)
class _DerivedGlobalEconomicStateDeltaV1:
    amount_deltas: tuple[_AmountDeltaRowV1, ...]
    supply_deltas: tuple[_SupplyDeltaRowV1, ...]
    lane_writes: tuple[LaneWriteV1, ...]
    replay_insertions: tuple[ReplayStateV1, ...]

    @property
    def touched_assets(self) -> frozenset[str]:
        amount_assets = {row.asset for row in self.amount_deltas}
        supply_assets = {row.asset for row in self.supply_deltas}
        return frozenset(amount_assets | supply_assets)

    @property
    def delta_root(self) -> str:
        return hash_global_v1(
            "global-economic-state-delta-v1",
            {
                "schema": GLOBAL_SETTLEMENT_ABI_V1,
                "amount_deltas": self.amount_deltas,
                "supply_deltas": self.supply_deltas,
                "lane_writes": self.lane_writes,
                "replay_insertions": self.replay_insertions,
            },
        )


def _checked_signed_delta_v1(post_atoms: int, pre_atoms: int) -> int:
    delta = post_atoms - pre_atoms
    if not -(1 << 127) <= delta <= (1 << 127) - 1:
        raise ValueError("economic refinement state delta exceeds signed 128-bit bounds")
    return delta


def _amount_delta_rows_v1(
    table: str,
    pre_rows: tuple[EconomicAmountV1, ...],
    post_rows: tuple[EconomicAmountV1, ...],
) -> tuple[_AmountDeltaRowV1, ...]:
    pre = {row.key: row.amount_atoms for row in pre_rows}
    post = {row.key: row.amount_atoms for row in post_rows}
    rows = []
    for asset, owner, domain in sorted(set(pre) | set(post)):
        delta = _checked_signed_delta_v1(
            post.get((asset, owner, domain), 0),
            pre.get((asset, owner, domain), 0),
        )
        if delta != 0:
            rows.append(_AmountDeltaRowV1(table, owner, asset, domain, delta))
    return tuple(sorted(rows))


def _effect_amount_delta_rows_v1(
    effect_plan: GlobalEconomicEffectPlanV1,
    table: str,
    kind: EconomicEffectKindV1,
) -> tuple[_AmountDeltaRowV1, ...]:
    return tuple(
        sorted(
            _AmountDeltaRowV1(
                table,
                row.principal,
                row.asset,
                row.custody_domain,
                row.delta_atoms,
            )
            for row in effect_plan.rows
            if row.kind is kind
        )
    )


def _require_amount_table_refinement_v1(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    effect_plan: GlobalEconomicEffectPlanV1,
) -> tuple[_AmountDeltaRowV1, ...]:
    result: list[_AmountDeltaRowV1] = []
    for table, kind in _AMOUNT_EFFECT_KIND_BY_TABLE.items():
        actual = _amount_delta_rows_v1(
            table,
            getattr(pre_state, table),
            getattr(post_state, table),
        )
        expected = _effect_amount_delta_rows_v1(effect_plan, table, kind)
        if actual != expected:
            singular = "liability" if table == "liabilities" else table.removesuffix("s")
            raise ValueError(f"economic refinement {singular} delta mismatch")
        result.extend(actual)
    return tuple(sorted(result))


def _supply_delta_rows_v1(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
) -> tuple[_SupplyDeltaRowV1, ...]:
    pre = {row.asset: row.amount_atoms for row in pre_state.supplies}
    post = {row.asset: row.amount_atoms for row in post_state.supplies}
    rows = []
    for asset in sorted(set(pre) | set(post)):
        delta = _checked_signed_delta_v1(post.get(asset, 0), pre.get(asset, 0))
        if delta != 0:
            rows.append(_SupplyDeltaRowV1(asset, delta))
    return tuple(rows)


def _effect_supply_delta_rows_v1(
    effect_plan: GlobalEconomicEffectPlanV1,
) -> tuple[_SupplyDeltaRowV1, ...]:
    issued: dict[str, int] = {}
    burned: dict[str, int] = {}
    for row in effect_plan.rows:
        if row.kind is EconomicEffectKindV1.ISSUE:
            issued[row.asset] = issued.get(row.asset, 0) + row.delta_atoms
            if issued[row.asset] > MAX_ATOMS_V1:
                raise ValueError("economic refinement issue total exceeds unsigned 128-bit bounds")
        elif row.kind is EconomicEffectKindV1.BURN:
            burned[row.asset] = burned.get(row.asset, 0) - row.delta_atoms
            if burned[row.asset] > MAX_ATOMS_V1:
                raise ValueError("economic refinement burn total exceeds unsigned 128-bit bounds")
    rows = []
    for asset in sorted(set(issued) | set(burned)):
        delta = _checked_signed_delta_v1(issued.get(asset, 0), burned.get(asset, 0))
        if delta != 0:
            rows.append(_SupplyDeltaRowV1(asset, delta))
    return tuple(rows)


def _require_supply_refinement_v1(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    effect_plan: GlobalEconomicEffectPlanV1,
) -> tuple[_SupplyDeltaRowV1, ...]:
    actual = _supply_delta_rows_v1(pre_state, post_state)
    if actual != _effect_supply_delta_rows_v1(effect_plan):
        raise ValueError("economic refinement supply delta mismatch")
    return actual


def _require_lane_write_refinement_v1(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    effect_plan: GlobalEconomicEffectPlanV1,
) -> tuple[LaneWriteV1, ...]:
    rows = []
    for pre_lane, post_lane in zip(pre_state.lane_roots, post_state.lane_roots, strict=True):
        if (
            pre_lane.lane_id is not post_lane.lane_id
            or pre_lane.module_release_id != post_lane.module_release_id
            or pre_lane.enabled is not post_lane.enabled
        ):
            raise ValueError("economic refinement unsupported lane metadata changed")
        if pre_lane.state_root != post_lane.state_root:
            rows.append(
                LaneWriteV1(pre_lane.lane_id, pre_lane.state_root, post_lane.state_root)
            )
    actual = tuple(sorted(rows, key=lambda row: row.lane_id.value))
    if actual != effect_plan.lane_writes:
        raise ValueError("economic refinement lane write mismatch")
    return actual


def _derive_global_economic_state_delta_v1(
    pre_state: GlobalEconomicStateV1,
    post_state: GlobalEconomicStateV1,
    effect_plan: GlobalEconomicEffectPlanV1,
    replay_insertions: tuple[ReplayStateV1, ...],
) -> _DerivedGlobalEconomicStateDeltaV1:
    return _DerivedGlobalEconomicStateDeltaV1(
        amount_deltas=_require_amount_table_refinement_v1(
            pre_state, post_state, effect_plan
        ),
        supply_deltas=_require_supply_refinement_v1(
            pre_state, post_state, effect_plan
        ),
        lane_writes=_require_lane_write_refinement_v1(
            pre_state, post_state, effect_plan
        ),
        replay_insertions=replay_insertions,
    )
