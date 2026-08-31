"""Economic-table and lifecycle checks for the V2 global refinement gate.

These deterministic helpers compare committed state against one canonical
effect plan.  They construct no authority and expose no acceptance witness.
"""

from __future__ import annotations

from typing import Final

from .global_economic_state_v2 import GlobalEconomicStateV2
from .global_settlement_types_v2 import (
    MAX_DELTA_ATOMS_V2,
    MIN_DELTA_ATOMS_V2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    TerminalObligationStatusV2,
)

_STATE_EFFECT_FIELDS_V2: Final = {
    EconomicEffectKindV2.ACCOUNT_MOVEMENT: "balances",
    EconomicEffectKindV2.CUSTODY: "custody",
    EconomicEffectKindV2.LIABILITY: "liabilities",
    EconomicEffectKindV2.RESERVE: "reserves",
}


def _amount_map_v2(
    rows: tuple[EconomicAmountV2, ...],
) -> dict[tuple[str, str, str], int]:
    return {row.key: row.amount_atoms for row in rows}


def _state_table_deltas_v2(
    pre_rows: tuple[EconomicAmountV2, ...],
    post_rows: tuple[EconomicAmountV2, ...],
) -> dict[tuple[str, str, str], int]:
    pre = _amount_map_v2(pre_rows)
    post = _amount_map_v2(post_rows)
    return {
        key: post.get(key, 0) - pre.get(key, 0)
        for key in pre.keys() | post.keys()
        if post.get(key, 0) != pre.get(key, 0)
    }


def _effect_deltas_v2(
    effect_plan: GlobalEconomicEffectPlanV2,
    kind: EconomicEffectKindV2,
) -> dict[tuple[str, str, str], int]:
    return {
        (row.asset, row.principal, row.custody_domain): row.delta_atoms
        for row in effect_plan.rows
        if row.kind is kind
    }


def _require_state_effect_rows_v2(
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
) -> None:
    for kind, field_name in _STATE_EFFECT_FIELDS_V2.items():
        expected = _state_table_deltas_v2(
            getattr(pre_state, field_name),
            getattr(post_state, field_name),
        )
        actual = _effect_deltas_v2(effect_plan, kind)
        if expected != actual:
            raise ValueError(f"global refinement {field_name} state/effect mismatch")


def _supply_map_v2(state: GlobalEconomicStateV2) -> dict[str, int]:
    return state.supply_atoms_by_asset()


def _supply_effect_deltas_v2(
    effect_plan: GlobalEconomicEffectPlanV2,
) -> dict[str, int]:
    deltas: dict[str, int] = {}
    for row in effect_plan.rows:
        if row.kind not in {EconomicEffectKindV2.ISSUE, EconomicEffectKindV2.BURN}:
            continue
        deltas[row.asset] = deltas.get(row.asset, 0) + row.delta_atoms
    return {asset: delta for asset, delta in deltas.items() if delta}


def _require_supply_effects_v2(
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
) -> None:
    pre = _supply_map_v2(pre_state)
    post = _supply_map_v2(post_state)
    expected = {
        asset: post.get(asset, 0) - pre.get(asset, 0)
        for asset in pre.keys() | post.keys()
        if post.get(asset, 0) != pre.get(asset, 0)
    }
    if expected != _supply_effect_deltas_v2(effect_plan):
        raise ValueError("global refinement supply issue/burn mismatch")


def _changed_economic_assets_v2(
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
) -> set[str]:
    touched = {row.asset for row in effect_plan.rows}
    touched.update(row.asset for row in effect_plan.fee_conservation)
    for field_name in ("balances", "custody", "liabilities", "reserves"):
        touched.update(
            key[0]
            for key in _state_table_deltas_v2(
                getattr(pre_state, field_name),
                getattr(post_state, field_name),
            )
        )
    pre_supply = _supply_map_v2(pre_state)
    post_supply = _supply_map_v2(post_state)
    touched.update(
        asset
        for asset in pre_supply.keys() | post_supply.keys()
        if pre_supply.get(asset, 0) != post_supply.get(asset, 0)
    )
    return touched


def _require_asset_conservation_v2(
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
) -> None:
    pre_owned = pre_state.owned_atoms_by_asset()
    post_owned = post_state.owned_atoms_by_asset()
    pre_supply = _supply_map_v2(pre_state)
    post_supply = _supply_map_v2(post_state)
    all_assets = pre_owned.keys() | post_owned.keys() | pre_supply.keys() | post_supply.keys()
    if any(
        pre_owned.get(asset, 0) != pre_supply.get(asset, 0)
        or post_owned.get(asset, 0) != post_supply.get(asset, 0)
        for asset in all_assets
    ):
        raise ValueError("global refinement owned total does not equal supply")
    rows = {row.asset: row for row in effect_plan.asset_conservation}
    if set(rows) != _changed_economic_assets_v2(pre_state, post_state, effect_plan):
        raise ValueError("global refinement conservation asset coverage mismatch")
    for asset, row in rows.items():
        if (
            row.owned_and_custodied_pre_atoms,
            row.owned_and_custodied_post_atoms,
            row.supply_pre_atoms,
            row.supply_post_atoms,
        ) != (
            pre_owned.get(asset, 0),
            post_owned.get(asset, 0),
            pre_supply.get(asset, 0),
            post_supply.get(asset, 0),
        ):
            raise ValueError("global refinement conservation state mismatch")


def _state_bearing_effect_totals_v2(
    effect_plan: GlobalEconomicEffectPlanV2,
) -> dict[tuple[str, str, str], int]:
    totals: dict[tuple[str, str, str], int] = {}
    for row in effect_plan.rows:
        if row.kind not in {
            EconomicEffectKindV2.ACCOUNT_MOVEMENT,
            EconomicEffectKindV2.CUSTODY,
            EconomicEffectKindV2.RESERVE,
        }:
            continue
        key = (row.asset, row.principal, row.custody_domain)
        total = totals.get(key, 0) + row.delta_atoms
        if not MIN_DELTA_ATOMS_V2 <= total <= MAX_DELTA_ATOMS_V2:
            raise ValueError("global refinement annotation mirror overflow")
        totals[key] = total
    return totals


def _require_annotation_mirrors_v2(effect_plan: GlobalEconomicEffectPlanV2) -> None:
    state_rows = _state_bearing_effect_totals_v2(effect_plan)
    for row in effect_plan.rows:
        key = (row.asset, row.principal, row.custody_domain)
        if row.kind is EconomicEffectKindV2.FEE_ALLOCATION:
            if row.delta_atoms < 0 or key not in state_rows:
                raise ValueError("global refinement fee allocation is not mirrored")
        elif row.kind in {EconomicEffectKindV2.REWARD, EconomicEffectKindV2.SLASH}:
            if state_rows.get(key, 0) != row.delta_atoms:
                raise ValueError(
                    "global refinement reward or slash lacks exact state-bearing mirror"
                )


def _require_liability_backing_v2(state: GlobalEconomicStateV2) -> None:
    custody: dict[str, int] = {}
    for row in state.custody:
        custody[row.asset] = custody.get(row.asset, 0) + row.amount_atoms
    liabilities = state.liability_atoms_by_asset()
    if any(amount > custody.get(asset, 0) for asset, amount in liabilities.items()):
        raise ValueError("global refinement liabilities exceed accounting backing")


def require_global_economic_tables_v2(
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
) -> None:
    """Require exact state/effect, supply, conservation, and backing agreement."""

    _require_state_effect_rows_v2(pre_state, post_state, effect_plan)
    _require_supply_effects_v2(pre_state, post_state, effect_plan)
    _require_asset_conservation_v2(pre_state, post_state, effect_plan)
    _require_annotation_mirrors_v2(effect_plan)
    _require_liability_backing_v2(pre_state)
    _require_liability_backing_v2(post_state)


def _terminal_liability_deltas_v2(
    plan: GlobalTerminalObligationPlanV2,
) -> dict[tuple[str, str, str], int]:
    values: dict[tuple[str, str, str], int] = {}
    for delta in plan.deltas:
        post = delta.post_obligation
        key = (post.asset, post.claimant, post.liability_domain)
        pre_atoms = (
            delta.pre_obligation.amount_atoms
            if delta.pre_obligation is not None
            and delta.pre_obligation.status is TerminalObligationStatusV2.OPEN
            else 0
        )
        post_atoms = (
            post.amount_atoms if post.status is TerminalObligationStatusV2.OPEN else 0
        )
        value = values.get(key, 0) + post_atoms - pre_atoms
        if not MIN_DELTA_ATOMS_V2 <= value <= MAX_DELTA_ATOMS_V2:
            raise ValueError("global refinement terminal liability delta overflow")
        values[key] = value
    return {key: value for key, value in values.items() if value}


def require_global_terminal_refinement_v2(
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
    terminal_plan: GlobalTerminalObligationPlanV2,
) -> None:
    expected = {row.obligation_id: row for row in pre_state.terminal_obligations}
    written_lanes = {row.lane_id for row in effect_plan.lane_writes}
    for delta in terminal_plan.deltas:
        if expected.get(delta.obligation_id) != delta.pre_obligation:
            raise ValueError("global refinement terminal obligation pre-state mismatch")
        if delta.post_obligation.lane_id not in written_lanes:
            raise ValueError("global refinement terminal obligation lacks its owning lane write")
        expected[delta.obligation_id] = delta.post_obligation
    if post_state.terminal_obligations != tuple(expected[key] for key in sorted(expected)):
        raise ValueError("global refinement terminal obligation plan mismatch")
    if _terminal_liability_deltas_v2(terminal_plan) != _effect_deltas_v2(
        effect_plan,
        EconomicEffectKindV2.LIABILITY,
    ):
        raise ValueError("global refinement terminal obligation liability mismatch")


def require_global_oracle_refinement_v2(
    pre_state: GlobalEconomicStateV2,
    post_state: GlobalEconomicStateV2,
    effect_plan: GlobalEconomicEffectPlanV2,
    oracle_plan: GlobalOracleOccurrencePlanV2,
) -> None:
    expected = {row.oracle_id: row for row in pre_state.oracle_occurrences}
    if oracle_plan.deltas and not any(
        row.lane_id is LaneIdV2.ORACLE_MARKET for row in effect_plan.lane_writes
    ):
        raise ValueError("global refinement Oracle lane write is missing")
    for delta in oracle_plan.deltas:
        if expected.get(delta.oracle_id) != delta.pre_occurrence:
            raise ValueError("global refinement Oracle occurrence pre-state mismatch")
        expected[delta.oracle_id] = delta.post_occurrence
    if post_state.oracle_occurrences != tuple(expected[key] for key in sorted(expected)):
        raise ValueError("global refinement Oracle occurrence plan mismatch")


__all__ = [
    "require_global_economic_tables_v2",
    "require_global_terminal_refinement_v2",
    "require_global_oracle_refinement_v2",
]
