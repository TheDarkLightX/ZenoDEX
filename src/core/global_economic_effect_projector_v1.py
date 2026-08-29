"""Deterministically project one supported effect plan into global state."""

from __future__ import annotations

from dataclasses import replace

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    GlobalEconomicEffectPlanV1,
    GlobalEconomicStateV1,
    ReplayStateV1,
)

_AMOUNT_TABLE_V1 = {
    EconomicEffectKindV1.ACCOUNT_MOVEMENT: "balances",
    EconomicEffectKindV1.CUSTODY: "custody",
    EconomicEffectKindV1.LIABILITY: "liabilities",
    EconomicEffectKindV1.RESERVE: "reserves",
}


def _project_amount_table_v1(
    rows: tuple[EconomicAmountV1, ...],
    effects: GlobalEconomicEffectPlanV1,
    kind: EconomicEffectKindV1,
) -> tuple[EconomicAmountV1, ...]:
    amounts = {row.key: row.amount_atoms for row in rows}
    for effect in effects.rows:
        if effect.kind is not kind:
            continue
        key = (effect.asset, effect.principal, effect.custody_domain)
        projected = amounts.get(key, 0) + effect.delta_atoms
        if not 0 <= projected <= MAX_ATOMS_V1:
            raise ValueError("economic effect projection amount is outside u128")
        if projected == 0:
            amounts.pop(key, None)
        else:
            amounts[key] = projected
    return tuple(
        EconomicAmountV1(owner, asset, domain, amount)
        for (asset, owner, domain), amount in sorted(amounts.items())
    )


def _project_supplies_v1(
    rows: tuple[AssetSupplyV1, ...],
    effects: GlobalEconomicEffectPlanV1,
) -> tuple[AssetSupplyV1, ...]:
    supplies = {row.asset: row.amount_atoms for row in rows}
    for effect in effects.rows:
        if effect.kind not in {EconomicEffectKindV1.ISSUE, EconomicEffectKindV1.BURN}:
            continue
        projected = supplies.get(effect.asset, 0) + effect.delta_atoms
        if not 0 <= projected <= MAX_ATOMS_V1:
            raise ValueError("economic effect projection supply is outside u128")
        if projected == 0:
            supplies.pop(effect.asset, None)
        else:
            supplies[effect.asset] = projected
    return tuple(AssetSupplyV1(asset, amount) for asset, amount in sorted(supplies.items()))


def project_single_occurrence_global_effects_v1(
    pre_state: GlobalEconomicStateV1,
    effects: GlobalEconomicEffectPlanV1,
    occurrence: EconomicCommandOccurrenceV1,
) -> GlobalEconomicStateV1:
    """Return the unique supported post-state or reject without mutation."""

    if type(pre_state) is not GlobalEconomicStateV1:
        raise TypeError("economic effect projection pre-state must be exact typed data")
    if type(effects) is not GlobalEconomicEffectPlanV1:
        raise TypeError("economic effect projection plan must be exact typed data")
    if type(occurrence) is not EconomicCommandOccurrenceV1:
        raise TypeError("economic effect projection occurrence must be exact typed data")
    effects.validate()
    if (
        occurrence.pre_state_root != pre_state.state_root
        or occurrence.chain_id != pre_state.chain_id
        or occurrence.deployment_root != pre_state.deployment_root
        or occurrence.profile_root != pre_state.profile_root
        or occurrence.height != pre_state.height + 1
        or effects.occurrence_consumptions != (occurrence.occurrence_id,)
    ):
        raise ValueError("economic effect projection occurrence context mismatch")
    unsupported = {
        EconomicEffectKindV1.REWARD,
        EconomicEffectKindV1.SLASH,
    }
    if effects.external_outbox_enqueue or any(row.kind in unsupported for row in effects.rows):
        raise ValueError("economic effect projection contains an unsupported effect")
    lane_roots = list(pre_state.lane_roots)
    for write in effects.lane_writes:
        index = next(
            index for index, lane in enumerate(lane_roots) if lane.lane_id is write.lane_id
        )
        if lane_roots[index].state_root != write.pre_root:
            raise ValueError("economic effect projection lane pre-root mismatch")
        lane_roots[index] = replace(lane_roots[index], state_root=write.post_root)
    replay = ReplayStateV1(occurrence.replay_id, occurrence.occurrence_id)
    if any(
        row.replay_id == replay.replay_id or row.occurrence_id == replay.occurrence_id
        for row in pre_state.replay_state
    ):
        raise ValueError("economic effect projection replay identity is already consumed")
    tables = {
        table: _project_amount_table_v1(
            getattr(pre_state, table),
            effects,
            kind,
        )
        for kind, table in _AMOUNT_TABLE_V1.items()
    }
    return replace(
        pre_state,
        height=occurrence.height,
        lane_roots=tuple(lane_roots),
        balances=tables["balances"],
        custody=tables["custody"],
        liabilities=tables["liabilities"],
        reserves=tables["reserves"],
        supplies=_project_supplies_v1(pre_state.supplies, effects),
        replay_state=tuple(
            sorted((*pre_state.replay_state, replay), key=lambda row: row.replay_id)
        ),
    )


__all__ = ["project_single_occurrence_global_effects_v1"]
