"""Deterministic ASSET_TRANSFER effect composition for one economic epoch.

This research-only core aggregates route-disclosed effect plans in command
order.  It owns no receipt verification, state publication, or external
delivery authority.  Routes outside the current single ASSET_TRANSFER lane are
rejected by the epoch verifier until their composition laws are implemented.
"""

from __future__ import annotations

from .global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MAX_EPOCH_COMMANDS_V1,
    MIN_DELTA_ATOMS_V1,
    AssetConservationRowV1,
    EconomicEffectRowV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
)


def _checked_i128(value: int, *, name: str) -> int:
    if not MIN_DELTA_ATOMS_V1 <= value <= MAX_DELTA_ATOMS_V1:
        raise ValueError(f"{name} exceeds signed 128-bit atoms")
    return value


def _checked_u128(value: int, *, name: str) -> int:
    if not 0 <= value <= MAX_ATOMS_V1:
        raise ValueError(f"{name} exceeds unsigned 128-bit atoms")
    return value


def _require_asset_lane_plan_shape(plan: GlobalEconomicEffectPlanV1) -> None:
    if len(plan.lane_writes) != 1 or plan.lane_writes[0].lane_id is not LaneIdV1.ASSET_TRANSFER:
        raise ValueError("asset-lane epoch plan requires one ASSET_TRANSFER lane write")
    if len(plan.occurrence_consumptions) != 1:
        raise ValueError("asset-lane epoch plan requires one occurrence consumption")
    if plan.external_outbox_enqueue:
        raise ValueError("asset-lane epoch plan forbids external outbox effects")


def _compose_effect_rows(
    plans: tuple[GlobalEconomicEffectPlanV1, ...],
) -> tuple[EconomicEffectRowV1, ...]:
    totals: dict[tuple[str, str, str, str], tuple[EconomicEffectRowV1, int]] = {}
    for plan in plans:
        for row in plan.rows:
            exemplar, prior = totals.get(row.key, (row, 0))
            total = _checked_i128(prior + row.delta_atoms, name="epoch effect row total")
            totals[row.key] = (exemplar, total)
    return tuple(
        EconomicEffectRowV1(
            exemplar.kind,
            exemplar.principal,
            exemplar.asset,
            exemplar.custody_domain,
            total,
        )
        for _, (exemplar, total) in sorted(totals.items())
        if total != 0
    )


def _compose_asset_conservation(
    plans: tuple[GlobalEconomicEffectPlanV1, ...],
) -> tuple[AssetConservationRowV1, ...]:
    # asset -> first owned, last owned, first supply, last supply, issue, burn
    totals: dict[str, tuple[int, int, int, int, int, int]] = {}
    for plan in plans:
        for row in plan.asset_conservation:
            prior = totals.get(row.asset)
            if prior is None:
                totals[row.asset] = (
                    row.owned_and_custodied_pre_atoms,
                    row.owned_and_custodied_post_atoms,
                    row.supply_pre_atoms,
                    row.supply_post_atoms,
                    row.authorized_issue_atoms,
                    row.authorized_burn_atoms,
                )
                continue
            first_owned, last_owned, first_supply, last_supply, issued, burned = prior
            if (
                last_owned != row.owned_and_custodied_pre_atoms
                or last_supply != row.supply_pre_atoms
            ):
                raise ValueError("asset-lane epoch conservation history is disconnected")
            totals[row.asset] = (
                first_owned,
                row.owned_and_custodied_post_atoms,
                first_supply,
                row.supply_post_atoms,
                _checked_u128(
                    issued + row.authorized_issue_atoms,
                    name="epoch authorized issue total",
                ),
                _checked_u128(
                    burned + row.authorized_burn_atoms,
                    name="epoch authorized burn total",
                ),
            )
    return tuple(
        AssetConservationRowV1(asset, *values)
        for asset, values in sorted(totals.items())
    )


def _compose_fee_conservation(
    plans: tuple[GlobalEconomicEffectPlanV1, ...],
) -> tuple[FeeConservationRowV1, ...]:
    totals: dict[str, tuple[int, int, int]] = {}
    for plan in plans:
        for row in plan.fee_conservation:
            charged, allocated, residue = totals.get(row.asset, (0, 0, 0))
            totals[row.asset] = (
                _checked_u128(charged + row.fee_charged_atoms, name="epoch fee total"),
                _checked_u128(
                    allocated + row.current_allocations_atoms,
                    name="epoch fee allocation total",
                ),
                _checked_u128(
                    residue + row.carried_residue_atoms,
                    name="epoch fee residue total",
                ),
            )
    return tuple(FeeConservationRowV1(asset, *values) for asset, values in sorted(totals.items()))


def _compose_lane_write(
    plans: tuple[GlobalEconomicEffectPlanV1, ...],
) -> tuple[LaneWriteV1, ...]:
    first = plans[0].lane_writes[0]
    last_post_root = first.post_root
    for plan in plans[1:]:
        current = plan.lane_writes[0]
        if current.pre_root != last_post_root:
            raise ValueError("asset-lane epoch lane-write history is disconnected")
        last_post_root = current.post_root
    return (LaneWriteV1(LaneIdV1.ASSET_TRANSFER, first.pre_root, last_post_root),)


def compose_asset_lane_epoch_effect_plans_v1(
    route_effect_plans: tuple[GlobalEconomicEffectPlanV1, ...],
) -> GlobalEconomicEffectPlanV1:
    """Compose 1..64 sequential ASSET_TRANSFER route plans.

    Each route plan must consume exactly one occurrence, carry one lane write,
    and have no external outbox row.  Asset and lane histories must connect in
    route order.  Canonical rows and occurrence IDs are aggregated with checked
    integer arithmetic.  The function is deterministic and performs no I/O.
    """

    if type(route_effect_plans) is not tuple or any(
        not isinstance(plan, GlobalEconomicEffectPlanV1) for plan in route_effect_plans
    ):
        raise TypeError("asset-lane epoch route effect plans must be an exact typed tuple")
    if not 1 <= len(route_effect_plans) <= MAX_EPOCH_COMMANDS_V1:
        raise ValueError("asset-lane epoch requires between one and 64 route effect plans")
    for plan in route_effect_plans:
        _require_asset_lane_plan_shape(plan)

    occurrence_consumptions = tuple(
        sorted(plan.occurrence_consumptions[0] for plan in route_effect_plans)
    )
    if len(occurrence_consumptions) != len(set(occurrence_consumptions)):
        raise ValueError("asset-lane epoch repeats an occurrence consumption")

    return GlobalEconomicEffectPlanV1(
        rows=_compose_effect_rows(route_effect_plans),
        asset_conservation=_compose_asset_conservation(route_effect_plans),
        fee_conservation=_compose_fee_conservation(route_effect_plans),
        lane_writes=_compose_lane_write(route_effect_plans),
        occurrence_consumptions=occurrence_consumptions,
        external_outbox_enqueue=(),
    )


__all__ = ["compose_asset_lane_epoch_effect_plans_v1"]
