"""Pure shadow transition for governed ZDEX protocol-fee allocation."""

from __future__ import annotations

from dataclasses import dataclass

from .global_settlement_types_v1 import (
    GLOBAL_SETTLEMENT_ABI_V1,
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    AssetConservationRowV1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    FeeConservationRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
)
from .zdex_fee_allocation_types_v1 import (
    BASIS_POINTS_DENOMINATOR_V1,
    FEE_BUYBACK_PRINCIPAL_V1,
    FEE_INGRESS_CONTROL_DOMAIN_V1,
    FEE_INGRESS_PRINCIPAL_V1,
    FEE_RESIDUE_CONTROL_DOMAIN_V1,
    FEE_RESIDUE_PRINCIPAL_V1,
    ZDEX_FEE_DESTINATIONS_V1,
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationOccurrenceV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeAllocationRejectCodeV1,
    ZDEXFeeAllocationRejectedV1,
    ZDEXFeeAllocationResultV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeDestinationV1,
    ZDEXFeeShareV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
    fee_destination_control_domain_v1,
    fee_destination_principal_v1,
)


@dataclass(frozen=True, slots=True)
class _AllocationProjectionV1:
    fee_charged_atoms: int
    allocations: tuple[ZDEXFeeDestinationAmountV1, ...]
    residue_atoms: int

    @property
    def allocated_atoms(self) -> int:
        return sum(value.allocation_atoms for value in self.allocations)


@dataclass(frozen=True, slots=True)
class _AcceptedInputsV1:
    context: ZDEXFeeAllocationContextV1
    pre_state: ZDEXFeeStateV1
    post_state: ZDEXFeeStateV1
    projection: _AllocationProjectionV1
    effects: GlobalEconomicEffectPlanV1


def _reject(
    code: ZDEXFeeAllocationRejectCodeV1,
    pre_state: ZDEXFeeStateV1,
) -> ZDEXFeeAllocationRejectedV1:
    return ZDEXFeeAllocationRejectedV1(code, pre_state, pre_state)


def _require_exact_inputs(
    context: object,
    pre_state: object,
    policy: object,
    command: object,
) -> None:
    expected = (
        (context, ZDEXFeeAllocationContextV1, "context"),
        (pre_state, ZDEXFeeStateV1, "pre-state"),
        (policy, ZDEXFeeAllocationPolicyV1, "policy"),
        (command, ZDEXFeeAllocationCommandV1, "command"),
    )
    for value, expected_type, name in expected:
        if type(value) is not expected_type:
            raise TypeError(f"ZDEX fee allocation {name} must be exact typed data")


def _precheck(
    context: ZDEXFeeAllocationContextV1,
    pre_state: ZDEXFeeStateV1,
    policy: ZDEXFeeAllocationPolicyV1,
    command: ZDEXFeeAllocationCommandV1,
) -> ZDEXFeeAllocationRejectedV1 | None:
    if context.policy_root != policy.policy_root or pre_state.policy_root != policy.policy_root:
        return _reject(ZDEXFeeAllocationRejectCodeV1.POLICY_MISMATCH, pre_state)
    if command.fee_charged_atoms == 0:
        return _reject(ZDEXFeeAllocationRejectCodeV1.ZERO_FEE, pre_state)
    if command.fee_charged_atoms > MAX_DELTA_ATOMS_V1:
        return _reject(ZDEXFeeAllocationRejectCodeV1.EFFECT_WIDTH_EXCEEDED, pre_state)
    if command.fee_charged_atoms > pre_state.fee_ingress_atoms:
        return _reject(ZDEXFeeAllocationRejectCodeV1.INSUFFICIENT_FEE_INGRESS, pre_state)
    return None


def _project(
    policy: ZDEXFeeAllocationPolicyV1,
    fee_charged_atoms: int,
) -> _AllocationProjectionV1:
    allocations = tuple(
        ZDEXFeeDestinationAmountV1(
            share.destination,
            fee_charged_atoms * share.share_bps // BASIS_POINTS_DENOMINATOR_V1,
        )
        for share in policy.shares
    )
    allocated_atoms = sum(value.allocation_atoms for value in allocations)
    return _AllocationProjectionV1(
        fee_charged_atoms,
        allocations,
        fee_charged_atoms - allocated_atoms,
    )


def _next_state(
    pre_state: ZDEXFeeStateV1,
    projection: _AllocationProjectionV1,
) -> ZDEXFeeStateV1 | None:
    balances: list[ZDEXFeeDestinationAmountV1] = []
    for previous, allocation in zip(
        pre_state.destination_balances,
        projection.allocations,
        strict=True,
    ):
        next_amount = previous.allocation_atoms + allocation.allocation_atoms
        if next_amount > MAX_ATOMS_V1:
            return None
        balances.append(ZDEXFeeDestinationAmountV1(previous.destination, next_amount))
    next_reserve = pre_state.unallocated_reserve_atoms + projection.residue_atoms
    if next_reserve > MAX_ATOMS_V1:
        return None
    return ZDEXFeeStateV1(
        pre_state.fee_asset_id,
        pre_state.policy_root,
        pre_state.fee_ingress_atoms - projection.fee_charged_atoms,
        next_reserve,
        tuple(balances),
        pre_state.owned_and_custodied_atoms,
        pre_state.supply_atoms,
    )


def _effect_rows(
    pre_state: ZDEXFeeStateV1,
    projection: _AllocationProjectionV1,
) -> tuple[EconomicEffectRowV1, ...]:
    rows = [
        EconomicEffectRowV1(
            EconomicEffectKindV1.CUSTODY,
            FEE_INGRESS_PRINCIPAL_V1,
            pre_state.fee_asset_id,
            FEE_INGRESS_CONTROL_DOMAIN_V1,
            -projection.fee_charged_atoms,
        )
    ]
    rows.extend(
        EconomicEffectRowV1(
            EconomicEffectKindV1.FEE_ALLOCATION,
            fee_destination_principal_v1(value.destination),
            pre_state.fee_asset_id,
            fee_destination_control_domain_v1(value.destination),
            value.allocation_atoms,
        )
        for value in projection.allocations
        if value.allocation_atoms > 0
    )
    if projection.residue_atoms > 0:
        rows.append(
            EconomicEffectRowV1(
                EconomicEffectKindV1.RESERVE,
                FEE_RESIDUE_PRINCIPAL_V1,
                pre_state.fee_asset_id,
                FEE_RESIDUE_CONTROL_DOMAIN_V1,
                projection.residue_atoms,
            )
        )
    return tuple(sorted(rows, key=lambda row: row.key))


def _effect_plan(
    context: ZDEXFeeAllocationContextV1,
    pre_state: ZDEXFeeStateV1,
    post_state: ZDEXFeeStateV1,
    projection: _AllocationProjectionV1,
) -> GlobalEconomicEffectPlanV1:
    return GlobalEconomicEffectPlanV1(
        rows=_effect_rows(pre_state, projection),
        asset_conservation=(
            AssetConservationRowV1(
                pre_state.fee_asset_id,
                pre_state.owned_and_custodied_atoms,
                post_state.owned_and_custodied_atoms,
                pre_state.supply_atoms,
                post_state.supply_atoms,
                0,
                0,
            ),
        ),
        fee_conservation=(
            FeeConservationRowV1(
                pre_state.fee_asset_id,
                projection.fee_charged_atoms,
                projection.allocated_atoms,
                projection.residue_atoms,
            ),
        ),
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.ZDEX_TOKENOMICS,
                pre_state.state_root,
                post_state.state_root,
            ),
        ),
        occurrence_consumptions=(context.command_occurrence_id,),
        external_outbox_enqueue=(),
    )


def _occurrence(inputs: _AcceptedInputsV1) -> ZDEXFeeAllocationOccurrenceV1:
    return ZDEXFeeAllocationOccurrenceV1(
        schema=GLOBAL_SETTLEMENT_ABI_V1,
        chain_id=inputs.context.chain_id,
        deployment_root=inputs.context.deployment_root,
        profile_root=inputs.context.profile_root,
        writer_epoch=inputs.context.writer_epoch,
        allocation_route_release_id=inputs.context.allocation_route_release_id,
        authorized_buyback_route_release_id=(
            inputs.context.authorized_buyback_route_release_id
        ),
        tokenomics_module_release_id=inputs.context.tokenomics_module_release_id,
        command_occurrence_id=inputs.context.command_occurrence_id,
        policy_root=inputs.context.policy_root,
        fee_asset_id=inputs.pre_state.fee_asset_id,
        fee_charged_atoms=inputs.projection.fee_charged_atoms,
        allocations=inputs.projection.allocations,
        carried_residue_atoms=inputs.projection.residue_atoms,
        pre_lane_root=inputs.pre_state.state_root,
        post_lane_root=inputs.post_state.state_root,
        effect_plan_root=inputs.effects.effect_plan_root,
    )


def transition_zdex_fee_allocation_v1(
    context: ZDEXFeeAllocationContextV1,
    pre_state: ZDEXFeeStateV1,
    policy: ZDEXFeeAllocationPolicyV1,
    command: ZDEXFeeAllocationCommandV1,
) -> ZDEXFeeAllocationResultV1:
    """Allocate one charged-fee occurrence with typed fail-closed rejection."""

    _require_exact_inputs(context, pre_state, policy, command)
    if rejected := _precheck(context, pre_state, policy, command):
        return rejected
    projection = _project(policy, command.fee_charged_atoms)
    post_state = _next_state(pre_state, projection)
    if post_state is None:
        return _reject(ZDEXFeeAllocationRejectCodeV1.STATE_OVERFLOW, pre_state)
    effects = _effect_plan(
        context,
        pre_state,
        post_state,
        projection,
    )
    inputs = _AcceptedInputsV1(
        context,
        pre_state,
        post_state,
        projection,
        effects,
    )
    return ZDEXFeeAllocationAcceptedV1(pre_state, post_state, effects, _occurrence(inputs))


__all__ = [
    "BASIS_POINTS_DENOMINATOR_V1",
    "FEE_BUYBACK_PRINCIPAL_V1",
    "FEE_INGRESS_CONTROL_DOMAIN_V1",
    "FEE_INGRESS_PRINCIPAL_V1",
    "FEE_RESIDUE_CONTROL_DOMAIN_V1",
    "FEE_RESIDUE_PRINCIPAL_V1",
    "ZDEX_FEE_DESTINATIONS_V1",
    "ZDEXFeeAllocationAcceptedV1",
    "ZDEXFeeAllocationCommandV1",
    "ZDEXFeeAllocationContextV1",
    "ZDEXFeeAllocationOccurrenceV1",
    "ZDEXFeeAllocationPolicyV1",
    "ZDEXFeeAllocationRejectCodeV1",
    "ZDEXFeeAllocationRejectedV1",
    "ZDEXFeeAllocationResultV1",
    "ZDEXFeeDestinationAmountV1",
    "ZDEXFeeDestinationV1",
    "ZDEXFeeShareV1",
    "ZDEXFeeStateV1",
    "candidate_zdex_fee_allocation_policy_v1",
    "transition_zdex_fee_allocation_v1",
]
