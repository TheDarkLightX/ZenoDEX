"""Exact owned snapshots for untrusted ZDEX tokenomics composition inputs."""

from __future__ import annotations

from dataclasses import replace
from typing import Any, TypeVar, cast

from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _require_exact_tuple_items,
    _snapshot_effect_plan_v1,
)
from .global_settlement_types_v1 import GlobalEconomicEffectPlanV1
from .zdex_fee_allocation_types_v1 import (
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationOccurrenceV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeDestinationV1,
    ZDEXFeeShareV1,
    ZDEXFeeStateV1,
)
from .zdex_hyperdeflation_types_v1 import ZDEXAmountBucketV1, ZDEXSupplyStateV1
from .zdex_purchase_burn_route_types_v1 import ZDEXBurnJournalV1
from .zdex_tokenomics_fee_lane_v1 import (
    ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
    ZDEXTokenomicsFeeAllocationPrivatePortV1,
)
from .zdex_tokenomics_lane_v1 import (
    ZDEXTokenomicsBurnCoordinatorContextV1,
    ZDEXTokenomicsBurnPrivatePortV1,
    ZDEXTokenomicsLaneStateV1,
)

_ExactScalarDataclassT = TypeVar("_ExactScalarDataclassT")


def _snapshot_exact_scalar_dataclass_v1(
    value: object,
    expected_type: type[_ExactScalarDataclassT],
    *,
    name: str,
) -> _ExactScalarDataclassT:
    if type(value) is not expected_type:
        raise TypeError(f"{name} must be exact typed data")
    _require_exact_dataclass_scalars_v1(value, name=name)
    return cast(_ExactScalarDataclassT, replace(cast(Any, value)))


def _snapshot_fee_destination_amounts_v1(
    values: object,
    *,
    name: str,
) -> tuple[ZDEXFeeDestinationAmountV1, ...]:
    if type(values) is not tuple or any(
        type(value) is not ZDEXFeeDestinationAmountV1 for value in values
    ):
        raise TypeError(f"{name} must be exact typed tuple data")
    snapshots = []
    for value in values:
        if (
            type(value.destination) is not ZDEXFeeDestinationV1
            or type(value.allocation_atoms) is not int
        ):
            raise TypeError(f"{name} must contain exact scalar data")
        snapshots.append(replace(value))
    return tuple(snapshots)


def _snapshot_fee_state_v1(state: object) -> ZDEXFeeStateV1:
    if type(state) is not ZDEXFeeStateV1:
        raise TypeError("ZDEX tokenomics fee state must be exact typed data")
    typed_state = cast(ZDEXFeeStateV1, state)
    _require_exact_dataclass_scalars_v1(
        typed_state,
        name="ZDEX tokenomics fee state",
        tuple_fields=frozenset({"destination_balances"}),
    )
    return replace(
        typed_state,
        destination_balances=_snapshot_fee_destination_amounts_v1(
            typed_state.destination_balances,
            name="ZDEX tokenomics fee state destination balances",
        ),
    )


def _snapshot_fee_journal_v1(
    journal: object,
) -> ZDEXFeeAllocationOccurrenceV1:
    if type(journal) is not ZDEXFeeAllocationOccurrenceV1:
        raise TypeError("ZDEX tokenomics fee journal must be exact typed data")
    typed_journal = cast(ZDEXFeeAllocationOccurrenceV1, journal)
    _require_exact_dataclass_scalars_v1(
        typed_journal,
        name="ZDEX tokenomics fee journal",
        tuple_fields=frozenset({"allocations"}),
    )
    return replace(
        typed_journal,
        allocations=_snapshot_fee_destination_amounts_v1(
            typed_journal.allocations,
            name="ZDEX tokenomics fee journal allocations",
        ),
    )


def _snapshot_fee_policy_v1(policy: object) -> ZDEXFeeAllocationPolicyV1:
    if type(policy) is not ZDEXFeeAllocationPolicyV1:
        raise TypeError("ZDEX tokenomics fee policy must be exact typed data")
    typed_policy = cast(ZDEXFeeAllocationPolicyV1, policy)
    _require_exact_dataclass_scalars_v1(
        typed_policy,
        name="ZDEX tokenomics fee policy",
        tuple_fields=frozenset({"shares"}),
    )
    if type(typed_policy.shares) is not tuple or any(
        type(share) is not ZDEXFeeShareV1 for share in typed_policy.shares
    ):
        raise TypeError("ZDEX tokenomics fee shares must be exact typed data")
    shares = []
    for share in typed_policy.shares:
        if (
            type(share.destination) is not ZDEXFeeDestinationV1
            or type(share.share_bps) is not int
        ):
            raise TypeError("ZDEX tokenomics fee shares must contain exact scalar data")
        shares.append(replace(share))
    return replace(typed_policy, shares=tuple(shares))


def snapshot_zdex_tokenomics_module_journal_v1(
    journal: object,
) -> LaneModuleTransitionJournalV1:
    return _snapshot_exact_scalar_dataclass_v1(
        journal,
        LaneModuleTransitionJournalV1,
        name="ZDEX tokenomics module journal",
    )


def snapshot_zdex_tokenomics_burn_context_v1(
    context: object,
) -> ZDEXTokenomicsBurnCoordinatorContextV1:
    return _snapshot_exact_scalar_dataclass_v1(
        context,
        ZDEXTokenomicsBurnCoordinatorContextV1,
        name="ZDEX tokenomics coordinator context",
    )


def snapshot_zdex_tokenomics_burn_port_v1(
    port: object,
) -> ZDEXTokenomicsBurnPrivatePortV1:
    return _snapshot_exact_scalar_dataclass_v1(
        port,
        ZDEXTokenomicsBurnPrivatePortV1,
        name="ZDEX tokenomics burn private port",
    )


def snapshot_zdex_tokenomics_fee_context_v1(
    context: object,
) -> ZDEXTokenomicsFeeAllocationCoordinatorContextV1:
    return _snapshot_exact_scalar_dataclass_v1(
        context,
        ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
        name="ZDEX tokenomics fee coordinator context",
    )


def snapshot_zdex_tokenomics_fee_port_v1(
    port: object,
) -> ZDEXTokenomicsFeeAllocationPrivatePortV1:
    return _snapshot_exact_scalar_dataclass_v1(
        port,
        ZDEXTokenomicsFeeAllocationPrivatePortV1,
        name="ZDEX tokenomics fee private port",
    )


def _snapshot_supply_state_v1(state: object) -> ZDEXSupplyStateV1:
    if type(state) is not ZDEXSupplyStateV1:
        raise TypeError("ZDEX tokenomics supply state must be exact typed data")
    typed_state = cast(ZDEXSupplyStateV1, state)
    _require_exact_dataclass_scalars_v1(
        typed_state,
        name="ZDEX tokenomics supply state",
        tuple_fields=frozenset({"buckets"}),
    )
    buckets = []
    for bucket in _require_exact_tuple_items(
        typed_state.buckets,
        ZDEXAmountBucketV1,
        "ZDEX tokenomics supply buckets",
    ):
        _require_exact_dataclass_scalars_v1(
            bucket,
            name="ZDEX tokenomics supply bucket",
        )
        buckets.append(replace(bucket))
    return replace(typed_state, buckets=tuple(buckets))


def snapshot_zdex_tokenomics_lane_state_v1(
    state: object,
) -> ZDEXTokenomicsLaneStateV1:
    if type(state) is not ZDEXTokenomicsLaneStateV1:
        raise TypeError("ZDEX tokenomics lane state must be exact typed data")
    typed_state = cast(ZDEXTokenomicsLaneStateV1, state)
    if type(typed_state.fee_allocation_states) is not tuple:
        raise TypeError("ZDEX tokenomics fee states must be an exact tuple")
    for field_name in (
        "staking_state_root",
        "host_claims_state_root",
        "treasury_claims_state_root",
        "proof_rewards_state_root",
        "cover_reserve_state_root",
        "lp_rebates_state_root",
    ):
        if type(getattr(typed_state, field_name)) is not str:
            raise TypeError(
                f"ZDEX tokenomics lane state.{field_name} must be an exact primitive"
            )
    fee_states = tuple(
        _snapshot_fee_state_v1(fee_state)
        for fee_state in _require_exact_tuple_items(
            typed_state.fee_allocation_states,
            ZDEXFeeStateV1,
            "ZDEX tokenomics fee states",
        )
    )
    return replace(
        typed_state,
        supply_state=_snapshot_supply_state_v1(typed_state.supply_state),
        fee_allocation_states=fee_states,
    )


def snapshot_zdex_tokenomics_burn_journal_v1(
    journal: object,
) -> ZDEXBurnJournalV1:
    return _snapshot_exact_scalar_dataclass_v1(
        journal,
        ZDEXBurnJournalV1,
        name="ZDEX tokenomics burn journal",
    )


def snapshot_zdex_tokenomics_effect_plan_v1(
    effect_plan: object,
) -> GlobalEconomicEffectPlanV1:
    if type(effect_plan) is not GlobalEconomicEffectPlanV1:
        raise TypeError("ZDEX tokenomics effect plan must be exact typed data")
    return _snapshot_effect_plan_v1(effect_plan)


def snapshot_zdex_tokenomics_fee_allocation_v1(
    allocation: object,
) -> ZDEXFeeAllocationAcceptedV1:
    if type(allocation) is not ZDEXFeeAllocationAcceptedV1:
        raise TypeError("ZDEX tokenomics fee allocation must be exact typed data")
    typed_allocation = cast(ZDEXFeeAllocationAcceptedV1, allocation)
    return replace(
        typed_allocation,
        pre_state=_snapshot_fee_state_v1(typed_allocation.pre_state),
        post_state=_snapshot_fee_state_v1(typed_allocation.post_state),
        effects=snapshot_zdex_tokenomics_effect_plan_v1(typed_allocation.effects),
        occurrence=_snapshot_fee_journal_v1(typed_allocation.occurrence),
    )


def snapshot_zdex_tokenomics_fee_policy_v1(
    policy: object,
) -> ZDEXFeeAllocationPolicyV1:
    return _snapshot_fee_policy_v1(policy)


__all__ = [
    "snapshot_zdex_tokenomics_burn_context_v1",
    "snapshot_zdex_tokenomics_burn_journal_v1",
    "snapshot_zdex_tokenomics_burn_port_v1",
    "snapshot_zdex_tokenomics_effect_plan_v1",
    "snapshot_zdex_tokenomics_fee_allocation_v1",
    "snapshot_zdex_tokenomics_fee_context_v1",
    "snapshot_zdex_tokenomics_fee_policy_v1",
    "snapshot_zdex_tokenomics_fee_port_v1",
    "snapshot_zdex_tokenomics_lane_state_v1",
    "snapshot_zdex_tokenomics_module_journal_v1",
]
