"""Pure integer arithmetic and bucket projections for ZDEX hyperdeflation."""

from __future__ import annotations

from .global_settlement_types_v1 import _require_atoms_u128
from .zdex_hyperdeflation_types_v1 import (
    ZDEXAmountBucketV1,
    ZDEXBurnCapacityV1,
    ZDEXBurnRouteContextV1,
    ZDEXHyperdeflationPolicyV1,
    ZDEXSupplyStateV1,
)


def retained_supply_atoms_v1(
    live_supply_atoms: int,
    policy: ZDEXHyperdeflationPolicyV1,
) -> int:
    """Return ceil(p*S/q) using the identity 1+(p*S-1)//q."""

    _require_atoms_u128(live_supply_atoms, name="ZDEX retained supply input")
    if live_supply_atoms == 0:
        raise ValueError("ZDEX retained supply input must be positive")
    if type(policy) is not ZDEXHyperdeflationPolicyV1:
        raise TypeError("ZDEX retained supply requires an exact policy")
    numerator_product = policy.retained_numerator * live_supply_atoms
    retained = 1 + (numerator_product - 1) // policy.retained_denominator
    if not 1 <= retained <= live_supply_atoms:
        raise ArithmeticError("ZDEX retained supply escaped the proved integer bounds")
    return retained


def compute_zdex_burn_capacity_v1(
    policy: ZDEXHyperdeflationPolicyV1,
    state: ZDEXSupplyStateV1,
    context: ZDEXBurnRouteContextV1,
    *,
    source_bucket_id: str,
) -> ZDEXBurnCapacityV1 | None:
    """Return current-epoch capacity, or ``None`` for an unknown source."""

    if type(policy) is not ZDEXHyperdeflationPolicyV1:
        raise TypeError("ZDEX burn capacity requires an exact policy")
    if type(state) is not ZDEXSupplyStateV1:
        raise TypeError("ZDEX burn capacity requires an exact state")
    if type(context) is not ZDEXBurnRouteContextV1:
        raise TypeError("ZDEX burn capacity requires an exact route context")
    source_atoms = state.bucket_atoms(source_bucket_id)
    if source_atoms is None:
        return None
    retained = retained_supply_atoms_v1(state.live_supply_atoms, policy)
    ratio_headroom = state.live_supply_atoms - retained
    source_headroom = max(0, source_atoms - context.source_reserve_floor_atoms)
    maximum_burn = min(
        ratio_headroom,
        source_headroom,
        context.remaining_epoch_burn_cap_atoms,
        context.route_safe_output_cap_atoms,
    )
    return ZDEXBurnCapacityV1(
        retained_supply_atoms=retained,
        ratio_headroom_atoms=ratio_headroom,
        source_headroom_atoms=source_headroom,
        epoch_headroom_atoms=context.remaining_epoch_burn_cap_atoms,
        route_headroom_atoms=context.route_safe_output_cap_atoms,
        maximum_burn_atoms=maximum_burn,
    )


def burned_bucket_projection_v1(
    state: ZDEXSupplyStateV1,
    *,
    source_bucket_id: str,
    burn_atoms: int,
) -> tuple[ZDEXAmountBucketV1, ...]:
    """Debit exactly one source bucket and omit it if its balance reaches zero."""

    source_atoms = state.bucket_atoms(source_bucket_id)
    if source_atoms is None:
        raise ValueError("ZDEX burn source bucket is absent from pre-state")
    if burn_atoms == 0 or burn_atoms > source_atoms:
        raise ValueError("ZDEX burn amount must fit the source bucket")
    remaining_atoms = source_atoms - burn_atoms
    rows: list[ZDEXAmountBucketV1] = []
    for bucket in state.buckets:
        if bucket.bucket_id != source_bucket_id:
            rows.append(bucket)
        elif remaining_atoms > 0:
            rows.append(ZDEXAmountBucketV1(bucket.bucket_id, remaining_atoms))
    return tuple(rows)


__all__ = [
    "burned_bucket_projection_v1",
    "compute_zdex_burn_capacity_v1",
    "retained_supply_atoms_v1",
]
