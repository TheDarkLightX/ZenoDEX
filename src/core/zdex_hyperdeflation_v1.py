"""Integer-safe, unmounted ZDEX hyperdeflation transition core.

The module keeps the public V1 import surface while delegating closed values,
arithmetic, and self-validating results to narrow sibling modules. It proves no
route authenticity, complete global bucket coverage, migration authority,
market liveness, or production settlement authority.
"""

from __future__ import annotations

from dataclasses import replace

from .global_settlement_types_v1 import MAX_ATOMS_V1, MAX_U64_V1
from .zdex_hyperdeflation_math_v1 import (
    burned_bucket_projection_v1,
    compute_zdex_burn_capacity_v1,
    retained_supply_atoms_v1,
)
from .zdex_hyperdeflation_results_v1 import (
    ZDEXPrecisionRescaleAcceptedV1,
    ZDEXPrecisionRescaleRejectedV1,
    ZDEXPrecisionRescaleResultV1,
    ZDEXPurchaseAndBurnAcceptedV1,
    ZDEXPurchaseAndBurnRejectedV1,
    ZDEXPurchaseAndBurnResultV1,
)
from .zdex_hyperdeflation_types_v1 import (
    MAX_DECIMAL_SCALE_STEP_V1,
    ZDEXAmountBucketV1,
    ZDEXBucketScaleV1,
    ZDEXBurnCapacityV1,
    ZDEXBurnEffectV1,
    ZDEXBurnRejectCodeV1,
    ZDEXBurnRouteContextV1,
    ZDEXHyperdeflationPolicyV1,
    ZDEXPrecisionEffectV1,
    ZDEXPrecisionRejectCodeV1,
    ZDEXPrecisionRescaleCommandV1,
    ZDEXPurchaseAndBurnCommandV1,
    ZDEXSupplyStateV1,
)


def transition_zdex_purchase_and_burn_v1(
    policy: ZDEXHyperdeflationPolicyV1,
    state: ZDEXSupplyStateV1,
    context: ZDEXBurnRouteContextV1,
    command: ZDEXPurchaseAndBurnCommandV1,
) -> ZDEXPurchaseAndBurnResultV1:
    """Apply the route-bound burn projection or return an exact no-effect reject."""

    _require_exact_burn_types(policy, state, context, command)
    reject_code, capacity = _burn_admission(policy, state, context, command)
    if reject_code is not None:
        return _burn_reject(reject_code, state)
    if capacity is None:
        raise AssertionError("accepted ZDEX burn admission requires capacity")
    return _apply_burn(policy, state, context, command, capacity)


def transition_zdex_precision_rescale_v1(
    policy: ZDEXHyperdeflationPolicyV1,
    state: ZDEXSupplyStateV1,
    command: ZDEXPrecisionRescaleCommandV1,
) -> ZDEXPrecisionRescaleResultV1:
    """Exactly rescale all projected live ZDEX buckets by a power of ten."""

    _require_exact_precision_types(policy, state, command)
    reject_code = _precision_admission_code(policy, state, command)
    if reject_code is not None:
        return _precision_reject(reject_code, state)
    scale_factor = 10**command.additional_decimals
    if _precision_overflows(state, scale_factor):
        return _precision_reject(ZDEXPrecisionRejectCodeV1.ATOM_OVERFLOW, state)
    return _apply_precision_rescale(policy, state, command, scale_factor)


def _burn_admission(
    policy: ZDEXHyperdeflationPolicyV1,
    state: ZDEXSupplyStateV1,
    context: ZDEXBurnRouteContextV1,
    command: ZDEXPurchaseAndBurnCommandV1,
) -> tuple[ZDEXBurnRejectCodeV1 | None, ZDEXBurnCapacityV1 | None]:
    if (
        policy.asset_id != state.asset_id
        or policy.policy_root != state.policy_root
        or context.policy_root != policy.policy_root
    ):
        return ZDEXBurnRejectCodeV1.POLICY_MISMATCH, None
    if command.expected_pre_state_root != state.state_root:
        return ZDEXBurnRejectCodeV1.STALE_STATE, None
    if command.expected_precision_epoch != state.precision_epoch:
        return ZDEXBurnRejectCodeV1.PRECISION_EPOCH_MISMATCH, None
    if command.purchased_zdex_atoms == 0:
        return ZDEXBurnRejectCodeV1.ZERO_PURCHASE, None
    if not _purchase_binding_matches(context, command):
        return ZDEXBurnRejectCodeV1.PURCHASE_BINDING_MISMATCH, None
    capacity = compute_zdex_burn_capacity_v1(
        policy,
        state,
        context,
        source_bucket_id=command.source_bucket_id,
    )
    if capacity is None:
        return ZDEXBurnRejectCodeV1.SOURCE_BUCKET_UNKNOWN, None
    exhausted = _exhausted_burn_code(capacity)
    if exhausted is not None:
        return exhausted, capacity
    if command.purchased_zdex_atoms > capacity.maximum_burn_atoms:
        return ZDEXBurnRejectCodeV1.PURCHASE_EXCEEDS_BURN_CAPACITY, capacity
    return None, capacity


def _purchase_binding_matches(
    context: ZDEXBurnRouteContextV1,
    command: ZDEXPurchaseAndBurnCommandV1,
) -> bool:
    return (
        command.expected_purchase_occurrence_root == context.purchase_occurrence_root
        and command.source_bucket_id == context.burn_source_bucket_id
        and command.purchased_zdex_atoms == context.purchased_zdex_atoms
    )


def _apply_burn(
    policy: ZDEXHyperdeflationPolicyV1,
    state: ZDEXSupplyStateV1,
    context: ZDEXBurnRouteContextV1,
    command: ZDEXPurchaseAndBurnCommandV1,
    capacity: ZDEXBurnCapacityV1,
) -> ZDEXPurchaseAndBurnAcceptedV1:
    burn_atoms = command.purchased_zdex_atoms
    post_state = replace(
        state,
        live_supply_atoms=state.live_supply_atoms - burn_atoms,
        buckets=burned_bucket_projection_v1(
            state,
            source_bucket_id=command.source_bucket_id,
            burn_atoms=burn_atoms,
        ),
    )
    effect = ZDEXBurnEffectV1(
        purchase_occurrence_root=context.purchase_occurrence_root,
        source_bucket_id=command.source_bucket_id,
        source_debit_atoms=burn_atoms,
        authorized_burn_atoms=burn_atoms,
    )
    return ZDEXPurchaseAndBurnAcceptedV1(
        policy=policy,
        route_context=context,
        pre_state=state,
        post_state=post_state,
        capacity=capacity,
        effect=effect,
    )


def _precision_admission_code(
    policy: ZDEXHyperdeflationPolicyV1,
    state: ZDEXSupplyStateV1,
    command: ZDEXPrecisionRescaleCommandV1,
) -> ZDEXPrecisionRejectCodeV1 | None:
    if policy.asset_id != state.asset_id or policy.policy_root != state.policy_root:
        return ZDEXPrecisionRejectCodeV1.POLICY_MISMATCH
    if command.expected_pre_state_root != state.state_root:
        return ZDEXPrecisionRejectCodeV1.STALE_STATE
    if command.expected_precision_epoch != state.precision_epoch:
        return ZDEXPrecisionRejectCodeV1.PRECISION_EPOCH_MISMATCH
    if command.additional_decimals == 0:
        return ZDEXPrecisionRejectCodeV1.ZERO_DECIMAL_STEP
    if (
        command.additional_decimals > policy.maximum_decimal_step
        or command.additional_decimals > MAX_DECIMAL_SCALE_STEP_V1
    ):
        return ZDEXPrecisionRejectCodeV1.DECIMAL_STEP_EXCEEDS_POLICY
    if state.decimals + command.additional_decimals > policy.maximum_decimals:
        return ZDEXPrecisionRejectCodeV1.MAXIMUM_DECIMALS_EXCEEDED
    if state.precision_epoch == MAX_U64_V1:
        return ZDEXPrecisionRejectCodeV1.EPOCH_COUNTER_EXHAUSTED
    return None


def _precision_overflows(state: ZDEXSupplyStateV1, scale_factor: int) -> bool:
    if state.live_supply_atoms > MAX_ATOMS_V1 // scale_factor:
        return True
    return any(
        bucket.amount_atoms > MAX_ATOMS_V1 // scale_factor
        for bucket in state.buckets
    )


def _apply_precision_rescale(
    policy: ZDEXHyperdeflationPolicyV1,
    state: ZDEXSupplyStateV1,
    command: ZDEXPrecisionRescaleCommandV1,
    scale_factor: int,
) -> ZDEXPrecisionRescaleAcceptedV1:
    bucket_scales = tuple(
        ZDEXBucketScaleV1(
            bucket_id=bucket.bucket_id,
            before_atoms=bucket.amount_atoms,
            after_atoms=bucket.amount_atoms * scale_factor,
        )
        for bucket in state.buckets
    )
    post_state = replace(
        state,
        decimals=state.decimals + command.additional_decimals,
        precision_epoch=state.precision_epoch + 1,
        live_supply_atoms=state.live_supply_atoms * scale_factor,
        buckets=tuple(
            ZDEXAmountBucketV1(row.bucket_id, row.after_atoms)
            for row in bucket_scales
        ),
    )
    effect = ZDEXPrecisionEffectV1(
        scale_factor=scale_factor,
        supply_before_atoms=state.live_supply_atoms,
        supply_after_atoms=post_state.live_supply_atoms,
        bucket_scales=bucket_scales,
    )
    return ZDEXPrecisionRescaleAcceptedV1(policy, state, post_state, effect)


def _require_exact_burn_types(
    policy: object,
    state: object,
    context: object,
    command: object,
) -> None:
    if type(policy) is not ZDEXHyperdeflationPolicyV1:
        raise TypeError("ZDEX burn transition requires an exact policy")
    if type(state) is not ZDEXSupplyStateV1:
        raise TypeError("ZDEX burn transition requires an exact state")
    if type(context) is not ZDEXBurnRouteContextV1:
        raise TypeError("ZDEX burn transition requires an exact route context")
    if type(command) is not ZDEXPurchaseAndBurnCommandV1:
        raise TypeError("ZDEX burn transition requires an exact command")


def _require_exact_precision_types(
    policy: object,
    state: object,
    command: object,
) -> None:
    if type(policy) is not ZDEXHyperdeflationPolicyV1:
        raise TypeError("ZDEX precision transition requires an exact policy")
    if type(state) is not ZDEXSupplyStateV1:
        raise TypeError("ZDEX precision transition requires an exact state")
    if type(command) is not ZDEXPrecisionRescaleCommandV1:
        raise TypeError("ZDEX precision transition requires an exact command")


def _exhausted_burn_code(
    capacity: ZDEXBurnCapacityV1,
) -> ZDEXBurnRejectCodeV1 | None:
    if capacity.ratio_headroom_atoms == 0:
        return ZDEXBurnRejectCodeV1.PRECISION_RESCALE_REQUIRED
    if capacity.source_headroom_atoms == 0:
        return ZDEXBurnRejectCodeV1.SOURCE_RESERVE_FLOOR_REACHED
    if capacity.epoch_headroom_atoms == 0:
        return ZDEXBurnRejectCodeV1.EPOCH_BURN_CAP_REACHED
    if capacity.route_headroom_atoms == 0:
        return ZDEXBurnRejectCodeV1.ROUTE_OUTPUT_CAP_ZERO
    return None


def _burn_reject(
    code: ZDEXBurnRejectCodeV1,
    state: ZDEXSupplyStateV1,
) -> ZDEXPurchaseAndBurnRejectedV1:
    return ZDEXPurchaseAndBurnRejectedV1(code=code, pre_state=state, post_state=state)


def _precision_reject(
    code: ZDEXPrecisionRejectCodeV1,
    state: ZDEXSupplyStateV1,
) -> ZDEXPrecisionRescaleRejectedV1:
    return ZDEXPrecisionRescaleRejectedV1(code=code, pre_state=state, post_state=state)


__all__ = [
    "MAX_DECIMAL_SCALE_STEP_V1",
    "ZDEXAmountBucketV1",
    "ZDEXBucketScaleV1",
    "ZDEXBurnCapacityV1",
    "ZDEXBurnEffectV1",
    "ZDEXBurnRejectCodeV1",
    "ZDEXBurnRouteContextV1",
    "ZDEXHyperdeflationPolicyV1",
    "ZDEXPrecisionEffectV1",
    "ZDEXPrecisionRejectCodeV1",
    "ZDEXPrecisionRescaleAcceptedV1",
    "ZDEXPrecisionRescaleCommandV1",
    "ZDEXPrecisionRescaleRejectedV1",
    "ZDEXPrecisionRescaleResultV1",
    "ZDEXPurchaseAndBurnAcceptedV1",
    "ZDEXPurchaseAndBurnCommandV1",
    "ZDEXPurchaseAndBurnRejectedV1",
    "ZDEXPurchaseAndBurnResultV1",
    "ZDEXSupplyStateV1",
    "compute_zdex_burn_capacity_v1",
    "retained_supply_atoms_v1",
    "transition_zdex_precision_rescale_v1",
    "transition_zdex_purchase_and_burn_v1",
]
