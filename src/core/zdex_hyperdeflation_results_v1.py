"""Self-validating result values for ZDEX hyperdeflation transitions."""

from __future__ import annotations

from dataclasses import dataclass

from .zdex_hyperdeflation_math_v1 import (
    burned_bucket_projection_v1,
    compute_zdex_burn_capacity_v1,
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
    ZDEXSupplyStateV1,
)


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseAndBurnAcceptedV1:
    policy: ZDEXHyperdeflationPolicyV1
    route_context: ZDEXBurnRouteContextV1
    pre_state: ZDEXSupplyStateV1
    post_state: ZDEXSupplyStateV1
    capacity: ZDEXBurnCapacityV1
    effect: ZDEXBurnEffectV1

    def __post_init__(self) -> None:
        _require_burn_result_types(self)
        _require_burn_policy_and_route(self)
        expected_capacity = compute_zdex_burn_capacity_v1(
            self.policy,
            self.pre_state,
            self.route_context,
            source_bucket_id=self.route_context.burn_source_bucket_id,
        )
        if expected_capacity is None or self.capacity != expected_capacity:
            raise ValueError("ZDEX accepted burn capacity was not recomputed exactly")
        _require_burn_post_state(self)


@dataclass(frozen=True, slots=True)
class ZDEXPurchaseAndBurnRejectedV1:
    code: ZDEXBurnRejectCodeV1
    pre_state: ZDEXSupplyStateV1
    post_state: ZDEXSupplyStateV1
    effects: tuple[ZDEXBurnEffectV1, ...] = ()

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXBurnRejectCodeV1:
            raise TypeError("ZDEX burn reject code is not closed")
        if (
            type(self.pre_state) is not ZDEXSupplyStateV1
            or type(self.post_state) is not ZDEXSupplyStateV1
        ):
            raise TypeError("ZDEX rejected burn requires exact supply states")
        if type(self.effects) is not tuple or any(
            type(effect) is not ZDEXBurnEffectV1 for effect in self.effects
        ):
            raise TypeError("ZDEX rejected burn effects are not closed")
        if self.pre_state is not self.post_state and self.pre_state != self.post_state:
            raise ValueError("ZDEX rejected burn changed state")
        if self.pre_state.state_root != self.post_state.state_root or self.effects:
            raise ValueError("ZDEX rejected burn carried a state change or effect")


ZDEXPurchaseAndBurnResultV1 = (
    ZDEXPurchaseAndBurnAcceptedV1 | ZDEXPurchaseAndBurnRejectedV1
)


@dataclass(frozen=True, slots=True)
class ZDEXPrecisionRescaleAcceptedV1:
    policy: ZDEXHyperdeflationPolicyV1
    pre_state: ZDEXSupplyStateV1
    post_state: ZDEXSupplyStateV1
    effect: ZDEXPrecisionEffectV1

    def __post_init__(self) -> None:
        _require_precision_result_types(self)
        _require_precision_policy_and_epoch(self)
        _require_precision_projection(self)


@dataclass(frozen=True, slots=True)
class ZDEXPrecisionRescaleRejectedV1:
    code: ZDEXPrecisionRejectCodeV1
    pre_state: ZDEXSupplyStateV1
    post_state: ZDEXSupplyStateV1
    effects: tuple[ZDEXPrecisionEffectV1, ...] = ()

    def __post_init__(self) -> None:
        if type(self.code) is not ZDEXPrecisionRejectCodeV1:
            raise TypeError("ZDEX precision reject code is not closed")
        if (
            type(self.pre_state) is not ZDEXSupplyStateV1
            or type(self.post_state) is not ZDEXSupplyStateV1
        ):
            raise TypeError("ZDEX rejected precision rescale requires exact supply states")
        if type(self.effects) is not tuple or any(
            type(effect) is not ZDEXPrecisionEffectV1 for effect in self.effects
        ):
            raise TypeError("ZDEX rejected precision effects are not closed")
        if self.pre_state is not self.post_state and self.pre_state != self.post_state:
            raise ValueError("ZDEX rejected precision transition changed state")
        if self.pre_state.state_root != self.post_state.state_root or self.effects:
            raise ValueError("ZDEX rejected precision transition carried state or effects")


ZDEXPrecisionRescaleResultV1 = (
    ZDEXPrecisionRescaleAcceptedV1 | ZDEXPrecisionRescaleRejectedV1
)


def _require_burn_result_types(result: ZDEXPurchaseAndBurnAcceptedV1) -> None:
    if type(result.policy) is not ZDEXHyperdeflationPolicyV1:
        raise TypeError("ZDEX accepted burn requires an exact policy")
    if type(result.route_context) is not ZDEXBurnRouteContextV1:
        raise TypeError("ZDEX accepted burn requires an exact route context")
    if (
        type(result.pre_state) is not ZDEXSupplyStateV1
        or type(result.post_state) is not ZDEXSupplyStateV1
    ):
        raise TypeError("ZDEX accepted burn requires exact supply states")
    if (
        type(result.capacity) is not ZDEXBurnCapacityV1
        or type(result.effect) is not ZDEXBurnEffectV1
    ):
        raise TypeError("ZDEX accepted burn requires exact capacity and effect values")


def _require_burn_policy_and_route(result: ZDEXPurchaseAndBurnAcceptedV1) -> None:
    if (
        result.policy.asset_id != result.pre_state.asset_id
        or result.policy.policy_root != result.pre_state.policy_root
        or result.route_context.policy_root != result.policy.policy_root
    ):
        raise ValueError("ZDEX accepted burn policy binding is inconsistent")
    if result.pre_state.decimals > result.policy.maximum_decimals:
        raise ValueError("ZDEX accepted burn state is outside its policy envelope")
    if result.route_context.burn_budget_epoch != result.pre_state.burn_budget_epoch:
        raise ValueError("ZDEX accepted burn budget epoch is inconsistent")
    if (
        result.effect.purchase_occurrence_root
        != result.route_context.purchase_occurrence_root
        or result.effect.source_bucket_id
        != result.route_context.burn_source_bucket_id
        or result.effect.authorized_burn_atoms
        != result.route_context.purchased_zdex_atoms
    ):
        raise ValueError("ZDEX accepted burn route binding is inconsistent")


def _require_burn_post_state(result: ZDEXPurchaseAndBurnAcceptedV1) -> None:
    burn = result.effect.authorized_burn_atoms
    if burn > result.capacity.maximum_burn_atoms:
        raise ValueError("ZDEX accepted burn exceeds computed capacity")
    if result.pre_state.asset_id != result.post_state.asset_id:
        raise ValueError("ZDEX accepted burn changed asset identity")
    if result.pre_state.policy_root != result.post_state.policy_root:
        raise ValueError("ZDEX accepted burn changed policy identity")
    if result.pre_state.decimals != result.post_state.decimals:
        raise ValueError("ZDEX accepted burn changed decimal precision")
    if result.pre_state.precision_epoch != result.post_state.precision_epoch:
        raise ValueError("ZDEX accepted burn changed precision epoch")
    if result.pre_state.burn_budget_epoch != result.post_state.burn_budget_epoch:
        raise ValueError("ZDEX accepted burn changed burn budget epoch")
    if result.post_state.live_supply_atoms != result.pre_state.live_supply_atoms - burn:
        raise ValueError("ZDEX accepted burn has the wrong post supply")
    if result.post_state.live_supply_atoms < result.capacity.retained_supply_atoms:
        raise ValueError("ZDEX accepted burn violates retained supply")
    if (
        result.post_state.remaining_epoch_burn_cap_atoms
        != result.pre_state.remaining_epoch_burn_cap_atoms - burn
    ):
        raise ValueError("ZDEX accepted burn did not consume epoch capacity")
    expected_buckets = burned_bucket_projection_v1(
        result.pre_state,
        source_bucket_id=result.effect.source_bucket_id,
        burn_atoms=burn,
    )
    if result.post_state.buckets != expected_buckets:
        raise ValueError("ZDEX accepted burn has the wrong bucket transition")


def _require_precision_result_types(result: ZDEXPrecisionRescaleAcceptedV1) -> None:
    if type(result.policy) is not ZDEXHyperdeflationPolicyV1:
        raise TypeError("ZDEX accepted precision rescale requires an exact policy")
    if (
        type(result.pre_state) is not ZDEXSupplyStateV1
        or type(result.post_state) is not ZDEXSupplyStateV1
    ):
        raise TypeError("ZDEX accepted precision rescale requires exact supply states")
    if type(result.effect) is not ZDEXPrecisionEffectV1:
        raise TypeError("ZDEX accepted precision rescale requires an exact effect")


def _require_precision_policy_and_epoch(
    result: ZDEXPrecisionRescaleAcceptedV1,
) -> None:
    if (
        result.policy.asset_id != result.pre_state.asset_id
        or result.policy.policy_root != result.pre_state.policy_root
    ):
        raise ValueError("ZDEX accepted precision policy binding is inconsistent")
    if result.post_state.precision_epoch != result.pre_state.precision_epoch + 1:
        raise ValueError("ZDEX precision epoch must advance exactly once")
    if result.post_state.asset_id != result.pre_state.asset_id:
        raise ValueError("ZDEX precision rescale changed asset identity")
    if result.post_state.policy_root != result.pre_state.policy_root:
        raise ValueError("ZDEX precision rescale changed policy identity")
    if result.post_state.burn_budget_epoch != result.pre_state.burn_budget_epoch:
        raise ValueError("ZDEX precision rescale changed burn budget epoch")
    if result.post_state.decimals <= result.pre_state.decimals:
        raise ValueError("ZDEX precision rescale must increase decimals")
    decimal_step = result.post_state.decimals - result.pre_state.decimals
    if decimal_step > MAX_DECIMAL_SCALE_STEP_V1:
        raise ValueError("ZDEX precision decimal step exceeds the global bound")
    if decimal_step > result.policy.maximum_decimal_step:
        raise ValueError("ZDEX precision decimal step exceeds the policy bound")
    if result.post_state.decimals > result.policy.maximum_decimals:
        raise ValueError("ZDEX precision decimals exceed the policy maximum")
    if result.effect.scale_factor != 10**decimal_step:
        raise ValueError("ZDEX precision scale factor does not match decimal step")


def _require_precision_projection(result: ZDEXPrecisionRescaleAcceptedV1) -> None:
    if result.effect.supply_before_atoms != result.pre_state.live_supply_atoms:
        raise ValueError("ZDEX precision effect has the wrong pre-state supply")
    if result.post_state.live_supply_atoms != result.effect.supply_after_atoms:
        raise ValueError("ZDEX precision effect and post-state supply disagree")
    if (
        result.effect.burn_budget_remaining_before_atoms
        != result.pre_state.remaining_epoch_burn_cap_atoms
        or result.effect.burn_budget_remaining_after_atoms
        != result.post_state.remaining_epoch_burn_cap_atoms
    ):
        raise ValueError("ZDEX precision effect has the wrong burn budget")
    expected_scales = tuple(
        ZDEXBucketScaleV1(
            bucket_id=bucket.bucket_id,
            before_atoms=bucket.amount_atoms,
            after_atoms=bucket.amount_atoms * result.effect.scale_factor,
        )
        for bucket in result.pre_state.buckets
    )
    if result.effect.bucket_scales != expected_scales:
        raise ValueError("ZDEX precision effect is not bound to every pre-state bucket")
    expected_buckets = tuple(
        ZDEXAmountBucketV1(row.bucket_id, row.after_atoms)
        for row in expected_scales
    )
    if result.post_state.buckets != expected_buckets:
        raise ValueError("ZDEX precision post-state buckets do not match the effect")


__all__ = [
    "ZDEXPrecisionRescaleAcceptedV1",
    "ZDEXPrecisionRescaleRejectedV1",
    "ZDEXPrecisionRescaleResultV1",
    "ZDEXPurchaseAndBurnAcceptedV1",
    "ZDEXPurchaseAndBurnRejectedV1",
    "ZDEXPurchaseAndBurnResultV1",
]
