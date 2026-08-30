"""Owned SHADOW profile capability for ZDEX purchase-burn V3 composition."""

from __future__ import annotations

from dataclasses import dataclass, replace

from .global_economic_capability_profile_binding_v1 import (
    snapshot_economic_policy_registry_v1,
)
from .global_economic_profile_snapshot_v1 import (
    _snapshot_coordinator_release_v1,
    _snapshot_lane_release_v1,
    _snapshot_route_release_v1,
    snapshot_economic_profile_v1,
)
from .global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteReleaseV1,
)
from .zdex_buyback_price_safety_v1 import (
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
    ZDEXBuybackPriceSafetyPolicyV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
    ZDEXBuybackExecutionPolicyV1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
)

_GOVERNED_PURCHASE_BURN_ROUTE_TOKEN_V2 = object()


@dataclass(frozen=True, slots=True)
class _GovernedZDEXPurchaseBurnRouteFieldsV2:
    profile: EconomicProfileSnapshotV1
    route_release: RouteReleaseV1
    purchase_module_release: LaneModuleReleaseV1
    burn_module_release: LaneModuleReleaseV1
    purchase_coordinator_release: LaneCoordinatorReleaseV1
    burn_coordinator_release: LaneCoordinatorReleaseV1
    policy_registry: EconomicPolicyRegistryV1
    buyback_execution_policy: ZDEXBuybackExecutionPolicyV1
    price_safety_policy: ZDEXBuybackPriceSafetyPolicyV1


class GovernedZDEXPurchaseBurnRouteV2:
    """Opaque profile-selected SHADOW route and policy graph."""

    __slots__ = ("_fields", "_trusted_profile_id", "_trusted_authority_epoch")
    _fields: _GovernedZDEXPurchaseBurnRouteFieldsV2
    _trusted_profile_id: str
    _trusted_authority_epoch: int

    def __init__(
        self,
        token: object,
        fields: _GovernedZDEXPurchaseBurnRouteFieldsV2,
        trusted_profile_id: str,
        trusted_authority_epoch: int,
    ) -> None:
        if token is not _GOVERNED_PURCHASE_BURN_ROUTE_TOKEN_V2:
            raise TypeError("governed ZDEX purchase-burn V2 route is verifier-constructed")
        if type(fields) is not _GovernedZDEXPurchaseBurnRouteFieldsV2:
            raise TypeError("governed ZDEX purchase-burn V2 fields are not closed")
        if type(trusted_profile_id) is not str or type(trusted_authority_epoch) is not int:
            raise TypeError("governed ZDEX purchase-burn V2 anchor is not exact typed data")
        object.__setattr__(self, "_fields", fields)
        object.__setattr__(self, "_trusted_profile_id", trusted_profile_id)
        object.__setattr__(self, "_trusted_authority_epoch", trusted_authority_epoch)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("governed ZDEX purchase-burn V2 route is immutable")


class _GovernedZDEXPurchaseBurnAnchorMismatchV2(ValueError):
    """Internal signal for a retained wrapper whose selected graph changed."""


def _registered_buyback_route_v2(
    profile: EconomicProfileSnapshotV1,
) -> RouteReleaseV1:
    routes = tuple(
        route
        for route in profile.route_registry.routes
        if route.command_kind == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
    )
    if len(routes) != 1:
        raise ValueError("ZDEX purchase-burn V2 governed route is absent or ambiguous")
    return routes[0]


def _require_governed_route_shapes_v2(
    fields: _GovernedZDEXPurchaseBurnRouteFieldsV2,
) -> None:
    route = fields.route_release
    purchase = fields.purchase_module_release
    burn = fields.burn_module_release
    if (
        route.status is not ReleaseStatusV1.SHADOW
        or route.accepts_new_objects
        or route.command_kind != PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
        or route.ordered_lanes
        != (LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS)
        or route.module_release_ids != (purchase.release_id, burn.release_id)
        or route.dependency_roles
        != (AMM_PURCHASE_OUTPUT_ROLE_V1, ZDEX_BURN_INPUT_ROLE_V1)
        or route.port_schema_roots
        != (zdex_amm_purchase_port_schema_root_v1(), zdex_burn_port_schema_root_v1())
    ):
        raise ValueError("ZDEX purchase-burn V2 governed route shape mismatch")
    for release, lane_id in (
        (purchase, LaneIdV1.SPOT_LIQUIDITY),
        (burn, LaneIdV1.ZDEX_TOKENOMICS),
    ):
        if (
            release.status is not ReleaseStatusV1.SHADOW
            or release.accepts_new_objects
            or release.lane_id is not lane_id
            or PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1 not in release.command_variants
        ):
            raise ValueError("ZDEX purchase-burn V2 module release shape mismatch")
    for coordinator, lane_id in (
        (fields.purchase_coordinator_release, LaneIdV1.SPOT_LIQUIDITY),
        (fields.burn_coordinator_release, LaneIdV1.ZDEX_TOKENOMICS),
    ):
        if (
            coordinator.status is not ReleaseStatusV1.SHADOW
            or coordinator.accepts_new_objects
            or coordinator.lane_id is not lane_id
        ):
            raise ValueError("ZDEX purchase-burn V2 coordinator shape mismatch")


def _require_policy_bindings_v2(
    profile: EconomicProfileSnapshotV1,
    registry: EconomicPolicyRegistryV1,
    execution_policy: ZDEXBuybackExecutionPolicyV1,
    price_policy: ZDEXBuybackPriceSafetyPolicyV1,
) -> RouteReleaseV1:
    if registry.registry_root != profile.policy_registry_root:
        raise ValueError("ZDEX purchase-burn V2 policy registry mismatch")
    execution_binding = registry.require_binding(
        policy_kind=ZDEX_BUYBACK_EXECUTION_POLICY_KIND_V1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    )
    price_binding = registry.require_binding(
        policy_kind=ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    )
    route = _registered_buyback_route_v2(profile)
    if execution_binding.policy_root != execution_policy.policy_root:
        raise ValueError("ZDEX purchase-burn V2 execution policy binding mismatch")
    if (
        price_binding.policy_root != price_policy.policy_root
        or route.oracle_policy_root != price_policy.policy_root
    ):
        raise ValueError("ZDEX purchase-burn V2 price policy binding mismatch")
    return route


def bind_zdex_purchase_burn_shadow_profile_v2(
    *,
    expected_profile_id: str,
    expected_authority_epoch: int,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    buyback_execution_policy: ZDEXBuybackExecutionPolicyV1,
    price_safety_policy: ZDEXBuybackPriceSafetyPolicyV1,
) -> GovernedZDEXPurchaseBurnRouteV2:
    """Own and select the exact V3 route graph from a trusted profile anchor."""

    if type(expected_profile_id) is not str or type(expected_authority_epoch) is not int:
        raise TypeError("ZDEX purchase-burn V2 expected anchor is not exact typed data")
    owned_profile = snapshot_economic_profile_v1(profile)
    owned_registry = snapshot_economic_policy_registry_v1(policy_registry)
    if type(buyback_execution_policy) is not ZDEXBuybackExecutionPolicyV1:
        raise TypeError("ZDEX purchase-burn V2 execution policy is not exact typed data")
    if type(price_safety_policy) is not ZDEXBuybackPriceSafetyPolicyV1:
        raise TypeError("ZDEX purchase-burn V2 price policy is not exact typed data")
    execution_policy = replace(buyback_execution_policy)
    price_policy = replace(price_safety_policy)
    if (
        owned_profile.profile_id != expected_profile_id
        or owned_profile.authority_epoch != expected_authority_epoch
        or owned_profile.status is not ProfileStatusV1.SHADOW
    ):
        raise ValueError("ZDEX purchase-burn V2 trusted profile mismatch")
    route = _require_policy_bindings_v2(
        owned_profile,
        owned_registry,
        execution_policy,
        price_policy,
    )
    fields = _GovernedZDEXPurchaseBurnRouteFieldsV2(
        owned_profile,
        route,
        owned_profile.lane_registry.release_for(LaneIdV1.SPOT_LIQUIDITY),
        owned_profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS),
        owned_profile.lane_coordinator_registry.release_for(LaneIdV1.SPOT_LIQUIDITY),
        owned_profile.lane_coordinator_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS),
        owned_registry,
        execution_policy,
        price_policy,
    )
    _require_governed_route_shapes_v2(fields)
    return GovernedZDEXPurchaseBurnRouteV2(
        _GOVERNED_PURCHASE_BURN_ROUTE_TOKEN_V2,
        fields,
        expected_profile_id,
        expected_authority_epoch,
    )


def _snapshot_governed_route_v2(
    governed: GovernedZDEXPurchaseBurnRouteV2,
) -> GovernedZDEXPurchaseBurnRouteV2:
    if type(governed) is not GovernedZDEXPurchaseBurnRouteV2:
        raise TypeError("ZDEX purchase-burn V2 governed route must be verifier-constructed")
    fields = governed._fields
    if type(fields) is not _GovernedZDEXPurchaseBurnRouteFieldsV2:
        raise TypeError("ZDEX purchase-burn V2 governed fields are not closed")
    owned = bind_zdex_purchase_burn_shadow_profile_v2(
        expected_profile_id=governed._trusted_profile_id,
        expected_authority_epoch=governed._trusted_authority_epoch,
        profile=fields.profile,
        policy_registry=fields.policy_registry,
        buyback_execution_policy=fields.buyback_execution_policy,
        price_safety_policy=fields.price_safety_policy,
    )
    expected = owned._fields
    if (
        _snapshot_route_release_v1(fields.route_release) != expected.route_release
        or _snapshot_lane_release_v1(fields.purchase_module_release)
        != expected.purchase_module_release
        or _snapshot_lane_release_v1(fields.burn_module_release)
        != expected.burn_module_release
        or _snapshot_coordinator_release_v1(fields.purchase_coordinator_release)
        != expected.purchase_coordinator_release
        or _snapshot_coordinator_release_v1(fields.burn_coordinator_release)
        != expected.burn_coordinator_release
    ):
        raise _GovernedZDEXPurchaseBurnAnchorMismatchV2(
            "ZDEX purchase-burn V2 governed selection changed"
        )
    return owned


__all__ = [
    "GovernedZDEXPurchaseBurnRouteV2",
    "bind_zdex_purchase_burn_shadow_profile_v2",
]
