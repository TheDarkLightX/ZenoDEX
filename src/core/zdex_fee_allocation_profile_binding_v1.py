"""Profile-selected SHADOW releases for ZDEX fee-allocation admission."""

from __future__ import annotations

from dataclasses import dataclass, replace

from .global_settlement_types_v1 import (
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    LaneCoordinatorReleaseV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    ProfileStatusV1,
    ReleaseStatusV1,
    RouteReleaseV1,
)
from .zdex_fee_allocation_types_v1 import (
    FEE_ALLOCATION_OUTPUT_ROLE_V1,
    PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
    ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
    zdex_fee_allocation_port_schema_root_v1,
)
from .zdex_purchase_burn_route_types_v1 import (
    AMM_PURCHASE_OUTPUT_ROLE_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEX_BURN_INPUT_ROLE_V1,
    zdex_amm_purchase_port_schema_root_v1,
    zdex_burn_port_schema_root_v1,
)


@dataclass(frozen=True, slots=True)
class _GovernedZDEXFeeAllocationProfileFieldsV1:
    profile: EconomicProfileSnapshotV1
    policy_registry: EconomicPolicyRegistryV1
    allocation_route: RouteReleaseV1
    buyback_route: RouteReleaseV1
    module_release: LaneModuleReleaseV1
    coordinator_release: LaneCoordinatorReleaseV1
    policy_binding: EconomicPolicyBindingV1


class GovernedZDEXFeeAllocationProfileV1:
    """Verifier-selected SHADOW profile binding for fee-allocation admission."""

    __slots__ = ("_fields",)
    _fields: _GovernedZDEXFeeAllocationProfileFieldsV1

    def __init__(
        self,
        token: object,
        fields: _GovernedZDEXFeeAllocationProfileFieldsV1,
    ) -> None:
        if token is not _GOVERNED_FEE_ALLOCATION_PROFILE_TOKEN:
            raise TypeError("governed ZDEX fee-allocation profile is verifier-constructed")
        object.__setattr__(self, "_fields", fields)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("governed ZDEX fee-allocation profile is immutable")


_GOVERNED_FEE_ALLOCATION_PROFILE_TOKEN = object()


def _registered_route(
    profile: EconomicProfileSnapshotV1,
    command_kind: str,
) -> RouteReleaseV1:
    for route in profile.route_registry.routes:
        if route.command_kind == command_kind:
            return route
    raise ValueError("ZDEX fee-allocation governed route is absent")


def bind_zdex_fee_allocation_shadow_profile_v1(
    *,
    expected_profile_id: str,
    expected_authority_epoch: int,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
) -> GovernedZDEXFeeAllocationProfileV1:
    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("ZDEX fee-allocation profile must be exact typed data")
    if type(policy_registry) is not EconomicPolicyRegistryV1:
        raise TypeError("ZDEX fee-allocation policy registry must be exact typed data")
    if type(expected_profile_id) is not str or expected_profile_id != profile.profile_id:
        raise ValueError("ZDEX fee-allocation expected profile mismatch")
    if (
        type(expected_authority_epoch) is not int
        or expected_authority_epoch != profile.authority_epoch
    ):
        raise ValueError("ZDEX fee-allocation expected authority epoch mismatch")
    if profile.status is not ProfileStatusV1.SHADOW:
        raise ValueError("ZDEX fee-allocation profile must remain SHADOW")
    if profile.policy_registry_root != policy_registry.registry_root:
        raise ValueError("ZDEX fee-allocation policy registry is outside the profile")
    fields = _GovernedZDEXFeeAllocationProfileFieldsV1(
        profile,
        policy_registry,
        _registered_route(profile, PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1),
        _registered_route(profile, PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1),
        profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS),
        profile.lane_coordinator_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS),
        policy_registry.require_binding(
            policy_kind=ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
            command_kind=PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
        ),
    )
    governed = GovernedZDEXFeeAllocationProfileV1(
        _GOVERNED_FEE_ALLOCATION_PROFILE_TOKEN,
        fields,
    )
    _require_release_shapes(governed)
    return governed


def _require_release_shapes(
    governed: GovernedZDEXFeeAllocationProfileV1,
) -> None:
    fields = governed._fields
    allocation = fields.allocation_route
    buyback = fields.buyback_route
    module = fields.module_release
    coordinator = fields.coordinator_release
    if allocation.status is not ReleaseStatusV1.SHADOW or allocation.accepts_new_objects:
        raise ValueError("ZDEX fee-allocation route must remain SHADOW")
    if (
        allocation.command_kind != PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1
        or allocation.ordered_lanes != (LaneIdV1.ZDEX_TOKENOMICS,)
        or allocation.module_release_ids != (module.release_id,)
        or allocation.dependency_roles != (FEE_ALLOCATION_OUTPUT_ROLE_V1,)
        or allocation.port_schema_roots != (zdex_fee_allocation_port_schema_root_v1(),)
    ):
        raise ValueError("ZDEX fee-allocation route shape mismatch")
    if buyback.status is not ReleaseStatusV1.SHADOW or buyback.accepts_new_objects:
        raise ValueError("ZDEX authorized buyback route must remain SHADOW")
    if (
        buyback.command_kind != PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
        or buyback.ordered_lanes
        != (LaneIdV1.SPOT_LIQUIDITY, LaneIdV1.ZDEX_TOKENOMICS)
        or buyback.module_release_ids[1] != module.release_id
        or buyback.dependency_roles
        != (AMM_PURCHASE_OUTPUT_ROLE_V1, ZDEX_BURN_INPUT_ROLE_V1)
        or buyback.port_schema_roots
        != (
            zdex_amm_purchase_port_schema_root_v1(),
            zdex_burn_port_schema_root_v1(),
        )
    ):
        raise ValueError("ZDEX authorized buyback route shape mismatch")
    if (
        module.status is not ReleaseStatusV1.SHADOW
        or module.accepts_new_objects
        or module.lane_id is not LaneIdV1.ZDEX_TOKENOMICS
        or PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1 not in module.command_variants
    ):
        raise ValueError("ZDEX fee-allocation module release shape mismatch")
    if (
        coordinator.status is not ReleaseStatusV1.SHADOW
        or coordinator.accepts_new_objects
        or coordinator.lane_id is not LaneIdV1.ZDEX_TOKENOMICS
    ):
        raise ValueError("ZDEX fee-allocation coordinator release shape mismatch")


def _revalidate_governed_fee_profile(
    governed: GovernedZDEXFeeAllocationProfileV1,
) -> None:
    fields = governed._fields
    replace(fields.profile)
    replace(fields.policy_registry)
    replace(fields.allocation_route)
    replace(fields.buyback_route)
    replace(fields.module_release)
    replace(fields.coordinator_release)
    if (
        fields.profile.policy_registry_root != fields.policy_registry.registry_root
        or _registered_route(fields.profile, PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1)
        != fields.allocation_route
        or _registered_route(fields.profile, PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1)
        != fields.buyback_route
        or fields.profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS)
        != fields.module_release
        or fields.profile.lane_coordinator_registry.release_for(
            LaneIdV1.ZDEX_TOKENOMICS
        )
        != fields.coordinator_release
        or fields.policy_registry.require_binding(
            policy_kind=ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
            command_kind=PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
        )
        != fields.policy_binding
    ):
        raise ValueError("ZDEX fee-allocation governed selection changed")
    _require_release_shapes(governed)


__all__ = [
    "GovernedZDEXFeeAllocationProfileV1",
    "bind_zdex_fee_allocation_shadow_profile_v1",
]
