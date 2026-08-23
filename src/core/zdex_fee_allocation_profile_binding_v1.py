"""Profile-selected SHADOW releases for ZDEX fee-allocation admission."""

from __future__ import annotations

from dataclasses import dataclass, replace

from .global_economic_profile_snapshot_v1 import (
    _snapshot_coordinator_release_v1,
    _snapshot_lane_release_v1,
    _snapshot_route_release_v1,
    snapshot_economic_profile_v1,
)
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
)
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

    __slots__ = ("_fields", "_trusted_profile_id", "_trusted_authority_epoch")
    _fields: _GovernedZDEXFeeAllocationProfileFieldsV1
    _trusted_profile_id: str
    _trusted_authority_epoch: int

    def __init__(
        self,
        token: object,
        fields: _GovernedZDEXFeeAllocationProfileFieldsV1,
        trusted_profile_id: str,
        trusted_authority_epoch: int,
    ) -> None:
        if token is not _GOVERNED_FEE_ALLOCATION_PROFILE_TOKEN:
            raise TypeError("governed ZDEX fee-allocation profile is verifier-constructed")
        if type(trusted_profile_id) is not str or type(trusted_authority_epoch) is not int:
            raise TypeError(
                "governed ZDEX fee-allocation trusted profile anchor "
                "must be exact typed data"
            )
        object.__setattr__(self, "_fields", fields)
        object.__setattr__(self, "_trusted_profile_id", trusted_profile_id)
        object.__setattr__(self, "_trusted_authority_epoch", trusted_authority_epoch)

    def __setattr__(self, name: str, value: object) -> None:
        raise AttributeError("governed ZDEX fee-allocation profile is immutable")


_GOVERNED_FEE_ALLOCATION_PROFILE_TOKEN = object()


def _trusted_fee_profile_anchor_v1(
    governed: GovernedZDEXFeeAllocationProfileV1,
) -> tuple[str, int]:
    if type(governed) is not GovernedZDEXFeeAllocationProfileV1:
        raise TypeError("ZDEX fee-allocation governed profile must be verifier-constructed")
    profile_id = governed._trusted_profile_id
    authority_epoch = governed._trusted_authority_epoch
    if type(profile_id) is not str or type(authority_epoch) is not int:
        raise TypeError(
            "ZDEX fee-allocation trusted profile anchor must be exact typed data"
        )
    return profile_id, authority_epoch


def _registered_route(
    profile: EconomicProfileSnapshotV1,
    command_kind: str,
) -> RouteReleaseV1:
    for route in profile.route_registry.routes:
        if route.command_kind == command_kind:
            return route
    raise ValueError("ZDEX fee-allocation governed route is absent")


def _snapshot_policy_registry_v1(
    registry: EconomicPolicyRegistryV1,
) -> EconomicPolicyRegistryV1:
    if type(registry) is not EconomicPolicyRegistryV1:
        raise TypeError("ZDEX fee-allocation policy registry must be exact typed data")
    _require_exact_dataclass_scalars_v1(
        registry,
        name="ZDEX fee-allocation policy registry",
        tuple_fields=frozenset({"bindings"}),
    )
    if type(registry.bindings) is not tuple or any(
        type(binding) is not EconomicPolicyBindingV1 for binding in registry.bindings
    ):
        raise TypeError("ZDEX fee-allocation policy bindings must be exact typed data")
    bindings = []
    for binding in registry.bindings:
        _require_exact_dataclass_scalars_v1(
            binding,
            name="ZDEX fee-allocation policy binding",
        )
        bindings.append(replace(binding))
    return EconomicPolicyRegistryV1(tuple(bindings))


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
    if type(expected_profile_id) is not str:
        raise ValueError("ZDEX fee-allocation expected profile mismatch")
    if type(expected_authority_epoch) is not int:
        raise ValueError("ZDEX fee-allocation expected authority epoch mismatch")
    owned_profile = snapshot_economic_profile_v1(profile)
    owned_policy_registry = _snapshot_policy_registry_v1(policy_registry)
    if expected_profile_id != owned_profile.profile_id:
        raise ValueError("ZDEX fee-allocation expected profile mismatch")
    if expected_authority_epoch != owned_profile.authority_epoch:
        raise ValueError("ZDEX fee-allocation expected authority epoch mismatch")
    if owned_profile.status is not ProfileStatusV1.SHADOW:
        raise ValueError("ZDEX fee-allocation profile must remain SHADOW")
    if owned_profile.policy_registry_root != owned_policy_registry.registry_root:
        raise ValueError("ZDEX fee-allocation policy registry is outside the profile")
    fields = _GovernedZDEXFeeAllocationProfileFieldsV1(
        owned_profile,
        owned_policy_registry,
        _registered_route(owned_profile, PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1),
        _registered_route(owned_profile, PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1),
        owned_profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS),
        owned_profile.lane_coordinator_registry.release_for(
            LaneIdV1.ZDEX_TOKENOMICS
        ),
        owned_policy_registry.require_binding(
            policy_kind=ZDEX_FEE_ALLOCATION_POLICY_KIND_V1,
            command_kind=PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
        ),
    )
    governed = GovernedZDEXFeeAllocationProfileV1(
        _GOVERNED_FEE_ALLOCATION_PROFILE_TOKEN,
        fields,
        expected_profile_id,
        expected_authority_epoch,
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
) -> GovernedZDEXFeeAllocationProfileV1:
    trusted_profile_id, trusted_authority_epoch = _trusted_fee_profile_anchor_v1(
        governed
    )
    fields = governed._fields
    if type(fields) is not _GovernedZDEXFeeAllocationProfileFieldsV1:
        raise TypeError("ZDEX fee-allocation governed fields must be exact typed data")
    if type(fields.profile) is not EconomicProfileSnapshotV1:
        raise TypeError("ZDEX fee-allocation governed profile must be exact typed data")
    if type(fields.policy_binding) is not EconomicPolicyBindingV1:
        raise TypeError(
            "ZDEX fee-allocation governed policy binding must be exact typed data"
        )
    _require_exact_dataclass_scalars_v1(
        fields.policy_binding,
        name="ZDEX fee-allocation governed policy binding",
    )
    owned_profile = snapshot_economic_profile_v1(fields.profile)
    owned_policy_registry = _snapshot_policy_registry_v1(fields.policy_registry)
    if (
        owned_profile.profile_id != trusted_profile_id
        or owned_profile.authority_epoch != trusted_authority_epoch
    ):
        raise ValueError("ZDEX fee-allocation trusted profile anchor changed")
    owned = bind_zdex_fee_allocation_shadow_profile_v1(
        expected_profile_id=trusted_profile_id,
        expected_authority_epoch=trusted_authority_epoch,
        profile=owned_profile,
        policy_registry=owned_policy_registry,
    )
    owned_fields = owned._fields
    if (
        _snapshot_route_release_v1(fields.allocation_route)
        != owned_fields.allocation_route
        or _snapshot_route_release_v1(fields.buyback_route)
        != owned_fields.buyback_route
        or _snapshot_lane_release_v1(fields.module_release)
        != owned_fields.module_release
        or _snapshot_coordinator_release_v1(fields.coordinator_release)
        != owned_fields.coordinator_release
        or replace(fields.policy_binding) != owned_fields.policy_binding
    ):
        raise ValueError(
            "ZDEX fee-allocation trusted profile anchor or selection changed"
        )
    return owned


__all__ = [
    "GovernedZDEXFeeAllocationProfileV1",
    "bind_zdex_fee_allocation_shadow_profile_v1",
]
