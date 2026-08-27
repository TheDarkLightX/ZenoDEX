"""Governed typed policy-registry membership for managed-asset issue and burn.

The lifecycle lane module carries an opaque ``asset_policy_registry_root`` and
one state policy per asset. This core binds that root to one exact typed
registry whose root commits to the exact ``ASSET_TRANSFER`` module release and
the sorted policy rows, and whose root the active profile's economic policy
registry governs for the command kind. Membership then requires the module's
release, the command asset, and every carried state policy to match the
registry exactly. Direct lifecycle transitions never consult the registry; it
grants no proof, settlement, or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .global_economic_capability_profile_binding_v1 import (
    snapshot_economic_policy_registry_v1,
)
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_economic_refinement_snapshot_v1 import _require_exact_dataclass_scalars_v1
from .global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    RouteReleaseV1,
    _require_ordered_objects,
    _require_root,
    _require_token,
    hash_global_v1,
)
from .managed_asset_lifecycle_lane_module_v1 import (
    ManagedAssetLifecycleLaneModuleInputV1,
    _snapshot_managed_asset_lifecycle_lane_module_input_v1,
    _snapshot_managed_policies_v1,
)
from .managed_asset_lifecycle_types_v1 import (
    MANAGED_ASSET_BURN_COMMAND_KIND_V1,
    MANAGED_ASSET_ISSUE_COMMAND_KIND_V1,
    ManagedAssetLifecyclePolicyV1,
)

MANAGED_ASSET_POLICY_REGISTRY_SCHEMA_V1: Final = (
    "zenodex/managed-asset-policy-registry/v1"
)
MANAGED_ASSET_POLICY_KIND_V1: Final = "managed_asset_policy_v1"
MAX_MANAGED_ASSET_POLICIES_V1: Final = 256
_MANAGED_ASSET_ROUTE_COMMAND_KINDS_V1: Final = frozenset(
    {MANAGED_ASSET_ISSUE_COMMAND_KIND_V1, MANAGED_ASSET_BURN_COMMAND_KIND_V1}
)


@dataclass(frozen=True, slots=True)
class ManagedAssetPolicyRegistryV1:
    """Exact governed policy rows bound to one ``ASSET_TRANSFER`` module release."""

    module_release_id: str
    policies: tuple[ManagedAssetLifecyclePolicyV1, ...]

    def __post_init__(self) -> None:
        _require_root(
            self.module_release_id,
            name="managed asset policy registry module release",
        )
        _require_ordered_objects(
            self.policies,
            name="managed asset policy registry policies",
            expected_type=ManagedAssetLifecyclePolicyV1,
            key="asset",
        )
        if len(self.policies) > MAX_MANAGED_ASSET_POLICIES_V1:
            raise ValueError("managed asset policy registry exceeds the ABI V1 bound")

    @property
    def registry_root(self) -> str:
        return hash_global_v1("managed-asset-policy-registry-v1", self.to_canonical())

    def policy_for(self, asset: str) -> ManagedAssetLifecyclePolicyV1 | None:
        _require_token(asset, name="managed asset policy registry asset")
        return next((policy for policy in self.policies if policy.asset == asset), None)

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": MANAGED_ASSET_POLICY_REGISTRY_SCHEMA_V1,
            "module_release_id": self.module_release_id,
            "policies": self.policies,
        }


def snapshot_managed_asset_policy_registry_v1(
    registry: ManagedAssetPolicyRegistryV1,
) -> ManagedAssetPolicyRegistryV1:
    """Own one exact, revalidated registry before any root or membership use."""

    if type(registry) is not ManagedAssetPolicyRegistryV1:
        raise TypeError("managed asset policy registry type is not closed")
    if type(registry.module_release_id) is not str:
        raise TypeError("managed asset policy registry module release must be exact text")
    return ManagedAssetPolicyRegistryV1(
        registry.module_release_id,
        _snapshot_managed_policies_v1(registry.policies),
    )


def snapshot_exact_economic_policy_registry_v1(
    registry: EconomicPolicyRegistryV1,
) -> EconomicPolicyRegistryV1:
    """Own the profile's economic policy registry with exact primitive bindings.

    Binding roots are compared against typed registry roots, so a text subclass
    carrying a hostile equality cannot stand in for an exact policy root.
    """

    owned = snapshot_economic_policy_registry_v1(registry)
    for binding in owned.bindings:
        _require_exact_dataclass_scalars_v1(binding, name="economic policy binding")
    return owned


def require_governed_managed_asset_policy_registry_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    occurrence: EconomicCommandOccurrenceV1,
    asset_policy_registry: ManagedAssetPolicyRegistryV1,
) -> ManagedAssetPolicyRegistryV1:
    """Return an owned typed registry after exact profile and command binding."""

    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("managed asset policy profile type is not closed")
    if type(occurrence) is not EconomicCommandOccurrenceV1:
        raise TypeError("managed asset policy occurrence type is not closed")
    owned_registry = snapshot_exact_economic_policy_registry_v1(policy_registry)
    owned_policies = snapshot_managed_asset_policy_registry_v1(asset_policy_registry)
    if owned_registry.registry_root != profile.policy_registry_root:
        raise ValueError("managed asset policy registry is outside the profile")
    binding = owned_registry.require_binding(
        policy_kind=MANAGED_ASSET_POLICY_KIND_V1,
        command_kind=occurrence.command_kind,
    )
    if binding.policy_root != owned_policies.registry_root:
        raise ValueError("managed asset policy registry root mismatch")
    return owned_policies


def require_managed_asset_policy_membership_v1(
    *,
    asset_policy_registry: ManagedAssetPolicyRegistryV1,
    module_input: ManagedAssetLifecycleLaneModuleInputV1,
) -> ManagedAssetLifecyclePolicyV1:
    """Return the governed member policy the lane module input executes under.

    The input's opaque registry root must be the typed registry root, the
    registry's module release must be the release the context and pre-state
    execute under, the command asset must be a member, and every carried state
    policy must equal its member exactly. Comparison uses owned exact
    snapshots on both sides.
    """

    owned_policies = snapshot_managed_asset_policy_registry_v1(asset_policy_registry)
    owned_input = _snapshot_managed_asset_lifecycle_lane_module_input_v1(module_input)
    if owned_input.asset_policy_registry_root != owned_policies.registry_root:
        raise ValueError("managed asset lane module policy registry root mismatch")
    if (
        owned_input.context.module_release_id != owned_policies.module_release_id
        or owned_input.pre_state.module_release_id != owned_policies.module_release_id
    ):
        raise ValueError("managed asset policy registry module release mismatch")
    member = owned_policies.policy_for(owned_input.command.asset)
    if member is None:
        raise ValueError(
            "managed asset command asset is absent from the governed policy registry"
        )
    for state_policy in owned_input.pre_state.policies:
        if owned_policies.policy_for(state_policy.asset) != state_policy:
            raise ValueError("managed asset state policy is not a governed registry member")
    return member


def require_managed_asset_route_policy_root_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    occurrence: EconomicCommandOccurrenceV1,
    asset_policy_registry: ManagedAssetPolicyRegistryV1,
) -> RouteReleaseV1:
    """Return the governed issue or burn route whose policy root is the registry root.

    ``RouteReleaseV1.issue_burn_policy_root`` is the route-owned issue/burn
    policy commitment; for managed issue and burn it must equal the exact typed
    registry root before any route witness or receipt verification.
    """

    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("managed asset route policy profile type is not closed")
    if type(occurrence) is not EconomicCommandOccurrenceV1:
        raise TypeError("managed asset route policy occurrence type is not closed")
    owned_policies = snapshot_managed_asset_policy_registry_v1(asset_policy_registry)
    if occurrence.command_kind not in _MANAGED_ASSET_ROUTE_COMMAND_KINDS_V1:
        raise ValueError("managed asset route policy binding requires an issue or burn command")
    route = profile.route_registry.route_for_command(
        occurrence.command_kind,
        claimed_route_release_id=occurrence.route_release_id,
    )
    if route.issue_burn_policy_root != owned_policies.registry_root:
        raise ValueError("managed asset route issue/burn policy root mismatch")
    return route


__all__ = [
    "MANAGED_ASSET_POLICY_KIND_V1",
    "MANAGED_ASSET_POLICY_REGISTRY_SCHEMA_V1",
    "MAX_MANAGED_ASSET_POLICIES_V1",
    "ManagedAssetPolicyRegistryV1",
    "require_governed_managed_asset_policy_registry_v1",
    "require_managed_asset_policy_membership_v1",
    "require_managed_asset_route_policy_root_v1",
    "snapshot_exact_economic_policy_registry_v1",
    "snapshot_managed_asset_policy_registry_v1",
]
