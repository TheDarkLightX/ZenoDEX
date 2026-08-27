"""Governed typed policy-registry membership for asset transfer.

The transfer lane module carries opaque ``asset_policy_registry_root`` and
``fee_policy_registry_root`` values plus one state policy row per asset. Those
rows economically control enablement, the fee owner, and the flat fee, so an
ungoverned row can redirect or reprice the fee while both opaque roots stay
unchanged. This core binds both roots to one exact typed registry that derives
two domain-separated roots from the same owned rows: the asset policy root
commits the ``ASSET_TRANSFER`` module release plus ordered ``(asset, enabled)``
rows, and the fee policy root commits the same release plus ordered
``(asset, fee_owner, transfer_fee_atoms)`` rows. The active profile's economic
policy registry governs both roots for the transfer command kind. Membership
then requires the module's release, the command asset, and every carried state
policy to match the registry exactly. Direct transfer transitions never
consult the registry; it grants no proof, settlement, or publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .asset_transfer_lane_module_v1 import (
    AssetTransferLaneModuleInputV1,
    _snapshot_asset_transfer_lane_module_input_v1,
)
from .asset_transfer_types_v1 import (
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferPolicyV1,
)
from .global_economic_proof_v1 import EconomicCommandOccurrenceV1
from .global_economic_refinement_snapshot_v1 import _snapshot_dataclass_tuple_v1
from .global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    LaneIdV1,
    _require_ordered_objects,
    _require_root,
    _require_token,
    hash_global_v1,
)
from .managed_asset_policy_registry_v1 import snapshot_exact_economic_policy_registry_v1

ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1: Final = (
    "zenodex/asset-transfer-policy-registry/v1"
)
ASSET_TRANSFER_ASSET_POLICY_ROOT_SCHEMA_V1: Final = (
    "zenodex/asset-transfer-asset-policy-root/v1"
)
ASSET_TRANSFER_FEE_POLICY_ROOT_SCHEMA_V1: Final = (
    "zenodex/asset-transfer-fee-policy-root/v1"
)
ASSET_TRANSFER_ASSET_POLICY_KIND_V1: Final = "asset_transfer_asset_policy_v1"
ASSET_TRANSFER_FEE_POLICY_KIND_V1: Final = "asset_transfer_fee_policy_v1"
MAX_ASSET_TRANSFER_POLICIES_V1: Final = 256
_ASSET_POLICY_ROOT_DOMAIN_V1: Final = "asset-transfer-asset-policy-root-v1"
_FEE_POLICY_ROOT_DOMAIN_V1: Final = "asset-transfer-fee-policy-root-v1"


@dataclass(frozen=True, slots=True)
class AssetTransferPolicyRegistryV1:
    """Exact governed transfer policy rows bound to one ``ASSET_TRANSFER`` release."""

    module_release_id: str
    policies: tuple[AssetTransferPolicyV1, ...]

    def __post_init__(self) -> None:
        _require_root(
            self.module_release_id,
            name="asset transfer policy registry module release",
        )
        if type(self.policies) is not tuple:
            raise TypeError("asset transfer policy registry policies must be a tuple")
        if len(self.policies) > MAX_ASSET_TRANSFER_POLICIES_V1:
            raise ValueError("asset transfer policy registry exceeds the ABI V1 bound")
        _require_ordered_objects(
            self.policies,
            name="asset transfer policy registry policies",
            expected_type=AssetTransferPolicyV1,
            key="asset",
        )

    @property
    def asset_policy_root(self) -> str:
        """Commit the release plus ordered ``(asset, enabled)`` rows."""

        return hash_global_v1(
            _ASSET_POLICY_ROOT_DOMAIN_V1,
            {
                "schema": ASSET_TRANSFER_ASSET_POLICY_ROOT_SCHEMA_V1,
                "module_release_id": self.module_release_id,
                "policies": tuple(
                    {"asset": policy.asset, "enabled": policy.enabled}
                    for policy in self.policies
                ),
            },
        )

    @property
    def fee_policy_root(self) -> str:
        """Commit the release plus ordered ``(asset, fee_owner, transfer_fee_atoms)`` rows."""

        return hash_global_v1(
            _FEE_POLICY_ROOT_DOMAIN_V1,
            {
                "schema": ASSET_TRANSFER_FEE_POLICY_ROOT_SCHEMA_V1,
                "module_release_id": self.module_release_id,
                "policies": tuple(
                    {
                        "asset": policy.asset,
                        "fee_owner": policy.fee_owner,
                        "transfer_fee_atoms": policy.transfer_fee_atoms,
                    }
                    for policy in self.policies
                ),
            },
        )

    def policy_for(self, asset: str) -> AssetTransferPolicyV1 | None:
        _require_token(asset, name="asset transfer policy registry asset")
        return next((policy for policy in self.policies if policy.asset == asset), None)

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1,
            "module_release_id": self.module_release_id,
            "policies": self.policies,
        }


def snapshot_asset_transfer_policy_registry_v1(
    registry: AssetTransferPolicyRegistryV1,
) -> AssetTransferPolicyRegistryV1:
    """Own one exact, revalidated registry before any root or membership use."""

    if type(registry) is not AssetTransferPolicyRegistryV1:
        raise TypeError("asset transfer policy registry type is not closed")
    if type(registry.module_release_id) is not str:
        raise TypeError("asset transfer policy registry module release must be exact text")
    return AssetTransferPolicyRegistryV1(
        registry.module_release_id,
        _snapshot_dataclass_tuple_v1(
            registry.policies,
            AssetTransferPolicyV1,
            "asset transfer policies",
        ),
    )


def require_governed_asset_transfer_policy_registry_v1(
    *,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    occurrence: EconomicCommandOccurrenceV1,
    asset_policy_registry: AssetTransferPolicyRegistryV1,
) -> AssetTransferPolicyRegistryV1:
    """Return an owned typed registry after exact profile and command binding.

    The outer policy registry root must be the profile's committed root, the
    asset-policy and fee-policy bindings for ``asset_transfer`` must both carry
    the exact domain-separated roots of this registry (so swapped roots reject),
    and the registry's module release must be the profile-selected
    ``ASSET_TRANSFER`` release.
    """

    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("asset transfer policy profile type is not closed")
    if type(occurrence) is not EconomicCommandOccurrenceV1:
        raise TypeError("asset transfer policy occurrence type is not closed")
    owned_registry = snapshot_exact_economic_policy_registry_v1(policy_registry)
    owned_policies = snapshot_asset_transfer_policy_registry_v1(asset_policy_registry)
    if occurrence.command_kind != ASSET_TRANSFER_COMMAND_KIND_V1:
        raise ValueError("asset transfer policy binding requires an asset transfer command")
    if owned_registry.registry_root != profile.policy_registry_root:
        raise ValueError("asset transfer policy registry is outside the profile")
    asset_binding = owned_registry.require_binding(
        policy_kind=ASSET_TRANSFER_ASSET_POLICY_KIND_V1,
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V1,
    )
    if asset_binding.policy_root != owned_policies.asset_policy_root:
        raise ValueError("asset transfer asset policy root mismatch")
    fee_binding = owned_registry.require_binding(
        policy_kind=ASSET_TRANSFER_FEE_POLICY_KIND_V1,
        command_kind=ASSET_TRANSFER_COMMAND_KIND_V1,
    )
    if fee_binding.policy_root != owned_policies.fee_policy_root:
        raise ValueError("asset transfer fee policy root mismatch")
    selected = profile.lane_registry.release_for(LaneIdV1.ASSET_TRANSFER)
    if selected.release_id != owned_policies.module_release_id:
        raise ValueError(
            "asset transfer policy registry module release is not the profile-selected release"
        )
    return owned_policies


def require_asset_transfer_policy_membership_v1(
    *,
    asset_policy_registry: AssetTransferPolicyRegistryV1,
    module_input: AssetTransferLaneModuleInputV1,
) -> AssetTransferPolicyV1:
    """Return the governed member policy the lane module input executes under.

    Both opaque input roots must be the typed registry roots, the registry's
    module release must be the release the context and pre-state execute
    under, the command asset must be a member carried by the pre-state, and
    every carried state policy must equal its member exactly. Comparison uses
    owned exact snapshots on both sides.
    """

    owned_policies = snapshot_asset_transfer_policy_registry_v1(asset_policy_registry)
    owned_input = _snapshot_asset_transfer_lane_module_input_v1(module_input)
    if owned_input.asset_policy_registry_root != owned_policies.asset_policy_root:
        raise ValueError("asset transfer lane module asset policy root mismatch")
    if owned_input.fee_policy_registry_root != owned_policies.fee_policy_root:
        raise ValueError("asset transfer lane module fee policy root mismatch")
    if (
        owned_input.context.module_release_id != owned_policies.module_release_id
        or owned_input.pre_state.module_release_id != owned_policies.module_release_id
    ):
        raise ValueError("asset transfer policy registry module release mismatch")
    member = owned_policies.policy_for(owned_input.command.asset)
    if member is None:
        raise ValueError(
            "asset transfer command asset is absent from the governed policy registry"
        )
    if all(policy.asset != member.asset for policy in owned_input.pre_state.policies):
        raise ValueError("asset transfer state omits the governed command policy")
    for state_policy in owned_input.pre_state.policies:
        if owned_policies.policy_for(state_policy.asset) != state_policy:
            raise ValueError("asset transfer state policy is not a governed registry member")
    return member


__all__ = [
    "ASSET_TRANSFER_ASSET_POLICY_KIND_V1",
    "ASSET_TRANSFER_ASSET_POLICY_ROOT_SCHEMA_V1",
    "ASSET_TRANSFER_FEE_POLICY_KIND_V1",
    "ASSET_TRANSFER_FEE_POLICY_ROOT_SCHEMA_V1",
    "ASSET_TRANSFER_POLICY_REGISTRY_SCHEMA_V1",
    "MAX_ASSET_TRANSFER_POLICIES_V1",
    "AssetTransferPolicyRegistryV1",
    "require_asset_transfer_policy_membership_v1",
    "require_governed_asset_transfer_policy_registry_v1",
    "snapshot_asset_transfer_policy_registry_v1",
]
