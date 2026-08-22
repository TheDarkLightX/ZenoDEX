"""Exact governed eight-decimal amount policy for the M6 profile."""

from __future__ import annotations

from typing import Final

from .global_settlement_types_v1 import (
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    hash_global_v1,
)

M6_ASSET_PRECISION_POLICY_SCHEMA_V1: Final = "zenodex/m6-asset-precision-policy/v1"
M6_ASSET_PRECISION_POLICY_DOMAIN_V1: Final = "m6-asset-precision-policy-v1"
M6_ASSET_PRECISION_POLICY_KIND_V1: Final = "m6_asset_precision_v1"
M6_ASSET_PRECISION_PROFILE_COMMAND_KIND_V1: Final = "global_economic_profile_v1"
M6_ASSET_DECIMAL_PLACES_V1: Final = 8
M6_ATOMS_PER_DISPLAY_UNIT_V1: Final = 100_000_000


def m6_asset_precision_policy_canonical_v1() -> dict[str, object]:
    return {
        "schema": M6_ASSET_PRECISION_POLICY_SCHEMA_V1,
        "decimal_places": M6_ASSET_DECIMAL_PLACES_V1,
        "atoms_per_display_unit": M6_ATOMS_PER_DISPLAY_UNIT_V1,
        "amount_representation": "unsigned_integer_atoms",
        "conversion_rule": "exact_integer_atoms_only",
        "rounding_rule": "command_specific_explicit_integer_rounding",
        "rescale_rule": "global_settlement_abi_v2_migration_only",
        "floating_point_allowed": False,
    }


M6_ASSET_PRECISION_POLICY_ROOT_V1: Final = hash_global_v1(
    M6_ASSET_PRECISION_POLICY_DOMAIN_V1,
    m6_asset_precision_policy_canonical_v1(),
)


def m6_asset_precision_policy_binding_v1() -> EconomicPolicyBindingV1:
    return EconomicPolicyBindingV1(
        policy_kind=M6_ASSET_PRECISION_POLICY_KIND_V1,
        command_kind=M6_ASSET_PRECISION_PROFILE_COMMAND_KIND_V1,
        policy_root=M6_ASSET_PRECISION_POLICY_ROOT_V1,
    )


def validate_m6_asset_precision_profile_binding_v1(
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
) -> None:
    """Require exact eight-decimal atom semantics in the governed profile."""

    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("M6 asset precision profile type is not closed")
    if type(policy_registry) is not EconomicPolicyRegistryV1:
        raise TypeError("M6 asset precision policy registry type is not closed")
    if policy_registry.registry_root != profile.policy_registry_root:
        raise ValueError("M6 asset precision policy registry root mismatch")
    binding = policy_registry.require_binding(
        policy_kind=M6_ASSET_PRECISION_POLICY_KIND_V1,
        command_kind=M6_ASSET_PRECISION_PROFILE_COMMAND_KIND_V1,
    )
    if binding.policy_root != M6_ASSET_PRECISION_POLICY_ROOT_V1:
        raise ValueError("M6 asset precision policy root mismatch")


__all__ = [
    "M6_ASSET_DECIMAL_PLACES_V1",
    "M6_ASSET_PRECISION_POLICY_DOMAIN_V1",
    "M6_ASSET_PRECISION_POLICY_KIND_V1",
    "M6_ASSET_PRECISION_POLICY_ROOT_V1",
    "M6_ASSET_PRECISION_POLICY_SCHEMA_V1",
    "M6_ASSET_PRECISION_PROFILE_COMMAND_KIND_V1",
    "M6_ATOMS_PER_DISPLAY_UNIT_V1",
    "m6_asset_precision_policy_binding_v1",
    "m6_asset_precision_policy_canonical_v1",
    "validate_m6_asset_precision_profile_binding_v1",
]
