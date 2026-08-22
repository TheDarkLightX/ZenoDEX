"""Governed profile binding for the closed M6 capability requirements."""

from __future__ import annotations

from dataclasses import replace
from typing import Final

from .global_settlement_types_v1 import (
    EconomicPolicyBindingV1,
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
)

M6_CAPABILITY_POLICY_KIND_V1: Final = "m6_capability_manifest_v1"
M6_CAPABILITY_PROFILE_COMMAND_KIND_V1: Final = "global_economic_profile_v1"
M6_CAPABILITY_MANIFEST_ROOT_V1: Final = (
    "0x21efc162df198e40a0aa942fcb69b7a5f5cc0f93907b11a3c6b25359e4a464bb"
)


def m6_capability_policy_binding_v1() -> EconomicPolicyBindingV1:
    return EconomicPolicyBindingV1(
        policy_kind=M6_CAPABILITY_POLICY_KIND_V1,
        command_kind=M6_CAPABILITY_PROFILE_COMMAND_KIND_V1,
        policy_root=M6_CAPABILITY_MANIFEST_ROOT_V1,
    )


def snapshot_economic_policy_registry_v1(
    registry: EconomicPolicyRegistryV1,
) -> EconomicPolicyRegistryV1:
    if type(registry) is not EconomicPolicyRegistryV1:
        raise TypeError("M6 capability policy registry type is not closed")
    if type(registry.bindings) is not tuple or any(
        type(binding) is not EconomicPolicyBindingV1 for binding in registry.bindings
    ):
        raise TypeError("M6 capability policy bindings are not exact typed values")
    return EconomicPolicyRegistryV1(tuple(replace(binding) for binding in registry.bindings))


def validate_m6_capability_profile_binding_v1(
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
) -> None:
    """Require the exact compiled capability manifest in the governed registry."""

    if type(profile) is not EconomicProfileSnapshotV1:
        raise TypeError("M6 capability profile type is not closed")
    owned_registry = snapshot_economic_policy_registry_v1(policy_registry)
    if owned_registry.registry_root != profile.policy_registry_root:
        raise ValueError("M6 capability policy registry root mismatch")
    binding = owned_registry.require_binding(
        policy_kind=M6_CAPABILITY_POLICY_KIND_V1,
        command_kind=M6_CAPABILITY_PROFILE_COMMAND_KIND_V1,
    )
    if binding.policy_root != M6_CAPABILITY_MANIFEST_ROOT_V1:
        raise ValueError("M6 capability manifest root mismatch")


__all__ = [
    "M6_CAPABILITY_POLICY_KIND_V1",
    "M6_CAPABILITY_PROFILE_COMMAND_KIND_V1",
    "M6_CAPABILITY_MANIFEST_ROOT_V1",
    "m6_capability_policy_binding_v1",
    "snapshot_economic_policy_registry_v1",
    "validate_m6_capability_profile_binding_v1",
]
