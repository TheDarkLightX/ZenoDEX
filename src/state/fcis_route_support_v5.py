"""Compatibility projection of exact route-pool support for FCIS v5.

The legacy v4 support-root module reuses this leaf for differential evidence.
All route cross-field semantics are delegated to the controlled exact binding
derivation.  This module performs no parallel structural validation.
"""

from __future__ import annotations

from ..core.fcis_route_binding import derive_exact_route_binding_v1
from ..core.fcis_route_binding_values import RouteBindingRejectV1
from .intent_snapshots import OwnedIntentV1


def route_support_pool_ids_owned_v5(intent: OwnedIntentV1) -> tuple[str, ...]:
    """Return canonical pool support from the exact derived route binding."""

    if type(intent) is not OwnedIntentV1:
        raise TypeError("route support intent must be an exact OwnedIntentV1")
    binding_result = derive_exact_route_binding_v1(intent)
    if type(binding_result) is RouteBindingRejectV1:
        raise ValueError(
            "exact route support rejects the route binding: "
            f"{binding_result.code.value} at {binding_result.path!r}"
        )
    return tuple(key for key, _value in binding_result.binding.pool_fingerprints.entries)


__all__ = ("route_support_pool_ids_owned_v5",)
