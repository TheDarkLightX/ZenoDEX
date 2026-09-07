"""Measured route receipt execution between pure preparation and binding.

The isolated factory owns verifier selection. This adapter accepts its exact
route port and preserves core rejection precedence by preparing before
execution. It issues no epoch, commit, settlement, migration or publication
authority.
"""

from __future__ import annotations

from ..core.route_composition_receipt_verification_v1 import (
    RouteCompositionReceiptCandidateV1,
    VerifiedRouteCompositionV1,
    bind_verified_route_composition_receipt_v1,
    prepare_route_composition_receipt_v1,
)
from .isolated_profile_receipt_ports_v1 import IsolatedReceiptPortV1


def verify_route_composition_receipt_v1(
    candidate: RouteCompositionReceiptCandidateV1,
    receipt_verifier: IsolatedReceiptPortV1,
) -> VerifiedRouteCompositionV1:
    """Prepare, execute and bind one route receipt statement."""
    prepared = prepare_route_composition_receipt_v1(candidate)
    if type(receipt_verifier) is not IsolatedReceiptPortV1:
        raise TypeError("route composition verification requires a measured isolated receipt port")
    binding_root = receipt_verifier.verifier_binding_root
    execution = receipt_verifier.verify_prepared_route_receipt_v1(prepared)
    return bind_verified_route_composition_receipt_v1(
        prepared, execution, expected_verifier_binding_root=binding_root
    )


__all__ = [
    "verify_route_composition_receipt_v1",
]
