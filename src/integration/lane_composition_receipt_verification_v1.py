"""Measured coordinator receipt execution between pure preparation and binding.

The isolated factory owns verifier selection. These adapters accept its exact
role ports and preserve core rejection precedence by preparing before execution.
They issue no writer, finality, release-activation or external-effect authority.
"""

from __future__ import annotations

from ..core.lane_composition_receipt_verification_v1 import (
    LaneCompositionReceiptCandidateV1,
    PreparedLaneCompositionReceiptV1,
    VerifiedLaneCompositionV1,
    bind_verified_lane_composition_receipt_v1,
    prepare_asset_lane_composition_receipt_v1,
    prepare_perps_margin_lane_composition_receipt_v1,
)
from .isolated_profile_receipt_ports_v1 import IsolatedReceiptPortV1


def _execute_and_bind_lane_composition_receipt_v1(
    prepared: PreparedLaneCompositionReceiptV1, receipt_verifier: IsolatedReceiptPortV1
) -> VerifiedLaneCompositionV1:
    if type(receipt_verifier) is not IsolatedReceiptPortV1:
        raise TypeError("lane composition verification requires a measured isolated receipt port")
    binding_root = receipt_verifier.verifier_binding_root
    execution = receipt_verifier.verify_prepared_coordinator_receipt_v1(prepared)
    return bind_verified_lane_composition_receipt_v1(
        prepared, execution, expected_verifier_binding_root=binding_root
    )


def verify_asset_lane_composition_receipt_v1(
    candidate: LaneCompositionReceiptCandidateV1,
    receipt_verifier: IsolatedReceiptPortV1,
) -> VerifiedLaneCompositionV1:
    """Prepare, execute and bind the asset-lane coordinator receipt statement."""
    return _execute_and_bind_lane_composition_receipt_v1(
        prepare_asset_lane_composition_receipt_v1(candidate), receipt_verifier
    )


def verify_perps_margin_lane_composition_receipt_v1(
    candidate: LaneCompositionReceiptCandidateV1,
    receipt_verifier: IsolatedReceiptPortV1,
) -> VerifiedLaneCompositionV1:
    """Prepare, execute and bind the perps-margin coordinator receipt statement."""
    return _execute_and_bind_lane_composition_receipt_v1(
        prepare_perps_margin_lane_composition_receipt_v1(candidate), receipt_verifier
    )


__all__ = [
    "verify_asset_lane_composition_receipt_v1",
    "verify_perps_margin_lane_composition_receipt_v1",
]
