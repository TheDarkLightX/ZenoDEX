"""Unit-only synthetic wrappers for coordinator and route receipt scenarios.

The production three verify_* names live in the integration shell and admit
only measured factory ports. These helpers preserve the old test call shape:
they prepare in the core, run the caller's recorded callback, and then mint
synthetic execution evidence with the core's private tokens before pure
binding. The fixed binding root and tokens are synthetic unit fixtures: they
provide no cryptographic, measured-deployment, publication, or finality
evidence, and this module is never a production adapter.
"""

from __future__ import annotations

from typing import Protocol

from src.core.lane_composition_receipt_verification_v1 import (
    _VERIFIED_LANE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1,
    LaneCompositionReceiptCandidateV1,
    PreparedLaneCompositionReceiptV1,
    VerifiedLaneCompositionReceiptExecutionV1,
    VerifiedLaneCompositionV1,
    bind_verified_lane_composition_receipt_v1,
    prepare_asset_lane_composition_receipt_v1,
    prepare_perps_margin_lane_composition_receipt_v1,
)
from src.core.route_composition_receipt_verification_v1 import (
    _VERIFIED_ROUTE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1,
    PreparedRouteCompositionReceiptV1,
    RouteCompositionReceiptCandidateV1,
    VerifiedRouteCompositionReceiptExecutionV1,
    VerifiedRouteCompositionV1,
    bind_verified_route_composition_receipt_v1,
    prepare_route_composition_receipt_v1,
)

_UNIT_SYNTHETIC_VERIFIER_BINDING_ROOT_V1 = "0x" + "f2" * 32


class _ReceiptVerifierV1(Protocol):
    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> object:
        ...


def _run_unit_callback_v1(
    prepared: PreparedLaneCompositionReceiptV1 | PreparedRouteCompositionReceiptV1,
    receipt_verifier: _ReceiptVerifierV1,
) -> None:
    # Keep callback exceptions and return values under test control. The
    # callback is the existing scenario double, not a cryptographic verifier.
    receipt_verifier.verify_succinct_receipt(
        prepared.receipt_bytes,
        expected_image_id=prepared.expected_image_id,
        expected_journal_bytes=prepared.expected_journal_bytes,
    )


def _execute_and_bind_unit_lane_receipt_v1(
    prepared: PreparedLaneCompositionReceiptV1,
    receipt_verifier: _ReceiptVerifierV1,
) -> VerifiedLaneCompositionV1:
    """Run the caller's recorded callback, then issue synthetic unit evidence."""

    _run_unit_callback_v1(prepared, receipt_verifier)
    execution = VerifiedLaneCompositionReceiptExecutionV1(
        _VERIFIED_LANE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1,
        prepared,
        _UNIT_SYNTHETIC_VERIFIER_BINDING_ROOT_V1,
    )
    return bind_verified_lane_composition_receipt_v1(
        prepared,
        execution,
        expected_verifier_binding_root=_UNIT_SYNTHETIC_VERIFIER_BINDING_ROOT_V1,
    )


def verify_asset_lane_composition_receipt_v1(
    candidate: LaneCompositionReceiptCandidateV1,
    receipt_verifier: _ReceiptVerifierV1,
) -> VerifiedLaneCompositionV1:
    """Unit-only compatibility wrapper for the former core API."""

    return _execute_and_bind_unit_lane_receipt_v1(
        prepare_asset_lane_composition_receipt_v1(candidate),
        receipt_verifier,
    )


def verify_perps_margin_lane_composition_receipt_v1(
    candidate: LaneCompositionReceiptCandidateV1,
    receipt_verifier: _ReceiptVerifierV1,
) -> VerifiedLaneCompositionV1:
    """Unit-only compatibility wrapper for the former core API."""

    return _execute_and_bind_unit_lane_receipt_v1(
        prepare_perps_margin_lane_composition_receipt_v1(candidate),
        receipt_verifier,
    )


def verify_route_composition_receipt_v1(
    candidate: RouteCompositionReceiptCandidateV1,
    receipt_verifier: _ReceiptVerifierV1,
) -> VerifiedRouteCompositionV1:
    """Unit-only compatibility wrapper for the former core API."""

    prepared = prepare_route_composition_receipt_v1(candidate)
    _run_unit_callback_v1(prepared, receipt_verifier)
    execution = VerifiedRouteCompositionReceiptExecutionV1(
        _VERIFIED_ROUTE_COMPOSITION_RECEIPT_EXECUTION_TOKEN_V1,
        prepared,
        _UNIT_SYNTHETIC_VERIFIER_BINDING_ROOT_V1,
    )
    return bind_verified_route_composition_receipt_v1(
        prepared,
        execution,
        expected_verifier_binding_root=_UNIT_SYNTHETIC_VERIFIER_BINDING_ROOT_V1,
    )


__all__ = [
    "verify_asset_lane_composition_receipt_v1",
    "verify_perps_margin_lane_composition_receipt_v1",
    "verify_route_composition_receipt_v1",
]
