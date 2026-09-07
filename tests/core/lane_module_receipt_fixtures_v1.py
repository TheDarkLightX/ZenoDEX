"""Unit-only compatibility wrappers for lane-module receipt scenarios.

The production four verify_* names live in the integration shell. These
helpers preserve the old test call shape while keeping the core preparation
and binding assertions executable. The fixed binding root and execution token
below are synthetic unit fixtures: they provide no cryptographic,
measured-deployment, publication, or finality evidence.
"""

from __future__ import annotations

from typing import Protocol

from src.core.lane_module_receipt_verification_v1 import (
    _VERIFIED_LANE_MODULE_RECEIPT_EXECUTION_TOKEN_V1,
    AssetTransferLaneModuleReceiptCandidateV1,
    ManagedAssetLifecycleLaneModuleReceiptCandidateV1,
    PerpsMarginLaneModuleReceiptCandidateV1,
    PreparedLaneModuleReceiptV1,
    VerifiedLaneModuleReceiptExecutionV1,
    VerifiedLaneModuleTransitionV1,
    bind_verified_lane_module_receipt_v1,
    prepare_asset_transfer_lane_module_custody_receipt_v1,
    prepare_asset_transfer_lane_module_receipt_v1,
    prepare_managed_asset_lifecycle_lane_module_receipt_v1,
    prepare_perps_margin_lane_module_receipt_v1,
)

_UNIT_SYNTHETIC_VERIFIER_BINDING_ROOT_V1 = "0x" + "f1" * 32


class _ReceiptVerifierV1(Protocol):
    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> object:
        ...


def _execute_and_bind_unit_receipt_v1(
    prepared: PreparedLaneModuleReceiptV1,
    receipt_verifier: _ReceiptVerifierV1,
) -> VerifiedLaneModuleTransitionV1:
    """Run the caller's recorded callback, then issue synthetic unit evidence."""

    # Keep callback exceptions and return values under test control. The
    # callback is the existing scenario double, not a cryptographic verifier.
    receipt_verifier.verify_succinct_receipt(
        prepared.receipt_bytes,
        expected_image_id=prepared.expected_image_id,
        expected_journal_bytes=prepared.expected_journal_bytes,
    )
    execution = VerifiedLaneModuleReceiptExecutionV1(
        _VERIFIED_LANE_MODULE_RECEIPT_EXECUTION_TOKEN_V1,
        prepared,
        _UNIT_SYNTHETIC_VERIFIER_BINDING_ROOT_V1,
    )
    return bind_verified_lane_module_receipt_v1(
        prepared,
        execution,
        expected_verifier_binding_root=_UNIT_SYNTHETIC_VERIFIER_BINDING_ROOT_V1,
    )


def verify_asset_transfer_lane_module_receipt_v1(
    candidate: AssetTransferLaneModuleReceiptCandidateV1,
    receipt_verifier: _ReceiptVerifierV1,
) -> VerifiedLaneModuleTransitionV1:
    """Unit-only compatibility wrapper for the former core API."""

    return _execute_and_bind_unit_receipt_v1(
        prepare_asset_transfer_lane_module_receipt_v1(candidate),
        receipt_verifier,
    )


def verify_asset_transfer_lane_module_custody_receipt_v1(
    candidate: AssetTransferLaneModuleReceiptCandidateV1,
    receipt_verifier: _ReceiptVerifierV1,
) -> VerifiedLaneModuleTransitionV1:
    """Unit-only compatibility wrapper for the former core API."""

    return _execute_and_bind_unit_receipt_v1(
        prepare_asset_transfer_lane_module_custody_receipt_v1(candidate),
        receipt_verifier,
    )


def verify_managed_asset_lifecycle_lane_module_receipt_v1(
    candidate: ManagedAssetLifecycleLaneModuleReceiptCandidateV1,
    receipt_verifier: _ReceiptVerifierV1,
) -> VerifiedLaneModuleTransitionV1:
    """Unit-only compatibility wrapper for the former core API."""

    return _execute_and_bind_unit_receipt_v1(
        prepare_managed_asset_lifecycle_lane_module_receipt_v1(candidate),
        receipt_verifier,
    )


def verify_perps_margin_lane_module_receipt_v1(
    candidate: PerpsMarginLaneModuleReceiptCandidateV1,
    receipt_verifier: _ReceiptVerifierV1,
) -> VerifiedLaneModuleTransitionV1:
    """Unit-only compatibility wrapper for the former core API."""

    return _execute_and_bind_unit_receipt_v1(
        prepare_perps_margin_lane_module_receipt_v1(candidate),
        receipt_verifier,
    )


__all__ = [
    "verify_asset_transfer_lane_module_receipt_v1",
    "verify_asset_transfer_lane_module_custody_receipt_v1",
    "verify_managed_asset_lifecycle_lane_module_receipt_v1",
    "verify_perps_margin_lane_module_receipt_v1",
]
