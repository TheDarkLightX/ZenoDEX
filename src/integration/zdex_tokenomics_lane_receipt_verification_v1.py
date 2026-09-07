"""Reference receipt execution for the ZDEX tokenomics burn and fee lanes.

Core prepares one exact detached subject (final marker fields plus the exact
receipt, image and canonical lane journal bytes) and performs no verifier
call.  This shell executes exactly that subject on the caller-supplied
reference verifier, then mints the existing process-local marker from the
executed snapshot only.

The generic ``ZDEXLaneSuccinctReceiptVerifierV1`` port's return value is
ignored, as the former core path did; the measured Bound verifier enforces its
own exact success contract internally.  The marker remains a shadow/reference
marker with no publication, settlement or production authority.
"""

from __future__ import annotations

from ..core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXLaneSuccinctReceiptVerifierV1,
)
from ..core.zdex_tokenomics_fee_lane_receipt_verification_v1 import (
    GovernedZDEXFeeAllocationProfileV1,
    ZDEXTokenomicsFeeLaneReceiptCandidateV1,
    prepare_zdex_tokenomics_fee_lane_receipt_v1,
)
from ..core.zdex_tokenomics_lane_receipt_common_v1 import (
    PreparedZDEXTokenomicsLaneReceiptV1,
    VerifiedZDEXTokenomicsLaneV1,
    _build_verified_zdex_tokenomics_lane_v1,
    snapshot_prepared_zdex_tokenomics_lane_receipt_v1,
)
from ..core.zdex_tokenomics_lane_receipt_verification_v1 import (
    GovernedZDEXTokenomicsProfileV1,
    ZDEXTokenomicsLaneReceiptCandidateV1,
    prepare_zdex_tokenomics_lane_receipt_v1,
)


def _execute_prepared_zdex_tokenomics_lane_receipt_v1(
    prepared: PreparedZDEXTokenomicsLaneReceiptV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXTokenomicsLaneV1:
    """Execute exactly the prepared receipt, image and journal, then mint.

    A detached core-validated copy is fixed before I/O.  Unsupported record
    types and digest-unbound bytes are refused while making that copy, before
    any call.  Only the executed copy reaches marker minting in this wrapper,
    so callback-side mutation of the caller-held prepared object or candidate
    cannot relabel the returned marker.
    """

    owned = snapshot_prepared_zdex_tokenomics_lane_receipt_v1(prepared)
    receipt_verifier.verify_succinct_receipt(
        owned.receipt_bytes,
        expected_image_id=owned.expected_image_id,
        expected_journal_bytes=owned.expected_journal_bytes,
    )
    return _build_verified_zdex_tokenomics_lane_v1(owned)


def verify_zdex_tokenomics_lane_receipt_v1(
    candidate: ZDEXTokenomicsLaneReceiptCandidateV1,
    governed: GovernedZDEXTokenomicsProfileV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXTokenomicsLaneV1:
    """Reference burn-lane admission through a supplied verifier; output has no authority.

    Core preparation runs every candidate, governed-profile, composition and
    receipt-shape check first, so no previously rejected input reaches the
    verifier.
    """

    prepared = prepare_zdex_tokenomics_lane_receipt_v1(candidate, governed)
    return _execute_prepared_zdex_tokenomics_lane_receipt_v1(prepared, receipt_verifier)


def verify_zdex_tokenomics_fee_lane_receipt_v1(
    candidate: ZDEXTokenomicsFeeLaneReceiptCandidateV1,
    governed: GovernedZDEXFeeAllocationProfileV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXTokenomicsLaneV1:
    """Verify one policy-selected fee leaf and its exact complete-lane receipt."""

    prepared = prepare_zdex_tokenomics_fee_lane_receipt_v1(candidate, governed)
    return _execute_prepared_zdex_tokenomics_lane_receipt_v1(prepared, receipt_verifier)


__all__ = [
    "verify_zdex_tokenomics_fee_lane_receipt_v1",
    "verify_zdex_tokenomics_lane_receipt_v1",
]
