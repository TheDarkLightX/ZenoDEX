"""Reference receipt execution for one governed ZDEX fee-allocation leaf.

Core prepares one exact detached subject (the marker fields plus the exact
receipt, module image and canonical allocation journal bytes) and performs no
verifier call.  This shell executes exactly that subject on the caller-supplied
reference verifier, then mints the existing process-local marker from the
executed snapshot only.

The generic ``ZDEXLaneSuccinctReceiptVerifierV1`` port's return value is
ignored, as the former core path did; the measured Bound verifier enforces its
own exact success contract internally.  The marker remains a shadow/reference
marker with no publication, settlement or production authority.
"""

from __future__ import annotations

from ..core.zdex_fee_allocation_receipt_verification_v1 import (
    GovernedZDEXFeeAllocationProfileV1,
    PreparedZDEXFeeAllocationReceiptV1,
    VerifiedZDEXFeeAllocationV1,
    ZDEXFeeAllocationReceiptCandidateV1,
    _build_verified_zdex_fee_allocation_v1,
    prepare_zdex_fee_allocation_receipt_v1,
    snapshot_prepared_zdex_fee_allocation_receipt_v1,
)
from ..core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXLaneSuccinctReceiptVerifierV1,
)


def _execute_prepared_zdex_fee_allocation_receipt_v1(
    prepared: PreparedZDEXFeeAllocationReceiptV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXFeeAllocationV1:
    """Execute exactly the prepared receipt, image and journal, then mint.

    A detached core-validated copy is fixed before I/O.  Unsupported record
    types and digest-unbound bytes are refused while making that copy, before
    any call.  Only the executed copy reaches marker minting, so callback-side
    mutation of the caller-held prepared object or candidate cannot relabel
    the returned marker.
    """

    owned = snapshot_prepared_zdex_fee_allocation_receipt_v1(prepared)
    receipt_verifier.verify_succinct_receipt(
        owned.receipt_bytes,
        expected_image_id=owned.expected_image_id,
        expected_journal_bytes=owned.expected_journal_bytes,
    )
    return _build_verified_zdex_fee_allocation_v1(owned)


def verify_zdex_fee_allocation_receipt_v1(
    candidate: ZDEXFeeAllocationReceiptCandidateV1,
    governed: GovernedZDEXFeeAllocationProfileV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXFeeAllocationV1:
    """Reference leaf admission through a supplied verifier; output has no authority.

    Core preparation runs every candidate, governed-profile, binding,
    recomputation and receipt-shape check first, so no previously rejected
    input reaches the verifier.
    """

    prepared = prepare_zdex_fee_allocation_receipt_v1(candidate, governed)
    return _execute_prepared_zdex_fee_allocation_receipt_v1(prepared, receipt_verifier)


__all__ = [
    "verify_zdex_fee_allocation_receipt_v1",
]
