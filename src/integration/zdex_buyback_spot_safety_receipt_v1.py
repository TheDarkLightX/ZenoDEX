"""Shadow receipt execution for the governed ZDEX buyback Spot safety leaf.

Core prepares the shadow Spot receipt in two pure phases and performs no
verifier call.  This shell owns the effectful steps between and after them:
the exact head and Bound type gates in the former order, ownership of the
complete authority head, the two Bound identity reads, the Bound deployment
binding, the single ``verify_profile_lane_receipt`` call on a subject detached
immediately before I/O, and minting from that executed copy only.

This API accepts exclusively ``BoundEconomicReceiptVerifierV1``.  The Bound
verifier's own exact-``None`` success contract is unchanged: ``False``, ``0``,
any other value and any exception reject as ``RECEIPT_VERIFICATION_FAILED``
with the former fixed detail.

Ownership repair: the former core path checked the caller's head, ran the
callback, then read that caller head and the verifier binding root after I/O.
The head is now owned and its binding root captured before I/O, and no caller
candidate, head, profile or policy alias is read after the callback.  This is
a Python ownership boundary inside one honest process; it is not a claim of
resistance to a compromised Python process or OS.  The marker remains a
shadow marker with no publication, settlement or production authority.
"""

from __future__ import annotations

from ..core.economic_receipt_verifier_deployment_v1 import BoundEconomicReceiptVerifierV1
from ..core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierSelectionPurposeV1,
)
from ..core.global_economic_authority_head_v1 import GlobalEconomicAuthorityHeadV1
from ..core.global_settlement_types_v1 import LaneIdV1
from ..core.zdex_buyback_spot_safety_receipt_preparation_v1 import (
    PreparedZDEXBuybackSpotSafetyReceiptV2,
    _build_verified_zdex_buyback_spot_safety_purchase_v2,
    _require_prepared_execution_binding_v2,
    prepare_zdex_buyback_spot_safety_receipt_v2,
    prepare_zdex_buyback_spot_safety_selection_v2,
    require_zdex_buyback_spot_authority_head_v2,
    require_zdex_buyback_spot_verifier_identity_v2,
    snapshot_prepared_zdex_buyback_spot_safety_receipt_v2,
    snapshot_zdex_buyback_spot_authority_head_v2,
)
from ..core.zdex_buyback_spot_safety_receipt_v1 import (
    VerifiedZDEXBuybackSpotSafetyPurchaseV2,
    ZDEXBuybackSpotReceiptCandidateV2,
    ZDEXBuybackSpotReceiptRejectCodeV1,
    _reject,
)


def _own_authority_head_v2(
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> GlobalEconomicAuthorityHeadV1:
    """Exact head then exact Bound type gates, then the owned complete head.

    The two type gates keep the former compound's first two terms and its
    code and detail, so a malformed exact head paired with a non-Bound
    verifier still reports the authority mismatch.  Ownership then reruns the
    head's own coordinate checks: a malformed exact head with a valid Bound
    capability fails closed here, before any I/O.  This is a named
    strengthening over the former path, which reached the callback with it.
    """

    if (
        type(authority_head) is not GlobalEconomicAuthorityHeadV1
        or type(receipt_verifier) is not BoundEconomicReceiptVerifierV1
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH,
            "receipt verifier is outside the current authority head",
        )
    try:
        return snapshot_zdex_buyback_spot_authority_head_v2(authority_head)
    except (TypeError, ValueError):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH,
            "authority head ownership or invariant validation failed",
        )


def _require_bound_deployment_binding_v2(
    owned_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> None:
    """Run the Bound deployment binding with the owned head's coordinates."""

    try:
        receipt_verifier.require_binding(
            verifier_registry_root=owned_head.verifier_registry_root,
            deployment_root=owned_head.deployment_root,
            profile_root=owned_head.profile_root,
            root_image_id=owned_head.root_image_id,
            selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW,
        )
    except (TypeError, ValueError):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH,
            "receipt verifier deployment binding mismatch",
        )


def _execute_prepared_zdex_buyback_spot_safety_receipt_v2(
    prepared: PreparedZDEXBuybackSpotSafetyReceiptV2,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXBuybackSpotSafetyPurchaseV2:
    """Execute exactly the prepared profile-lane request, then mint.

    A detached core-validated copy is fixed immediately before I/O.
    Unsupported record types and request-unbound fields are refused while
    making that copy, before any call.  Only the executed copy reaches marker
    minting, so callback-side mutation of the caller-held prepared object,
    candidate or head cannot relabel the returned marker.
    """

    if type(receipt_verifier) is not BoundEconomicReceiptVerifierV1:
        raise TypeError("ZDEX buyback Spot receipt verifier must be a bound capability")
    owned = snapshot_prepared_zdex_buyback_spot_safety_receipt_v2(prepared)
    _require_prepared_execution_binding_v2(
        owned,
        executing_verifier_binding_root=receipt_verifier.binding_root,
    )
    try:
        receipt_verifier.verify_profile_lane_receipt(
            owned.receipt_bytes,
            profile=owned.profile,
            lane_id=LaneIdV1.SPOT_LIQUIDITY,
            expected_module_release_id=owned.expected_module_release_id,
            expected_image_id=owned.expected_image_id,
            expected_journal_bytes=owned.expected_journal_bytes,
        )
    except Exception:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.RECEIPT_VERIFICATION_FAILED,
            "receipt callback rejected or failed",
        )
    return _build_verified_zdex_buyback_spot_safety_purchase_v2(owned)


def verify_zdex_buyback_spot_safety_receipt_shadow_v2(
    candidate: ZDEXBuybackSpotReceiptCandidateV2,
    *,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXBuybackSpotSafetyPurchaseV2:
    """Verify exact shadow receipt bindings and return an opaque marker.

    Reject precedence is candidate ownership, governed selection, exact head
    and Bound coordinates, Bound deployment binding, governed policy,
    occurrence, state/Oracle freshness, receipt profile and size, then the
    single external receipt callback.  Any callback exception or non-``None``
    result rejects without creating a marker.
    """

    selection = prepare_zdex_buyback_spot_safety_selection_v2(candidate)
    owned_head = _own_authority_head_v2(authority_head, receipt_verifier)
    require_zdex_buyback_spot_authority_head_v2(selection, owned_head)
    verifier_release_id = receipt_verifier.release_id
    verifier_binding_root = receipt_verifier.binding_root
    require_zdex_buyback_spot_verifier_identity_v2(
        selection,
        owned_head,
        verifier_release_id=verifier_release_id,
        verifier_binding_root=verifier_binding_root,
    )
    _require_bound_deployment_binding_v2(owned_head, receipt_verifier)
    prepared = prepare_zdex_buyback_spot_safety_receipt_v2(
        selection,
        authority_head=owned_head,
        verifier_binding_root=verifier_binding_root,
    )
    return _execute_prepared_zdex_buyback_spot_safety_receipt_v2(prepared, receipt_verifier)


__all__ = [
    "verify_zdex_buyback_spot_safety_receipt_shadow_v2",
]
