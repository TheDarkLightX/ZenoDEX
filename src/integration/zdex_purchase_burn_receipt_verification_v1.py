"""Reference receipt execution for the legacy ZDEX purchase V1/V2 and burn V1 leaves.

Core prepares one exact detached subject (the complete marker fields plus the
exact receipt, module image and canonical journal bytes) and performs no
verifier call.  This shell executes exactly that subject on the caller-supplied
verifier, then mints the existing process-local markers from the executed
snapshot only.

The generic ``ZDEXLaneSuccinctReceiptVerifierV1`` port's return value is
ignored, as the former core path did; the measured Bound verifier enforces its
own exact success contract internally.  The governed entry points own the
exact typed authority head before its checked use and before I/O, capture the
checked verifier binding root before I/O, and never read a caller-held head,
profile or policy alias after the callback to construct a marker.  This is an
ownership repair for callback-retained aliases inside one honest process; it
is not a claim of resistance to a compromised Python process or OS.

Every marker remains a shadow/reference marker with no publication,
settlement or production authority.
"""

from __future__ import annotations

from typing import Protocol

from ..core.economic_receipt_verifier_deployment_v1 import BoundEconomicReceiptVerifierV1
from ..core.global_economic_authority_head_v1 import GlobalEconomicAuthorityHeadV1
from ..core.global_settlement_types_v1 import (
    EconomicPolicyRegistryV1,
    EconomicProfileSnapshotV1,
    LaneIdV1,
)
from ..core.zdex_purchase_burn_receipt_preparation_v1 import (
    PreparedGovernedZDEXAMMPurchaseReceiptV2,
    PreparedZDEXAMMPurchaseReceiptV1,
    PreparedZDEXAMMPurchaseReceiptV2,
    PreparedZDEXBurnReceiptV1,
    _build_governed_verified_zdex_amm_purchase_v2,
    _build_verified_zdex_amm_purchase_v1,
    _build_verified_zdex_amm_purchase_v2,
    _build_verified_zdex_burn_v1,
    prepare_governed_zdex_amm_purchase_receipt_shadow_v1,
    prepare_governed_zdex_amm_purchase_receipt_shadow_v2,
    prepare_governed_zdex_burn_receipt_shadow_v1,
    prepare_zdex_amm_purchase_receipt_v1,
    prepare_zdex_amm_purchase_receipt_v2,
    prepare_zdex_burn_receipt_v1,
    snapshot_governed_receipt_authority_head_v1,
    snapshot_prepared_governed_zdex_amm_purchase_receipt_v2,
    snapshot_prepared_zdex_amm_purchase_receipt_v1,
    snapshot_prepared_zdex_amm_purchase_receipt_v2,
    snapshot_prepared_zdex_burn_receipt_v1,
    snapshot_zdex_burn_receipt_candidate_v1,
    snapshot_zdex_purchase_receipt_candidate_v1,
    snapshot_zdex_purchase_receipt_candidate_v2,
)
from ..core.zdex_purchase_burn_receipt_verification_v1 import (
    GovernedVerifiedZDEXAMMPurchaseV2,
    VerifiedZDEXAMMPurchaseV1,
    VerifiedZDEXAMMPurchaseV2,
    VerifiedZDEXBurnV1,
    ZDEXBurnReceiptCandidateV1,
    ZDEXPurchaseReceiptCandidateV1,
    ZDEXPurchaseReceiptCandidateV2,
    _require_current_shadow_authority_v1,
)


class ZDEXLaneSuccinctReceiptVerifierV1(Protocol):
    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None: ...


class _ProfileLaneReceiptVerifierV1:
    """Narrow adapter that removes caller-selected lane image authority."""

    __slots__ = ("_bound", "_profile", "_lane_id", "_module_release_id")

    def __init__(
        self,
        bound: BoundEconomicReceiptVerifierV1,
        profile: EconomicProfileSnapshotV1,
        lane_id: LaneIdV1,
        module_release_id: str,
    ) -> None:
        self._bound = bound
        self._profile = profile
        self._lane_id = lane_id
        self._module_release_id = module_release_id

    def verify_succinct_receipt(
        self,
        receipt_bytes: bytes,
        *,
        expected_image_id: str,
        expected_journal_bytes: bytes,
    ) -> None:
        self._bound.verify_profile_lane_receipt(
            receipt_bytes,
            profile=self._profile,
            lane_id=self._lane_id,
            expected_module_release_id=self._module_release_id,
            expected_image_id=expected_image_id,
            expected_journal_bytes=expected_journal_bytes,
        )


_PreparedLeafReceiptV1 = (
    PreparedZDEXAMMPurchaseReceiptV1
    | PreparedZDEXAMMPurchaseReceiptV2
    | PreparedZDEXBurnReceiptV1
)


def _own_governed_authority_head_v1(
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> GlobalEconomicAuthorityHeadV1:
    """Exact type gates in the historical order, then the owned complete head.

    The candidate snapshot precedes this call.  The exact head type and the
    exact Bound capability type are checked before the head is reconstructed,
    so a corrupted exact head paired with a non-Bound verifier still reports
    the Bound type error first, as the shared authority helper always did.
    Reconstruction then reruns the head's own twelve-coordinate checks; a
    corrupted exact head with a valid Bound capability is rejected here before
    any I/O.  No economic authority predicate is duplicated in this shell.
    """

    if type(authority_head) is not GlobalEconomicAuthorityHeadV1:
        raise TypeError("ZDEX governed receipt authority head must be exact typed data")
    if type(receipt_verifier) is not BoundEconomicReceiptVerifierV1:
        raise TypeError("ZDEX governed receipt verifier must be a bound capability")
    return snapshot_governed_receipt_authority_head_v1(authority_head)


def _execute_exact_receipt_request_v1(
    owned: _PreparedLeafReceiptV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> None:
    """Perform the single verifier call on one detached prepared subject.

    The historical contract ignores every normal return value, including
    ``False`` and ``0``; only an exception refuses the marker.
    """

    receipt_verifier.verify_succinct_receipt(
        owned.receipt_bytes,
        expected_image_id=owned.expected_image_id,
        expected_journal_bytes=owned.expected_journal_bytes,
    )


def _execute_prepared_zdex_amm_purchase_receipt_v1(
    prepared: PreparedZDEXAMMPurchaseReceiptV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXAMMPurchaseV1:
    """Execute exactly the prepared receipt, image and journal, then mint.

    A detached core-validated copy is fixed before I/O.  Unsupported record
    types and digest-unbound bytes are refused while making that copy, before
    any call.  Only the executed copy reaches marker minting, so callback-side
    mutation of the caller-held prepared object or candidate cannot relabel
    the returned marker.
    """

    owned = snapshot_prepared_zdex_amm_purchase_receipt_v1(prepared)
    _execute_exact_receipt_request_v1(owned, receipt_verifier)
    return _build_verified_zdex_amm_purchase_v1(owned)


def _execute_prepared_zdex_amm_purchase_receipt_v2(
    prepared: PreparedZDEXAMMPurchaseReceiptV2,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXAMMPurchaseV2:
    """Execute exactly the prepared V2 subject, then mint from the executed copy."""

    owned = snapshot_prepared_zdex_amm_purchase_receipt_v2(prepared)
    _execute_exact_receipt_request_v1(owned, receipt_verifier)
    return _build_verified_zdex_amm_purchase_v2(owned)


def _execute_prepared_zdex_burn_receipt_v1(
    prepared: PreparedZDEXBurnReceiptV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXBurnV1:
    """Execute exactly the prepared burn subject, then mint from the executed copy."""

    owned = snapshot_prepared_zdex_burn_receipt_v1(prepared)
    _execute_exact_receipt_request_v1(owned, receipt_verifier)
    return _build_verified_zdex_burn_v1(owned)


def _execute_prepared_governed_zdex_amm_purchase_receipt_v2(
    prepared: PreparedGovernedZDEXAMMPurchaseReceiptV2,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> GovernedVerifiedZDEXAMMPurchaseV2:
    """Execute exactly the prepared governed V2 leaf, then mint from the executed copy."""

    owned = snapshot_prepared_governed_zdex_amm_purchase_receipt_v2(prepared)
    _execute_exact_receipt_request_v1(owned.leaf, receipt_verifier)
    return _build_governed_verified_zdex_amm_purchase_v2(owned)


def verify_zdex_amm_purchase_receipt_v1(
    candidate: ZDEXPurchaseReceiptCandidateV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXAMMPurchaseV1:
    """Authenticate exact AMM output under its release-selected shadow image.

    Core preparation runs every candidate, release, occurrence, binding,
    effect and receipt-shape check first, so no previously rejected input
    reaches the verifier.
    """

    prepared = prepare_zdex_amm_purchase_receipt_v1(candidate)
    return _execute_prepared_zdex_amm_purchase_receipt_v1(prepared, receipt_verifier)


def verify_zdex_amm_purchase_receipt_v2(
    candidate: ZDEXPurchaseReceiptCandidateV2,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXAMMPurchaseV2:
    """Authenticate a purchase whose price inputs have committed authority."""

    prepared = prepare_zdex_amm_purchase_receipt_v2(candidate)
    return _execute_prepared_zdex_amm_purchase_receipt_v2(prepared, receipt_verifier)


def verify_zdex_burn_receipt_v1(
    candidate: ZDEXBurnReceiptCandidateV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXBurnV1:
    """Authenticate exact burn output under its release-selected shadow image."""

    prepared = prepare_zdex_burn_receipt_v1(candidate)
    return _execute_prepared_zdex_burn_receipt_v1(prepared, receipt_verifier)


def verify_governed_zdex_amm_purchase_receipt_shadow_v1(
    candidate: ZDEXPurchaseReceiptCandidateV1,
    *,
    profile: EconomicProfileSnapshotV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXAMMPurchaseV1:
    """Verify a purchase under the current profile-selected Spot image.

    Sequence: own the candidate, gate the exact head and Bound types, own the
    complete head, run the retained current-authority helper on the owned
    head, capture the checked verifier binding root, prepare purely, execute
    once, mint from the executed copy.
    """

    owned = snapshot_zdex_purchase_receipt_candidate_v1(candidate)
    owned_head = _own_governed_authority_head_v1(authority_head, receipt_verifier)
    owned_profile = _require_current_shadow_authority_v1(
        profile=profile,
        route=owned.route_release,
        release=owned.module_release,
        occurrence=owned.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        authority_head=owned_head,
        receipt_verifier=receipt_verifier,
    )
    verifier_binding_root = receipt_verifier.binding_root
    prepared = prepare_governed_zdex_amm_purchase_receipt_shadow_v1(
        owned,
        profile=owned_profile,
        authority_head=owned_head,
        verifier_binding_root=verifier_binding_root,
    )
    return _execute_prepared_zdex_amm_purchase_receipt_v1(
        prepared,
        _ProfileLaneReceiptVerifierV1(
            receipt_verifier,
            owned_profile,
            LaneIdV1.SPOT_LIQUIDITY,
            prepared.verified_fields.module_release_id,
        ),
    )


def verify_governed_zdex_amm_purchase_receipt_shadow_v2(
    candidate: ZDEXPurchaseReceiptCandidateV2,
    *,
    profile: EconomicProfileSnapshotV1,
    policy_registry: EconomicPolicyRegistryV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> GovernedVerifiedZDEXAMMPurchaseV2:
    """Verify an authority-bound purchase under the selected Spot image."""

    owned = snapshot_zdex_purchase_receipt_candidate_v2(candidate)
    owned_head = _own_governed_authority_head_v1(authority_head, receipt_verifier)
    owned_profile = _require_current_shadow_authority_v1(
        profile=profile,
        route=owned.route_release,
        release=owned.module_release,
        occurrence=owned.occurrence,
        lane_id=LaneIdV1.SPOT_LIQUIDITY,
        authority_head=owned_head,
        receipt_verifier=receipt_verifier,
    )
    verifier_binding_root = receipt_verifier.binding_root
    prepared = prepare_governed_zdex_amm_purchase_receipt_shadow_v2(
        owned,
        profile=owned_profile,
        policy_registry=policy_registry,
        authority_head=owned_head,
        verifier_binding_root=verifier_binding_root,
    )
    return _execute_prepared_governed_zdex_amm_purchase_receipt_v2(
        prepared,
        _ProfileLaneReceiptVerifierV1(
            receipt_verifier,
            owned_profile,
            LaneIdV1.SPOT_LIQUIDITY,
            prepared.leaf.verified_fields.module_release_id,
        ),
    )


def verify_governed_zdex_burn_receipt_shadow_v1(
    candidate: ZDEXBurnReceiptCandidateV1,
    *,
    profile: EconomicProfileSnapshotV1,
    authority_head: GlobalEconomicAuthorityHeadV1,
    receipt_verifier: BoundEconomicReceiptVerifierV1,
) -> VerifiedZDEXBurnV1:
    """Verify a burn under the current profile-selected tokenomics image."""

    owned = snapshot_zdex_burn_receipt_candidate_v1(candidate)
    owned_head = _own_governed_authority_head_v1(authority_head, receipt_verifier)
    owned_profile = _require_current_shadow_authority_v1(
        profile=profile,
        route=owned.route_release,
        release=owned.module_release,
        occurrence=owned.occurrence,
        lane_id=LaneIdV1.ZDEX_TOKENOMICS,
        authority_head=owned_head,
        receipt_verifier=receipt_verifier,
    )
    verifier_binding_root = receipt_verifier.binding_root
    prepared = prepare_governed_zdex_burn_receipt_shadow_v1(
        owned,
        profile=owned_profile,
        authority_head=owned_head,
        verifier_binding_root=verifier_binding_root,
    )
    return _execute_prepared_zdex_burn_receipt_v1(
        prepared,
        _ProfileLaneReceiptVerifierV1(
            receipt_verifier,
            owned_profile,
            LaneIdV1.ZDEX_TOKENOMICS,
            prepared.verified_fields.module_release_id,
        ),
    )


__all__ = [
    "ZDEXLaneSuccinctReceiptVerifierV1",
    "verify_governed_zdex_amm_purchase_receipt_shadow_v1",
    "verify_governed_zdex_amm_purchase_receipt_shadow_v2",
    "verify_governed_zdex_burn_receipt_shadow_v1",
    "verify_zdex_amm_purchase_receipt_v1",
    "verify_zdex_amm_purchase_receipt_v2",
    "verify_zdex_burn_receipt_v1",
]
