"""Receipt preparation for the governed ZDEX buyback Spot safety leaf.

The pure core prepares the shadow Spot safety receipt in two phases so the
former rejection order survives the extraction of the external callback:

1. ``prepare_zdex_buyback_spot_safety_selection_v2`` owns the candidate and
   selects the governed route plus the Spot and tokenomics releases.
2. After the shell has owned the exact authority head, read the Bound
   verifier identity and run its deployment binding,
   ``prepare_zdex_buyback_spot_safety_receipt_v2`` runs the policy,
   occurrence, state/Oracle, receipt-domain and journal-ceiling checks and
   fixes the complete execution request plus every marker source as one
   detached subject.

The head-versus-profile and head-versus-verifier predicates of the former
authority compound live here as pure functions split around the shell's two
Bound identity reads, so the shell reads and the core decides.

Prepared data carries the raw fee-state, the pre-I/O checked authority roots,
and an ephemeral owned complete authority head.  The fee-ingress witness is
derived only by the private completion factory, which the shell calls with the
executed copy after callback success.
The detached copy re-owns every nested value, including the opaque price
authority and price safety witnesses through controlled private data
construction, and rebinds every marker source to the journal commitments.
Prepared records and private factories carry no cryptographic, proof or
publication authority; the marker remains a shadow marker.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace

from .global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from .global_economic_profile_snapshot_v1 import snapshot_economic_profile_v1
from .global_economic_proof_v1 import ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
)
from .global_settlement_types_v1 import (
    EconomicProfileSnapshotV1,
    LaneIdV1,
    LaneModuleReleaseV1,
    RouteReleaseV1,
    _require_atoms_u128,
    _require_root,
    canonical_global_bytes_v1,
    hash_global_v1,
)
from .zdex_atomic_buyback_state_v1 import ZDEXAtomicBuybackTokenomicsStateV1
from .zdex_buyback_price_authority_v1 import (
    _VERIFIED_ZDEX_BUYBACK_PRICE_AUTHORITY_TOKEN_V1,
    VerifiedZDEXBuybackPriceAuthorityV1,
    _VerifiedZDEXBuybackPriceAuthorityFieldsV1,
)
from .zdex_buyback_price_safety_v1 import (
    _VERIFIED_PRICE_SAFETY_TOKEN_V1,
    VerifiedZDEXBuybackPriceSafetyV1,
    ZDEXBuybackPriceSafetyObservationV1,
    _VerifiedZDEXBuybackPriceSafetyFieldsV1,
)
from .zdex_buyback_spend_v1 import ZDEXBuybackSpendPolicyV1
from .zdex_buyback_spot_safety_receipt_v1 import (
    _VERIFIED_ZDEX_BUYBACK_SPOT_TOKEN_V2,
    VerifiedZDEXBuybackSpotSafetyPurchaseV2,
    ZDEXBuybackSpotReceiptCandidateV2,
    ZDEXBuybackSpotReceiptRejectCodeV1,
    ZDEXBuybackSpotSafetyPurchaseJournalV2,
    _reject,
    _require_governed_policy_v1,
    _require_occurrence_bindings_v1,
    _require_state_and_oracle_bindings_v1,
    _select_shadow_route_and_release_v1,
    _snapshot_candidate_v1,
    _snapshot_fee_context_v1,
    _snapshot_journal_v1,
    _snapshot_price_policy_v1,
    _snapshot_spend_policy_v1,
    _snapshot_tokenomics_pre_state_v1,
    _VerifiedZDEXBuybackSpotFieldsV2,
    _ZDEXBuybackSpotReceiptSnapshotV2,
)
from .zdex_fee_allocation_receipt_verification_v1 import (
    _snapshot_fee_policy_v1,
    _snapshot_fee_state_v1,
)
from .zdex_fee_allocation_types_v1 import (
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationPolicyV1,
    ZDEXFeeStateV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEXBuybackExecutionPolicyV1,
)
from .zdex_verified_fee_ingress_slice_v1 import (
    _derive_verified_zdex_fee_ingress_slice_v1,
)

_AUTHORITY_HEAD_DETAIL_V2 = "receipt verifier is outside the current authority head"
_PREPARED_NAME_V2 = "prepared ZDEX buyback Spot receipt"


@dataclass(frozen=True, slots=True)
class PreparedZDEXBuybackSpotSelectionV2:
    """Phase-1 subject: the owned candidate and its profile-selected releases.

    Data only.  The route and both releases are values inside the owned
    profile graph, never the caller's objects.
    """

    owned: _ZDEXBuybackSpotReceiptSnapshotV2
    route: RouteReleaseV1
    spot_release: LaneModuleReleaseV1
    tokenomics_release: LaneModuleReleaseV1

    def __post_init__(self) -> None:
        expected = (
            (self.owned, _ZDEXBuybackSpotReceiptSnapshotV2, "snapshot"),
            (self.route, RouteReleaseV1, "route"),
            (self.spot_release, LaneModuleReleaseV1, "Spot release"),
            (self.tokenomics_release, LaneModuleReleaseV1, "tokenomics release"),
        )
        for value, expected_type, label in expected:
            if type(value) is not expected_type:
                raise TypeError(
                    f"prepared ZDEX buyback Spot selection {label} must be exact typed data"
                )


@dataclass(frozen=True, slots=True)
class PreparedZDEXBuybackSpotSafetyReceiptV2:
    """Complete pure execution subject for one governed Spot safety receipt.

    Data only.  Holding this record is not evidence that any verifier ran.
    The request group is exactly what the shell hands the Bound verifier; the
    marker group is every owned marker source; the ingress group is the raw
    fee state plus the pre-I/O checked roots from which the completion
    factory derives the fee-ingress witness after callback success.  The
    complete authority head is ephemeral preparation data, outside the final
    marker and ingress layouts, that binds ``authority_head_root``.
    """

    # Exact profile-lane receipt request.
    profile: EconomicProfileSnapshotV1
    expected_module_release_id: str
    expected_image_id: str
    receipt_bytes: bytes
    expected_journal_bytes: bytes
    # Owned marker sources.
    journal: ZDEXBuybackSpotSafetyPurchaseJournalV2
    journal_digest: str
    receipt_digest: str
    receipt_kind: ReceiptKindV1
    tokenomics_pre_state: ZDEXAtomicBuybackTokenomicsStateV1
    spend_policy: ZDEXBuybackSpendPolicyV1
    fee_policy: ZDEXFeeAllocationPolicyV1
    fee_context: ZDEXFeeAllocationContextV1
    price_authority: VerifiedZDEXBuybackPriceAuthorityV1
    price_authority_root: str
    # Raw fee-ingress sources and pre-I/O checked roots.
    fee_state: ZDEXFeeStateV1
    command_occurrence_id: str
    global_pre_state_root: str
    profile_root: str
    authority_head: GlobalEconomicAuthorityHeadV1
    authority_head_root: str
    verifier_binding_root: str

    def __post_init__(self) -> None:
        _require_prepared_record_types_v2(self)


def _sha256_root_v2(value: bytes) -> str:
    return "0x" + hashlib.sha256(value).hexdigest()


def _require_prepared_record_types_v2(prepared: PreparedZDEXBuybackSpotSafetyReceiptV2) -> None:
    typed = (
        (prepared.profile, EconomicProfileSnapshotV1, "profile"),
        (prepared.receipt_bytes, bytes, "receipt bytes"),
        (prepared.expected_journal_bytes, bytes, "journal bytes"),
        (prepared.journal, ZDEXBuybackSpotSafetyPurchaseJournalV2, "journal"),
        (prepared.receipt_kind, ReceiptKindV1, "receipt kind"),
        (prepared.tokenomics_pre_state, ZDEXAtomicBuybackTokenomicsStateV1, "tokenomics pre-state"),
        (prepared.spend_policy, ZDEXBuybackSpendPolicyV1, "spend policy"),
        (prepared.fee_policy, ZDEXFeeAllocationPolicyV1, "fee policy"),
        (prepared.fee_context, ZDEXFeeAllocationContextV1, "fee context"),
        (prepared.price_authority, VerifiedZDEXBuybackPriceAuthorityV1, "price authority"),
        (prepared.fee_state, ZDEXFeeStateV1, "fee state"),
        (prepared.authority_head, GlobalEconomicAuthorityHeadV1, "authority head"),
    )
    for value, expected_type, label in typed:
        if type(value) is not expected_type:
            raise TypeError(f"{_PREPARED_NAME_V2} {label} must be exact typed data")
    for name in (
        "expected_module_release_id",
        "expected_image_id",
        "journal_digest",
        "receipt_digest",
        "price_authority_root",
        "command_occurrence_id",
        "global_pre_state_root",
        "profile_root",
        "authority_head_root",
        "verifier_binding_root",
    ):
        value = getattr(prepared, name)
        if type(value) is not str:
            raise TypeError(f"{_PREPARED_NAME_V2} {name} must be exact str")
        _require_root(value, name=f"{_PREPARED_NAME_V2} {name}")


def _own_candidate_v2(
    candidate: ZDEXBuybackSpotReceiptCandidateV2,
) -> _ZDEXBuybackSpotReceiptSnapshotV2:
    try:
        return _snapshot_candidate_v1(candidate)
    except (TypeError, ValueError):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
            "candidate ownership or invariant validation failed",
        )


def prepare_zdex_buyback_spot_safety_selection_v2(
    candidate: ZDEXBuybackSpotReceiptCandidateV2,
) -> PreparedZDEXBuybackSpotSelectionV2:
    """Own the candidate and select the governed route and releases (phase 1).

    Reject precedence is unchanged from the former entry point: candidate
    ownership (``MALFORMED_CANDIDATE``), SHADOW profile, exactly one buyback
    route of the governed shape, then the Spot and tokenomics releases.
    """

    owned = _own_candidate_v2(candidate)
    route, spot_release, tokenomics_release = _select_shadow_route_and_release_v1(owned)
    return PreparedZDEXBuybackSpotSelectionV2(owned, route, spot_release, tokenomics_release)


def snapshot_prepared_zdex_buyback_spot_selection_v2(
    selection: PreparedZDEXBuybackSpotSelectionV2,
) -> PreparedZDEXBuybackSpotSelectionV2:
    """Re-own the phase-1 subject through the candidate's own ownership path."""

    if type(selection) is not PreparedZDEXBuybackSpotSelectionV2:
        raise TypeError("prepared ZDEX buyback Spot selection must be exact typed data")
    owned = selection.owned
    if type(owned) is not _ZDEXBuybackSpotReceiptSnapshotV2:
        raise TypeError("prepared ZDEX buyback Spot selection snapshot must be exact typed data")
    try:
        candidate = ZDEXBuybackSpotReceiptCandidateV2(
            profile=owned.profile,
            policy_registry=owned.policy_registry,
            buyback_policy=owned.buyback_policy,
            spend_policy=owned.spend_policy,
            price_policy=owned.price_policy,
            fee_policy=owned.fee_policy,
            fee_context=owned.fee_context,
            fee_command=owned.fee_command,
            occurrence=owned.occurrence,
            global_pre_state=owned.global_pre_state,
            tokenomics_pre_state=owned.tokenomics_pre_state,
            journal=owned.journal,
            receipt=owned.receipt,
        )
    except (TypeError, ValueError):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.MALFORMED_CANDIDATE,
            "candidate ownership or invariant validation failed",
        )
    return prepare_zdex_buyback_spot_safety_selection_v2(candidate)


def snapshot_zdex_buyback_spot_authority_head_v2(
    authority_head: GlobalEconomicAuthorityHeadV1,
) -> GlobalEconomicAuthorityHeadV1:
    """Own the exact typed head; the copy reruns the head's own coordinate checks."""

    if type(authority_head) is not GlobalEconomicAuthorityHeadV1:
        raise TypeError("ZDEX buyback Spot authority head must be exact typed data")
    return replace(authority_head)


def require_zdex_buyback_spot_authority_head_v2(
    selection: PreparedZDEXBuybackSpotSelectionV2,
    authority_head: GlobalEconomicAuthorityHeadV1,
) -> None:
    """Head-versus-profile half of the former authority compound.

    Status, chain, deployment, profile root, writer epoch and verifier
    registry root are compared in the former order.  The shell reads the
    Bound identity only after this passes, exactly as the former single
    expression short-circuited.
    """

    if type(selection) is not PreparedZDEXBuybackSpotSelectionV2:
        raise TypeError("prepared ZDEX buyback Spot selection must be exact typed data")
    head = snapshot_zdex_buyback_spot_authority_head_v2(authority_head)
    owned = selection.owned
    if (
        head.status is not GlobalEconomicAuthorityStatusV1.ACTIVE
        or head.chain_id != owned.occurrence.chain_id
        or head.deployment_root != owned.occurrence.deployment_root
        or head.profile_root != owned.profile.profile_id
        or head.writer_epoch != owned.profile.authority_epoch
        or head.verifier_registry_root != owned.profile.verifier_registry_root
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH,
            _AUTHORITY_HEAD_DETAIL_V2,
        )


def require_zdex_buyback_spot_verifier_identity_v2(
    selection: PreparedZDEXBuybackSpotSelectionV2,
    authority_head: GlobalEconomicAuthorityHeadV1,
    *,
    verifier_release_id: str,
    verifier_binding_root: str,
) -> None:
    """Head-versus-verifier half of the former authority compound.

    The identity values are plain data the shell read from the Bound
    verifier; release id, binding root and root image are compared in the
    former order with the former single code and detail.
    """

    if type(selection) is not PreparedZDEXBuybackSpotSelectionV2:
        raise TypeError("prepared ZDEX buyback Spot selection must be exact typed data")
    head = snapshot_zdex_buyback_spot_authority_head_v2(authority_head)
    if (
        type(verifier_release_id) is not str
        or type(verifier_binding_root) is not str
        or head.verifier_release_id != verifier_release_id
        or head.verifier_binding_root != verifier_binding_root
        or head.root_image_id != selection.owned.profile.root_image_id
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH,
            _AUTHORITY_HEAD_DETAIL_V2,
        )


def _require_admissible_receipt_v2(
    owned: _ZDEXBuybackSpotReceiptSnapshotV2,
    route: RouteReleaseV1,
    spot_release: LaneModuleReleaseV1,
) -> bytes:
    """Succinct kind, nonempty bytes, then the route/Spot journal ceiling.

    The ceiling is ``min(route.max_journal_bytes, spot_release.max_journal_bytes)``
    and equality is admissible.
    """

    receipt = owned.receipt
    if receipt.receipt_kind is not ReceiptKindV1.SUCCINCT:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.UNSUPPORTED_RECEIPT_KIND,
            "only Succinct receipts are admissible",
        )
    if not receipt.receipt_bytes:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.EMPTY_RECEIPT,
            "receipt bytes must be nonempty",
        )
    journal_bytes = canonical_global_bytes_v1(owned.journal)
    if len(journal_bytes) > min(route.max_journal_bytes, spot_release.max_journal_bytes):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.JOURNAL_TOO_LARGE,
            "canonical journal exceeds the selected release ceiling",
        )
    return journal_bytes


def _require_prepared_authority_v2(
    selection: PreparedZDEXBuybackSpotSelectionV2,
    authority_head: GlobalEconomicAuthorityHeadV1,
    verifier_binding_root: str,
) -> GlobalEconomicAuthorityHeadV1:
    """Re-apply the pure head predicates on the owned inputs of phase 2.

    The verifier binding root is the value the shell captured from the Bound
    verifier before any I/O; it must equal the owned head's own binding root.
    """

    head = snapshot_zdex_buyback_spot_authority_head_v2(authority_head)
    require_zdex_buyback_spot_authority_head_v2(selection, head)
    if (
        type(verifier_binding_root) is not str
        or head.verifier_binding_root != verifier_binding_root
        or head.root_image_id != selection.owned.profile.root_image_id
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH,
            _AUTHORITY_HEAD_DETAIL_V2,
        )
    return head


def prepare_zdex_buyback_spot_safety_receipt_v2(
    selection: PreparedZDEXBuybackSpotSelectionV2,
    *,
    authority_head: GlobalEconomicAuthorityHeadV1,
    verifier_binding_root: str,
) -> PreparedZDEXBuybackSpotSafetyReceiptV2:
    """Fix the complete execution subject with no verifier call (phase 2).

    Reject precedence after the shell's authority step is unchanged: governed
    policy, occurrence bindings, state/Oracle bindings with the pure price
    authority, Succinct kind, nonempty receipt, then the journal ceiling.
    The fee-ingress witness is not derived here.
    """

    owned_selection = snapshot_prepared_zdex_buyback_spot_selection_v2(selection)
    head = _require_prepared_authority_v2(owned_selection, authority_head, verifier_binding_root)
    owned = owned_selection.owned
    route = owned_selection.route
    spot_release = owned_selection.spot_release
    _require_governed_policy_v1(owned, route)
    _require_occurrence_bindings_v1(owned, route, spot_release, owned_selection.tokenomics_release)
    price_authority = _require_state_and_oracle_bindings_v1(owned, route)
    journal_bytes = _require_admissible_receipt_v2(owned, route, spot_release)
    return PreparedZDEXBuybackSpotSafetyReceiptV2(
        profile=owned.profile,
        expected_module_release_id=spot_release.release_id,
        expected_image_id=spot_release.guest_image_id,
        receipt_bytes=owned.receipt.receipt_bytes,
        expected_journal_bytes=journal_bytes,
        journal=owned.journal,
        journal_digest=_sha256_root_v2(journal_bytes),
        receipt_digest=_sha256_root_v2(owned.receipt.receipt_bytes),
        receipt_kind=owned.receipt.receipt_kind,
        tokenomics_pre_state=owned.tokenomics_pre_state,
        spend_policy=owned.spend_policy,
        fee_policy=owned.fee_policy,
        fee_context=owned.fee_context,
        price_authority=price_authority,
        price_authority_root=price_authority.authority_root,
        fee_state=owned.tokenomics_pre_state.fee_state_for(owned.journal.quote_asset_id),
        command_occurrence_id=owned.occurrence.occurrence_id,
        global_pre_state_root=owned.global_pre_state.state_root,
        profile_root=owned.profile.profile_id,
        authority_head=head,
        authority_head_root=head.authority_root,
        verifier_binding_root=verifier_binding_root,
    )


def _snapshot_price_safety_v2(
    witness: VerifiedZDEXBuybackPriceSafetyV1,
) -> VerifiedZDEXBuybackPriceSafetyV1:
    """Own one exact price-safety witness by copying its checked private data.

    Controlled private data construction only: the copied policy, observation
    and derived limits rerun their own validators, and the witness identity is
    preserved.  No price envelope is re-decided and no authority is granted.
    """

    if type(witness) is not VerifiedZDEXBuybackPriceSafetyV1:
        raise TypeError(f"{_PREPARED_NAME_V2} price safety must be exact typed data")
    fields = witness._fields
    if type(fields) is not _VerifiedZDEXBuybackPriceSafetyFieldsV1:
        raise TypeError(f"{_PREPARED_NAME_V2} price safety fields must be exact typed data")
    if type(fields.observation) is not ZDEXBuybackPriceSafetyObservationV1:
        raise TypeError(f"{_PREPARED_NAME_V2} price observation must be exact typed data")
    _require_exact_dataclass_scalars_v1(fields.observation, name="ZDEX buyback price observation")
    for name in ("route_safe_quote_limit_atoms", "minimum_output_atoms"):
        value = getattr(fields, name)
        if type(value) is not int:
            raise TypeError(f"{_PREPARED_NAME_V2} price safety {name} must be exact int")
        _require_atoms_u128(value, name=f"{_PREPARED_NAME_V2} price safety {name}")
    return VerifiedZDEXBuybackPriceSafetyV1(
        _VERIFIED_PRICE_SAFETY_TOKEN_V1,
        _VerifiedZDEXBuybackPriceSafetyFieldsV1(
            _snapshot_price_policy_v1(fields.policy),
            replace(fields.observation),
            fields.route_safe_quote_limit_atoms,
            fields.minimum_output_atoms,
        ),
    )


def _snapshot_price_authority_v2(
    witness: VerifiedZDEXBuybackPriceAuthorityV1,
) -> VerifiedZDEXBuybackPriceAuthorityV1:
    """Own one exact price-authority witness and its nested price safety."""

    if type(witness) is not VerifiedZDEXBuybackPriceAuthorityV1:
        raise TypeError(f"{_PREPARED_NAME_V2} price authority must be exact typed data")
    fields = witness._fields
    if type(fields) is not _VerifiedZDEXBuybackPriceAuthorityFieldsV1:
        raise TypeError(f"{_PREPARED_NAME_V2} price authority fields must be exact typed data")
    roots = (
        fields.pre_state_root,
        fields.command_occurrence_id,
        fields.execution_policy_root,
        fields.price_policy_root,
        fields.price_occurrence_root,
    )
    for index, value in enumerate(roots):
        if type(value) is not str:
            raise TypeError(f"{_PREPARED_NAME_V2} price authority root {index} must be exact str")
        _require_root(value, name=f"{_PREPARED_NAME_V2} price authority root {index}")
    return VerifiedZDEXBuybackPriceAuthorityV1(
        _VERIFIED_ZDEX_BUYBACK_PRICE_AUTHORITY_TOKEN_V1,
        _VerifiedZDEXBuybackPriceAuthorityFieldsV1(
            *roots,
            _snapshot_price_safety_v2(fields.price_safety),
        ),
    )


def _journal_observation_v2(
    journal: ZDEXBuybackSpotSafetyPurchaseJournalV2,
) -> ZDEXBuybackPriceSafetyObservationV1:
    """The price-safety observation the journal commits, as the verifier built it."""

    return ZDEXBuybackPriceSafetyObservationV1(
        oracle_occurrence_root=journal.oracle_occurrence_root,
        current_height=journal.consensus_height,
        oracle_observed_height=journal.oracle_observed_height,
        oracle_quote_numerator_atoms=journal.oracle_quote_numerator_atoms,
        oracle_zdex_denominator_atoms=journal.oracle_zdex_denominator_atoms,
        quote_reserve_atoms=journal.quote_reserve_atoms,
        zdex_reserve_atoms=journal.zdex_reserve_atoms,
        quote_amount_in_atoms=journal.quote_amount_in_atoms,
        purchased_zdex_atoms=journal.purchased_zdex_atoms,
        claimed_route_safe_quote_limit_atoms=journal.route_safe_quote_limit_atoms,
        claimed_minimum_output_atoms=journal.minimum_output_atoms,
    )


def _require_prepared_request_binding_v2(
    prepared: PreparedZDEXBuybackSpotSafetyReceiptV2,
) -> None:
    """Bind bytes, digests, image, receipt domain and ceiling to the owned journal."""

    journal = prepared.journal
    profile = prepared.profile
    release = profile.lane_registry.release_for(LaneIdV1.SPOT_LIQUIDITY)
    routes = tuple(
        route
        for route in profile.route_registry.routes
        if route.route_release_id == journal.route_release_id
        and route.command_kind == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1
    )
    if prepared.receipt_digest != _sha256_root_v2(prepared.receipt_bytes):
        raise ValueError(f"{_PREPARED_NAME_V2} receipt digest mismatch")
    if prepared.expected_journal_bytes != canonical_global_bytes_v1(journal):
        raise ValueError(f"{_PREPARED_NAME_V2} journal bytes mismatch")
    if prepared.journal_digest != _sha256_root_v2(prepared.expected_journal_bytes):
        raise ValueError(f"{_PREPARED_NAME_V2} journal digest mismatch")
    if (
        prepared.expected_module_release_id != release.release_id
        or prepared.expected_image_id != release.guest_image_id
        or journal.spot_module_release_id != release.release_id
        or journal.spot_guest_image_id != release.guest_image_id
        or journal.tokenomics_module_release_id
        != profile.lane_registry.release_for(LaneIdV1.ZDEX_TOKENOMICS).release_id
        or journal.writer_epoch != profile.authority_epoch
    ):
        raise ValueError(f"{_PREPARED_NAME_V2} request image is outside the profile")
    if prepared.receipt_kind is not ReceiptKindV1.SUCCINCT or not prepared.receipt_bytes:
        raise ValueError(f"{_PREPARED_NAME_V2} receipt domain is outside the admissible kind")
    if len(routes) != 1 or len(prepared.expected_journal_bytes) > min(
        routes[0].max_journal_bytes, release.max_journal_bytes
    ):
        raise ValueError(f"{_PREPARED_NAME_V2} journal is outside the selected route ceiling")


def _require_prepared_marker_binding_v2(
    prepared: PreparedZDEXBuybackSpotSafetyReceiptV2,
    *,
    authority_head: GlobalEconomicAuthorityHeadV1,
) -> None:
    """Bind every owned marker source and ingress root to the journal commitments."""

    journal = prepared.journal
    tokenomics = prepared.tokenomics_pre_state
    if (
        prepared.profile_root != prepared.profile.profile_id
        or prepared.profile_root != journal.profile_root
        or prepared.command_occurrence_id != journal.command_occurrence_id
        or prepared.global_pre_state_root != journal.global_pre_state_root
    ):
        raise ValueError(f"{_PREPARED_NAME_V2} ingress roots are outside the journal")
    if prepared.authority_head_root != authority_head.authority_root:
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH,
            _AUTHORITY_HEAD_DETAIL_V2,
        )
    if (
        journal.spend_policy_root != prepared.spend_policy.policy_root
        or journal.fee_policy_root != prepared.fee_policy.policy_root
        or journal.fee_context_root
        != hash_global_v1("zdex-fee-allocation-context-v1", prepared.fee_context.to_canonical())
        or journal.tokenomics_pre_state_root != tokenomics.state_root
        or journal.cadence_pre_state_root
        != tokenomics.cadence_state_for(journal.quote_asset_id).state_root
    ):
        raise ValueError(f"{_PREPARED_NAME_V2} marker policies are outside the journal")
    if (
        prepared.fee_state != tokenomics.fee_state_for(journal.quote_asset_id)
        or journal.fee_pre_state_root != prepared.fee_state.state_root
        or journal.fee_command_root
        != hash_global_v1(
            "zdex-fee-allocation-command-v1",
            {"fee_charged_atoms": prepared.fee_state.fee_ingress_atoms},
        )
    ):
        raise ValueError(f"{_PREPARED_NAME_V2} fee state is outside the tokenomics pre-state")


def _require_prepared_price_authority_binding_v2(
    prepared: PreparedZDEXBuybackSpotSafetyReceiptV2,
) -> None:
    """Bind the owned price authority and its nested price safety to the journal."""

    journal = prepared.journal
    price_authority = prepared.price_authority
    price_safety = price_authority.price_safety
    execution_policy = ZDEXBuybackExecutionPolicyV1(
        pool_id=journal.pool_id,
        pool_definition_root=journal.pool_definition_root,
        quote_asset_id=journal.quote_asset_id,
        zdex_asset_id=journal.zdex_asset_id,
    )
    if (
        price_authority.authority_root != prepared.price_authority_root
        or price_authority.pre_state_root != journal.global_pre_state_root
        or price_authority.command_occurrence_id != journal.command_occurrence_id
        or price_authority.execution_policy_root != execution_policy.policy_root
        or price_authority.price_policy_root != journal.oracle_policy_root
        or price_authority.price_occurrence_root != journal.oracle_occurrence_root
        or price_safety.policy_root != journal.oracle_policy_root
        or price_safety.observation_root != _journal_observation_v2(journal).observation_root
        or price_safety.route_safe_quote_limit_atoms != journal.route_safe_quote_limit_atoms
        or price_safety.minimum_output_atoms != journal.minimum_output_atoms
    ):
        raise ValueError(f"{_PREPARED_NAME_V2} price authority root mismatch")


def _require_prepared_execution_binding_v2(
    prepared: PreparedZDEXBuybackSpotSafetyReceiptV2,
    *,
    executing_verifier_binding_root: str,
) -> None:
    """Bind a detached prepared root to the exact Bound identity read by shell.

    The shell has already established the exact Bound capability type.  This
    pure comparison deliberately receives only its captured root, so the core
    does not import, retain, or invoke the effectful capability.
    """

    if (
        type(executing_verifier_binding_root) is not str
        or prepared.verifier_binding_root != executing_verifier_binding_root
    ):
        _reject(
            ZDEXBuybackSpotReceiptRejectCodeV1.AUTHORITY_BINDING_MISMATCH,
            _AUTHORITY_HEAD_DETAIL_V2,
        )


def snapshot_prepared_zdex_buyback_spot_safety_receipt_v2(
    prepared: PreparedZDEXBuybackSpotSafetyReceiptV2,
) -> PreparedZDEXBuybackSpotSafetyReceiptV2:
    """Return a validated detached copy of one prepared Spot safety subject.

    Exact record and nested types plus request-to-marker binding are
    rechecked against the owned journal, then every nested value, including
    both opaque price witnesses, is copied through its own owning snapshot so
    no caller-held alias survives into the copy.
    """

    if type(prepared) is not PreparedZDEXBuybackSpotSafetyReceiptV2:
        raise TypeError(f"{_PREPARED_NAME_V2} must be exact typed data")
    _require_prepared_record_types_v2(prepared)
    authority_head = snapshot_zdex_buyback_spot_authority_head_v2(prepared.authority_head)
    _require_prepared_request_binding_v2(prepared)
    _require_prepared_marker_binding_v2(prepared, authority_head=authority_head)
    _require_prepared_price_authority_binding_v2(prepared)
    return PreparedZDEXBuybackSpotSafetyReceiptV2(
        profile=snapshot_economic_profile_v1(prepared.profile),
        expected_module_release_id=prepared.expected_module_release_id,
        expected_image_id=prepared.expected_image_id,
        receipt_bytes=prepared.receipt_bytes,
        expected_journal_bytes=prepared.expected_journal_bytes,
        journal=_snapshot_journal_v1(prepared.journal),
        journal_digest=prepared.journal_digest,
        receipt_digest=prepared.receipt_digest,
        receipt_kind=prepared.receipt_kind,
        tokenomics_pre_state=_snapshot_tokenomics_pre_state_v1(prepared.tokenomics_pre_state),
        spend_policy=_snapshot_spend_policy_v1(prepared.spend_policy),
        fee_policy=_snapshot_fee_policy_v1(prepared.fee_policy),
        fee_context=_snapshot_fee_context_v1(prepared.fee_context),
        price_authority=_snapshot_price_authority_v2(prepared.price_authority),
        price_authority_root=prepared.price_authority_root,
        fee_state=_snapshot_fee_state_v1(prepared.fee_state),
        command_occurrence_id=prepared.command_occurrence_id,
        global_pre_state_root=prepared.global_pre_state_root,
        profile_root=prepared.profile_root,
        authority_head=authority_head,
        authority_head_root=prepared.authority_head_root,
        verifier_binding_root=prepared.verifier_binding_root,
    )


def _build_verified_zdex_buyback_spot_safety_purchase_v2(
    prepared: PreparedZDEXBuybackSpotSafetyReceiptV2,
) -> VerifiedZDEXBuybackSpotSafetyPurchaseV2:
    """Mint the existing marker from one validated prepared subject.

    Deterministic data construction only.  Post-callback sequencing belongs
    to the shell, which calls this with the detached copy it executed.  The
    fee-ingress witness is derived here from the raw fee state and the
    pre-I/O checked roots, and ``fee_command`` is derived from that witness
    exactly as before.  This factory is not a verifier.
    """

    owned = snapshot_prepared_zdex_buyback_spot_safety_receipt_v2(prepared)
    fee_ingress = _derive_verified_zdex_fee_ingress_slice_v1(
        command_occurrence_id=owned.command_occurrence_id,
        global_pre_state_root=owned.global_pre_state_root,
        profile_root=owned.profile_root,
        fee_state=owned.fee_state,
        authority_head_root=owned.authority_head_root,
        verifier_binding_root=owned.verifier_binding_root,
    )
    fields = _VerifiedZDEXBuybackSpotFieldsV2(
        journal=owned.journal,
        journal_digest=owned.journal_digest,
        expected_image_id=owned.expected_image_id,
        receipt_digest=owned.receipt_digest,
        receipt_kind=owned.receipt_kind,
        tokenomics_pre_state=owned.tokenomics_pre_state,
        spend_policy=owned.spend_policy,
        fee_policy=owned.fee_policy,
        fee_context=owned.fee_context,
        fee_command=ZDEXFeeAllocationCommandV1(fee_ingress.fee_ingress_atoms),
        fee_ingress=fee_ingress,
        price_authority=owned.price_authority,
        authority_head_root=owned.authority_head_root,
        verifier_binding_root=owned.verifier_binding_root,
    )
    return VerifiedZDEXBuybackSpotSafetyPurchaseV2(_VERIFIED_ZDEX_BUYBACK_SPOT_TOKEN_V2, fields)


__all__ = [
    "PreparedZDEXBuybackSpotSafetyReceiptV2",
    "PreparedZDEXBuybackSpotSelectionV2",
    "prepare_zdex_buyback_spot_safety_receipt_v2",
    "prepare_zdex_buyback_spot_safety_selection_v2",
    "require_zdex_buyback_spot_authority_head_v2",
    "require_zdex_buyback_spot_verifier_identity_v2",
    "snapshot_prepared_zdex_buyback_spot_safety_receipt_v2",
    "snapshot_prepared_zdex_buyback_spot_selection_v2",
    "snapshot_zdex_buyback_spot_authority_head_v2",
]
