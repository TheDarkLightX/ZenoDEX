"""SHADOW receipt admission for one complete ZDEX fee-allocation lane."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace

from .global_economic_proof_v1 import EconomicCommandOccurrenceV1, ReceiptKindV1
from .global_economic_refinement_snapshot_v1 import (
    _require_exact_dataclass_scalars_v1,
    _snapshot_occurrence_v1,
)
from .global_settlement_types_v1 import canonical_global_bytes_v1
from .zdex_fee_allocation_profile_binding_v1 import (
    GovernedZDEXFeeAllocationProfileV1,
    _revalidate_governed_fee_profile,
)
from .zdex_fee_allocation_receipt_verification_v1 import (
    VerifiedZDEXFeeAllocationV1,
    _VerifiedZDEXFeeAllocationFieldsV1,
)
from .zdex_fee_allocation_types_v1 import PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1
from .zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXLaneReceiptEnvelopeV1,
    ZDEXLaneSuccinctReceiptVerifierV1,
)
from .zdex_tokenomics_fee_lane_coordinator_v1 import (
    ZDEXTokenomicsFeeAllocationLaneCandidateV1,
    _snapshot_zdex_tokenomics_fee_lane_candidate_v1,
    compose_zdex_tokenomics_fee_allocation_lane_v1,
)
from .zdex_tokenomics_lane_receipt_common_v1 import (
    VerifiedZDEXTokenomicsLaneV1,
    _verify_and_build_zdex_tokenomics_lane_v1,
    _ZDEXTokenomicsCoordinatorReceiptExpectationV1,
    _ZDEXTokenomicsLaneBindingV1,
)
from .zdex_tokenomics_lane_v1 import ZDEXTokenomicsLaneCompositionAcceptedV1


@dataclass(frozen=True, slots=True)
class ZDEXTokenomicsFeeLaneReceiptCandidateV1:
    occurrence: EconomicCommandOccurrenceV1
    lane_candidate: ZDEXTokenomicsFeeAllocationLaneCandidateV1
    verified_allocation: VerifiedZDEXFeeAllocationV1
    receipt: ZDEXLaneReceiptEnvelopeV1

    def __post_init__(self) -> None:
        expected = (
            (self.occurrence, EconomicCommandOccurrenceV1, "occurrence"),
            (
                self.lane_candidate,
                ZDEXTokenomicsFeeAllocationLaneCandidateV1,
                "lane candidate",
            ),
            (
                self.verified_allocation,
                VerifiedZDEXFeeAllocationV1,
                "verified allocation",
            ),
            (self.receipt, ZDEXLaneReceiptEnvelopeV1, "receipt"),
        )
        for value, expected_type, label in expected:
            if type(value) is not expected_type:
                raise TypeError(
                    f"ZDEX tokenomics fee-lane {label} must be exact typed data"
                )


def _require_candidate_bindings(
    candidate: ZDEXTokenomicsFeeLaneReceiptCandidateV1,
    governed: GovernedZDEXFeeAllocationProfileV1,
) -> None:
    fields = governed._fields
    occurrence = candidate.occurrence
    lane = candidate.lane_candidate
    allocation = lane.allocation
    journal = allocation.occurrence
    context = lane.context
    verified = candidate.verified_allocation
    journal_bytes = canonical_global_bytes_v1(journal)
    # Route admission owns the occurrence's global pre-root. This boundary
    # binds the complete lane roots through the recomputed lane journal.
    if (
        occurrence.profile_root != fields.profile.profile_id
        or occurrence.command_kind != PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1
        or occurrence.route_release_id != fields.allocation_route.route_release_id
        or occurrence.occurrence_id != journal.command_occurrence_id
        or context.chain_id != occurrence.chain_id
        or context.deployment_root != occurrence.deployment_root
        or context.profile_root != fields.profile.profile_id
        or context.writer_epoch != fields.profile.authority_epoch
        or context.coordinator_release_id
        != fields.coordinator_release.coordinator_release_id
        or context.allocation_route_release_id
        != fields.allocation_route.route_release_id
        or context.authorized_buyback_route_release_id
        != fields.buyback_route.route_release_id
        or context.tokenomics_module_release_id != fields.module_release.release_id
        or context.command_occurrence_id != occurrence.occurrence_id
        or context.policy_root != fields.policy_binding.policy_root
        or lane.policy.policy_root != fields.policy_binding.policy_root
        or lane.module_journal.module_release_id != fields.module_release.release_id
        or verified.allocation_route_release_id
        != fields.allocation_route.route_release_id
        or verified.authorized_buyback_route_release_id
        != fields.buyback_route.route_release_id
        or verified.module_release_id != fields.module_release.release_id
        or verified.command_occurrence_id != occurrence.occurrence_id
        or verified.profile_root != fields.profile.profile_id
        or verified.writer_epoch != fields.profile.authority_epoch
        or verified.journal_root != journal.occurrence_root
        or verified.journal_digest
        != "0x" + hashlib.sha256(journal_bytes).hexdigest()
        or verified.effect_plan_root != allocation.effects.effect_plan_root
        or verified.expected_image_id != fields.module_release.guest_image_id
        or verified.receipt_kind is not ReceiptKindV1.SUCCINCT
        or verified.policy_root != fields.policy_binding.policy_root
        or verified.fee_asset_id != journal.fee_asset_id
        or verified.fee_ingress_atoms != allocation.pre_state.fee_ingress_atoms
        or verified.buyback_quote_atoms != journal.buyback_quote_atoms
        or verified.pre_lane_root != journal.pre_lane_root
        or verified.post_lane_root != journal.post_lane_root
    ):
        raise ValueError("ZDEX tokenomics governed fee-lane candidate mismatch")


def verify_zdex_tokenomics_fee_lane_receipt_v1(
    candidate: ZDEXTokenomicsFeeLaneReceiptCandidateV1,
    governed: GovernedZDEXFeeAllocationProfileV1,
    receipt_verifier: ZDEXLaneSuccinctReceiptVerifierV1,
) -> VerifiedZDEXTokenomicsLaneV1:
    """Verify one policy-selected leaf and its exact complete-lane receipt."""

    if type(candidate) is not ZDEXTokenomicsFeeLaneReceiptCandidateV1:
        raise TypeError("ZDEX tokenomics fee-lane receipt candidate must be exact")
    candidate.__post_init__()
    owned_governed = _revalidate_governed_fee_profile(governed)
    witness_fields = candidate.verified_allocation._fields
    if type(witness_fields) is not _VerifiedZDEXFeeAllocationFieldsV1:
        raise TypeError(
            "ZDEX tokenomics fee-allocation witness fields must be exact typed data"
        )
    _require_exact_dataclass_scalars_v1(
        witness_fields,
        name="ZDEX tokenomics fee-allocation witness",
    )
    owned_candidate = replace(
        candidate,
        occurrence=_snapshot_occurrence_v1(candidate.occurrence),
        lane_candidate=_snapshot_zdex_tokenomics_fee_lane_candidate_v1(
            candidate.lane_candidate
        ),
    )
    _require_candidate_bindings(owned_candidate, owned_governed)
    recomputed = compose_zdex_tokenomics_fee_allocation_lane_v1(
        owned_candidate.lane_candidate
    )
    if type(recomputed) is not ZDEXTokenomicsLaneCompositionAcceptedV1:
        raise ValueError("ZDEX tokenomics fee-lane composition rejected")
    fields = owned_governed._fields
    journal = recomputed.lane_journal
    return _verify_and_build_zdex_tokenomics_lane_v1(
        owned_candidate.receipt,
        journal,
        _ZDEXTokenomicsCoordinatorReceiptExpectationV1(
            fields.allocation_route,
            fields.coordinator_release,
        ),
        _ZDEXTokenomicsLaneBindingV1(
            fields.profile.profile_id,
            fields.allocation_route.route_release_id,
            fields.module_release.release_id,
            owned_candidate.occurrence.occurrence_id,
            fields.profile.authority_epoch,
            owned_candidate.lane_candidate.module_journal.journal_root,
            fields.module_release.guest_image_id,
        ),
        receipt_verifier,
    )


__all__ = [
    "ZDEXTokenomicsFeeLaneReceiptCandidateV1",
    "verify_zdex_tokenomics_fee_lane_receipt_v1",
]
