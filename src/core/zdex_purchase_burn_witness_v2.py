"""Closed receipt and fee-budget checks for the V3 ZDEX buy-and-burn route."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass, replace

from .global_economic_proof_v1 import ReceiptKindV1
from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    GlobalEconomicEffectPlanV1,
    LaneModuleReleaseV1,
    canonical_global_bytes_v1,
)
from .zdex_fee_allocation_v1 import (
    ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    candidate_zdex_fee_allocation_policy_v1,
    transition_zdex_fee_allocation_v1,
)
from .zdex_purchase_burn_contract_v2 import ZDEXPurchaseBurnRouteCandidateV2
from .zdex_purchase_burn_receipt_verification_v1 import (
    VerifiedZDEXAMMPurchaseV2,
    VerifiedZDEXBurnV1,
)
from .zdex_purchase_burn_route_types_v1 import (
    ZDEXAMMPurchaseJournalV2,
    ZDEXBurnJournalV1,
    ZDEXPurchaseBurnRouteRejectCodeV1,
)


@dataclass(frozen=True, slots=True)
class _LaneWitnessExpectationV2:
    route_release_id: str
    module_release: LaneModuleReleaseV1
    occurrence_id: str
    profile_root: str
    writer_epoch: int


def _lane_witness_matches_v2(
    witness: VerifiedZDEXAMMPurchaseV2 | VerifiedZDEXBurnV1,
    expectation: _LaneWitnessExpectationV2,
    journal: ZDEXAMMPurchaseJournalV2 | ZDEXBurnJournalV1,
    effects: GlobalEconomicEffectPlanV1,
) -> bool:
    digest = "0x" + hashlib.sha256(canonical_global_bytes_v1(journal)).hexdigest()
    release = expectation.module_release
    return not any(
        (
            witness.route_release_id != expectation.route_release_id,
            witness.module_release_id != release.release_id,
            witness.expected_image_id != release.guest_image_id,
            witness.command_occurrence_id != expectation.occurrence_id,
            witness.profile_root != expectation.profile_root,
            witness.writer_epoch != expectation.writer_epoch,
            witness.journal_root != journal.journal_root,
            witness.journal_digest != digest,
            witness.effect_plan_root != effects.effect_plan_root,
            witness.receipt_kind is not ReceiptKindV1.SUCCINCT,
        )
    )


def _budget_witness_matches_v2(
    candidate: ZDEXPurchaseBurnRouteCandidateV2,
) -> bool:
    budget = candidate.buyback_budget_occurrence
    witness = candidate.verified_buyback_budget
    governed = candidate.governed_profile._fields
    digest = "0x" + hashlib.sha256(canonical_global_bytes_v1(budget)).hexdigest()
    return not any(
        (
            witness.authorized_buyback_route_release_id
            != candidate.route_release.route_release_id,
            witness.allocation_route_release_id != budget.allocation_route_release_id,
            witness.module_release_id != governed.burn_module_release.release_id,
            witness.expected_image_id != governed.burn_module_release.guest_image_id,
            witness.command_occurrence_id != budget.command_occurrence_id,
            witness.profile_root != candidate.occurrence.profile_root,
            witness.writer_epoch != candidate.purchase_journal.writer_epoch,
            witness.journal_root != budget.occurrence_root,
            witness.journal_digest != digest,
            witness.effect_plan_root != budget.effect_plan_root,
            witness.policy_root != budget.policy_root,
            witness.fee_asset_id != budget.fee_asset_id,
            witness.fee_ingress_atoms != budget.fee_charged_atoms,
            witness.buyback_quote_atoms != budget.buyback_quote_atoms,
            witness.pre_lane_root != budget.pre_lane_root,
            witness.post_lane_root != budget.post_lane_root,
            witness.receipt_kind is not ReceiptKindV1.SUCCINCT,
        )
    )


def _budget_recomputes_v2(candidate: ZDEXPurchaseBurnRouteCandidateV2) -> bool:
    budget = candidate.buyback_budget_occurrence
    policy = candidate.buyback_budget_policy
    if policy != candidate_zdex_fee_allocation_policy_v1():
        return False
    context = ZDEXFeeAllocationContextV1(
        chain_id=budget.chain_id,
        deployment_root=budget.deployment_root,
        profile_root=budget.profile_root,
        writer_epoch=budget.writer_epoch,
        allocation_route_release_id=budget.allocation_route_release_id,
        authorized_buyback_route_release_id=budget.authorized_buyback_route_release_id,
        tokenomics_module_release_id=budget.tokenomics_module_release_id,
        command_occurrence_id=budget.command_occurrence_id,
        policy_root=budget.policy_root,
    )
    recomputed = transition_zdex_fee_allocation_v1(
        context,
        candidate.buyback_budget_pre_state,
        policy,
        ZDEXFeeAllocationCommandV1(budget.fee_charged_atoms),
    )
    return type(recomputed) is ZDEXFeeAllocationAcceptedV1 and (
        recomputed.occurrence == budget
    )


def _witness_reject_code_v2(
    candidate: ZDEXPurchaseBurnRouteCandidateV2,
    occurrence_id: str,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    governed = candidate.governed_profile._fields
    admitted = candidate.verified_purchase
    purchase_expected = _LaneWitnessExpectationV2(
        candidate.route_release.route_release_id,
        governed.purchase_module_release,
        occurrence_id,
        candidate.occurrence.profile_root,
        candidate.purchase_journal.writer_epoch,
    )
    if (
        admitted.authority_head_root == ZERO_ROOT_V1
        or admitted.verifier_binding_root == ZERO_ROOT_V1
        or admitted.policy_registry_root != governed.policy_registry.registry_root
        or not _lane_witness_matches_v2(
            admitted.verified_leaf,
            purchase_expected,
            candidate.purchase_journal,
            candidate.purchase_effects,
        )
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_WITNESS_MISMATCH
    burn = candidate.verified_burn
    burn_expected = replace(
        purchase_expected,
        module_release=governed.burn_module_release,
        writer_epoch=candidate.burn_journal.writer_epoch,
    )
    if (
        burn.authority_head_root != admitted.authority_head_root
        or burn.verifier_binding_root != admitted.verifier_binding_root
        or burn.authority_head_root == ZERO_ROOT_V1
        or not _lane_witness_matches_v2(
            burn,
            burn_expected,
            candidate.burn_journal,
            candidate.burn_effects,
        )
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BURN_WITNESS_MISMATCH
    if not _budget_witness_matches_v2(candidate) or not _budget_recomputes_v2(candidate):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    return None


__all__: list[str] = []
