"""Pure V3 route composer for a governed same-occurrence ZDEX buy-and-burn."""

from __future__ import annotations

from .global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    AssetConservationRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
)
from .zdex_fee_allocation_v1 import FEE_BUYBACK_PRINCIPAL_V1
from .zdex_purchase_burn_contract_v2 import (
    ZDEXPurchaseBurnRouteAcceptedV2,
    ZDEXPurchaseBurnRouteCandidateV2,
    ZDEXPurchaseBurnRouteResultV2,
    _snapshot_route_candidate_v2,
)
from .zdex_purchase_burn_profile_v2 import _GovernedZDEXPurchaseBurnAnchorMismatchV2
from .zdex_purchase_burn_route_types_v1 import (
    ZDEXPurchaseBurnRouteRejectCodeV1,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)
from .zdex_purchase_burn_route_v1 import (
    ZDEXPurchaseBurnRouteRejectedV1,
    _compose_conservation,
    _compose_rows,
)
from .zdex_purchase_burn_witness_v2 import _witness_reject_code_v2
from .zdex_tokenomics_lane_v1 import (
    zdex_tokenomics_complete_lane_obligation_root_v1,
)


def _reject_v2(
    code: ZDEXPurchaseBurnRouteRejectCodeV1,
) -> ZDEXPurchaseBurnRouteRejectedV1:
    return ZDEXPurchaseBurnRouteRejectedV1(code)


def _compose_effects_v2(
    candidate: ZDEXPurchaseBurnRouteCandidateV2,
) -> GlobalEconomicEffectPlanV1:
    purchase = candidate.purchase_journal
    conservation: tuple[AssetConservationRowV1, ...] = _compose_conservation(
        purchase,
        candidate.burn_journal,
    )
    return GlobalEconomicEffectPlanV1(
        rows=_compose_rows(candidate.purchase_effects, candidate.burn_effects),
        asset_conservation=conservation,
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(
                LaneIdV1.SPOT_LIQUIDITY,
                purchase.pre_spot_lane_root,
                purchase.post_spot_lane_root,
            ),
        ),
        occurrence_consumptions=(candidate.occurrence.occurrence_id,),
        external_outbox_enqueue=(),
    )


def _governed_reject_code_v2(
    candidate: ZDEXPurchaseBurnRouteCandidateV2,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    governed = candidate.governed_profile._fields
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    if (
        candidate.route_release != governed.route_release
        or occurrence.profile_root != governed.profile.profile_id
        or occurrence.route_release_id != governed.route_release.route_release_id
        or occurrence.command_kind != governed.route_release.command_kind
        or purchase.writer_epoch != governed.profile.authority_epoch
        or purchase.spot_module_release_id != governed.purchase_module_release.release_id
        or candidate.burn_journal.tokenomics_module_release_id
        != governed.burn_module_release.release_id
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.GOVERNED_PROFILE_MISMATCH
    return None


def _basic_reject_code_v2(
    candidate: ZDEXPurchaseBurnRouteCandidateV2,
    occurrence_id: str,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    route = candidate.route_release
    occurrence = candidate.occurrence
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    budget = candidate.buyback_budget_occurrence
    if (
        route.route_release_id != occurrence.route_release_id
        or route.route_release_id != purchase.route_release_id
        or route.route_release_id != burn.route_release_id
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.ROUTE_BINDING_MISMATCH
    if purchase.command_occurrence_id != occurrence_id or burn.command_occurrence_id != occurrence_id:
        return ZDEXPurchaseBurnRouteRejectCodeV1.OCCURRENCE_MISMATCH
    if (
        purchase.profile_root != occurrence.profile_root
        or burn.profile_root != occurrence.profile_root
        or purchase.writer_epoch != burn.writer_epoch
        or purchase.chain_id != occurrence.chain_id
        or burn.chain_id != occurrence.chain_id
        or purchase.deployment_root != occurrence.deployment_root
        or burn.deployment_root != occurrence.deployment_root
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.PROFILE_OR_EPOCH_MISMATCH
    if (
        budget.chain_id != occurrence.chain_id
        or budget.deployment_root != occurrence.deployment_root
        or budget.profile_root != occurrence.profile_root
        or budget.writer_epoch != purchase.writer_epoch
        or budget.authorized_buyback_route_release_id != route.route_release_id
        or budget.tokenomics_module_release_id != burn.tokenomics_module_release_id
        or budget.command_occurrence_id == occurrence_id
        or purchase.quote_source_bucket_id != FEE_BUYBACK_PRINCIPAL_V1
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    return None


def _execution_policy_matches_v2(candidate: ZDEXPurchaseBurnRouteCandidateV2) -> bool:
    purchase = candidate.purchase_journal
    execution = candidate.governed_profile._fields.buyback_execution_policy
    return not any(
        (
            purchase.buyback_execution_policy_root != execution.policy_root,
            purchase.quote_asset_id != execution.quote_asset_id,
            purchase.zdex_asset_id != execution.zdex_asset_id,
            purchase.quote_pool_bucket_id
            != zdex_pool_reserve_principal_v1(
                pool_id=execution.pool_id,
                asset_id=execution.quote_asset_id,
            ),
            purchase.zdex_pool_bucket_id
            != zdex_pool_reserve_principal_v1(
                pool_id=execution.pool_id,
                asset_id=execution.zdex_asset_id,
            ),
            purchase.burn_bucket_id
            != zdex_occurrence_burn_port_v1(
                profile_root=candidate.occurrence.profile_root,
                route_release_id=candidate.route_release.route_release_id,
                command_occurrence_id=candidate.occurrence.occurrence_id,
            ),
        )
    )


def _economic_flow_reject_code_v2(
    candidate: ZDEXPurchaseBurnRouteCandidateV2,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    purchase = candidate.purchase_journal
    burn = candidate.burn_journal
    budget = candidate.buyback_budget_occurrence
    if purchase.zdex_asset_id != burn.zdex_asset_id:
        return ZDEXPurchaseBurnRouteRejectCodeV1.ASSET_MISMATCH
    if burn.purchase_occurrence_root != purchase.journal_root:
        return ZDEXPurchaseBurnRouteRejectCodeV1.PURCHASE_OCCURRENCE_MISMATCH
    if purchase.purchased_zdex_atoms != burn.burned_zdex_atoms:
        return ZDEXPurchaseBurnRouteRejectCodeV1.AMOUNT_MISMATCH
    if (
        purchase.burn_bucket_id != burn.burn_bucket_id
        or purchase.burn_bucket_post_atoms != burn.burn_bucket_pre_atoms
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BURN_BUCKET_MISMATCH
    if (
        purchase.buyback_budget_occurrence_root != budget.occurrence_root
        or burn.buyback_budget_occurrence_root != budget.occurrence_root
        or purchase.quote_asset_id != budget.fee_asset_id
        or purchase.quote_amount_in_atoms != burn.authorized_quote_input_atoms
        or purchase.quote_amount_in_atoms != budget.buyback_quote_atoms
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    if (
        purchase.zdex_owned_atoms != burn.zdex_owned_pre_atoms
        or purchase.zdex_supply_atoms != burn.zdex_supply_pre_atoms
        or purchase.quote_owned_atoms != purchase.quote_supply_atoms
        or purchase.zdex_owned_atoms != purchase.zdex_supply_atoms
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.CONSERVATION_HISTORY_DISCONNECTED
    return None


def _economic_reject_code_v2(
    candidate: ZDEXPurchaseBurnRouteCandidateV2,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    purchase = candidate.purchase_journal
    budget_root = candidate.buyback_budget_occurrence.occurrence_root
    expected_consumed = tuple(sorted((budget_root, purchase.oracle_occurrence_root)))
    if budget_root == candidate.occurrence.occurrence_id or (
        candidate.occurrence.consumed_object_ids != expected_consumed
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    if not _execution_policy_matches_v2(candidate):
        return ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_EXECUTION_POLICY_MISMATCH
    price_policy_root = candidate.governed_profile._fields.price_safety_policy.policy_root
    if (
        purchase.price_safety_policy_root != price_policy_root
        or candidate.verified_purchase.price_safety_policy_root != price_policy_root
        or candidate.verified_purchase.price_authority_root == ZERO_ROOT_V1
    ):
        return ZDEXPurchaseBurnRouteRejectCodeV1.PRICE_SAFETY_AUTHORITY_MISMATCH
    return _economic_flow_reject_code_v2(candidate)


def _first_reject_code_v2(
    candidate: ZDEXPurchaseBurnRouteCandidateV2,
    occurrence_id: str,
) -> ZDEXPurchaseBurnRouteRejectCodeV1 | None:
    code = _governed_reject_code_v2(candidate)
    if code is not None:
        return code
    code = _basic_reject_code_v2(candidate, occurrence_id)
    if code is not None:
        return code
    code = _witness_reject_code_v2(candidate, occurrence_id)
    if code is not None:
        return code
    return _economic_reject_code_v2(candidate)


def compose_zdex_purchase_burn_route_v2(
    candidate: ZDEXPurchaseBurnRouteCandidateV2,
) -> ZDEXPurchaseBurnRouteResultV2:
    """Compose authenticated leaves with deterministic fail-closed precedence."""

    try:
        owned = _snapshot_route_candidate_v2(candidate)
    except _GovernedZDEXPurchaseBurnAnchorMismatchV2:
        return _reject_v2(ZDEXPurchaseBurnRouteRejectCodeV1.GOVERNED_PROFILE_MISMATCH)
    occurrence_id = owned.occurrence.occurrence_id
    reject_code = _first_reject_code_v2(owned, occurrence_id)
    if reject_code is not None:
        return _reject_v2(reject_code)
    governed = owned.governed_profile._fields
    purchase = owned.purchase_journal
    burn = owned.burn_journal
    return ZDEXPurchaseBurnRouteAcceptedV2(
        route_release_id=owned.route_release.route_release_id,
        command_occurrence_id=occurrence_id,
        profile_root=owned.occurrence.profile_root,
        writer_epoch=purchase.writer_epoch,
        ordered_lane_journal_roots=(purchase.journal_root, burn.journal_root),
        ordered_verified_binding_roots=(
            owned.verified_purchase.leaf_binding_root,
            owned.verified_burn.leaf_binding_root,
        ),
        verified_budget_binding_root=owned.verified_buyback_budget.binding_root,
        buyback_execution_policy_root=governed.buyback_execution_policy.policy_root,
        price_safety_policy_root=governed.price_safety_policy.policy_root,
        price_authority_root=owned.verified_purchase.price_authority_root,
        effects=_compose_effects_v2(owned),
        terminal_obligations_root=zdex_tokenomics_complete_lane_obligation_root_v1(),
    )


__all__ = ["compose_zdex_purchase_burn_route_v2"]
