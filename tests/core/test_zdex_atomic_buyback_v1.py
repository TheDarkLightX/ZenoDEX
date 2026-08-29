"""End-to-end and adversarial evidence for same-occurrence ZDEX buy-and-burn."""

from __future__ import annotations

from dataclasses import replace

from src.core.global_economic_effect_projector_v1 import (
    project_single_occurrence_global_effects_v1,
)
from src.core.global_economic_proof_v1 import ReceiptKindV1, RouteCompositionJournalV1
from src.core.global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementCandidateV1,
    refine_route_global_economic_state_effects_v1,
)
from src.core.global_settlement_types_v1 import ZERO_ROOT_V1, EconomicEffectKindV1
from src.core.zdex_atomic_buyback_v1 import (
    ZDEXAtomicBuybackAcceptedV1,
    ZDEXAtomicBuybackCandidateV1,
    ZDEXAtomicBuybackPendingV1,
    ZDEXAtomicBuybackRejectCodeV1,
    ZDEXAtomicBuybackRejectedV1,
    finalize_zdex_atomic_buyback_v1,
    prepare_zdex_atomic_buyback_v1,
)
from src.core.zdex_hyperdeflation_types_v1 import ZDEXHyperdeflationPolicyV1
from src.core.zdex_purchase_burn_effects_v1 import (
    burn_effects_v1,
    purchase_effects_v1,
)
from src.core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXBurnReceiptCandidateV1,
    ZDEXLaneReceiptEnvelopeV1,
    ZDEXPurchaseReceiptCandidateV1,
    verify_governed_zdex_amm_purchase_receipt_shadow_v1,
    verify_governed_zdex_burn_receipt_shadow_v1,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    ZDEXAMMPurchaseJournalV1,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)
from src.core.zdex_verified_buyback_spend_v1 import (
    VerifiedZDEXBuybackSpendV1,
    transition_verified_zdex_buyback_spend_shadow_v1,
)
from tests.core.test_zdex_buyback_spot_safety_receipt_v1 import _Fixture, _fixture, _verify


def _purchase_journal(
    fixture: _Fixture, spend: VerifiedZDEXBuybackSpendV1
) -> ZDEXAMMPurchaseJournalV1:
    candidate = fixture.candidate
    safety = candidate.journal
    supply = candidate.tokenomics_pre_state.tokenomics.supply_state
    journal = ZDEXAMMPurchaseJournalV1(
        chain_id=candidate.occurrence.chain_id,
        deployment_root=candidate.occurrence.deployment_root,
        profile_root=candidate.occurrence.profile_root,
        writer_epoch=candidate.profile.authority_epoch,
        route_release_id=fixture.route.route_release_id,
        command_occurrence_id=candidate.occurrence.occurrence_id,
        spot_module_release_id=fixture.spot_release.release_id,
        issue_burn_policy_root=fixture.route.issue_burn_policy_root,
        buyback_budget_occurrence_root=spend.accepted.intent.intent_root,
        quote_asset_id=safety.quote_asset_id,
        zdex_asset_id=safety.zdex_asset_id,
        quote_source_bucket_id="protocol-fee-buyback-reserve",
        quote_pool_bucket_id=zdex_pool_reserve_principal_v1(
            pool_id=candidate.buyback_policy.pool_id,
            asset_id=safety.quote_asset_id,
        ),
        zdex_pool_bucket_id=zdex_pool_reserve_principal_v1(
            pool_id=candidate.buyback_policy.pool_id,
            asset_id=safety.zdex_asset_id,
        ),
        burn_bucket_id=zdex_occurrence_burn_port_v1(
            profile_root=candidate.occurrence.profile_root,
            route_release_id=fixture.route.route_release_id,
            command_occurrence_id=candidate.occurrence.occurrence_id,
        ),
        quote_amount_in_atoms=safety.quote_amount_in_atoms,
        purchased_zdex_atoms=safety.purchased_zdex_atoms,
        quote_source_pre_atoms=125,
        quote_source_post_atoms=0,
        quote_pool_pre_atoms=1_000,
        quote_pool_post_atoms=1_125,
        zdex_pool_pre_atoms=1_000,
        zdex_pool_post_atoms=889,
        burn_bucket_pre_atoms=0,
        burn_bucket_post_atoms=111,
        quote_owned_atoms=10_000,
        quote_supply_atoms=10_000,
        zdex_owned_atoms=supply.live_supply_atoms,
        zdex_supply_atoms=supply.live_supply_atoms,
        pre_spot_lane_root=safety.pre_spot_lane_root,
        post_spot_lane_root=safety.post_spot_lane_root,
        effect_plan_root="0x" + "99" * 32,
    )
    effects = purchase_effects_v1(journal)
    return replace(journal, effect_plan_root=effects.effect_plan_root)


def _candidate() -> tuple[_Fixture, ZDEXAtomicBuybackCandidateV1]:
    fixture = _fixture()
    safety = _verify(fixture)
    spend = transition_verified_zdex_buyback_spend_shadow_v1(
        fixture.candidate.occurrence,
        safety,
    )
    assert isinstance(spend, VerifiedZDEXBuybackSpendV1)
    purchase = _purchase_journal(fixture, spend)
    effects = purchase_effects_v1(purchase)
    verified_purchase = verify_governed_zdex_amm_purchase_receipt_shadow_v1(
        ZDEXPurchaseReceiptCandidateV1(
            fixture.route,
            fixture.spot_release,
            fixture.candidate.occurrence,
            purchase,
            effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"purchase-receipt"),
        ),
        profile=fixture.candidate.profile,
        authority_head=fixture.authority_head,
        receipt_verifier=fixture.receipt_verifier,
    )
    return fixture, ZDEXAtomicBuybackCandidateV1(
        fixture.candidate.occurrence,
        fixture.route,
        safety,
        spend,
        purchase,
        effects,
        verified_purchase,
        ZDEXHyperdeflationPolicyV1(
            safety.journal.zdex_asset_id,
            1,
            10,
            38,
            8,
        ),
    )


def _verify_burn(
    fixture: _Fixture,
    pending: ZDEXAtomicBuybackPendingV1,
):
    tokenomics_release = fixture.candidate.profile.lane_registry.release_for(
        pending.route.ordered_lanes[1]
    )
    return verify_governed_zdex_burn_receipt_shadow_v1(
        ZDEXBurnReceiptCandidateV1(
            fixture.route,
            tokenomics_release,
            fixture.candidate.occurrence,
            pending.burn.journal,
            burn_effects_v1(pending.burn.journal),
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"burn-receipt"),
        ),
        profile=fixture.candidate.profile,
        authority_head=fixture.authority_head,
        receipt_verifier=fixture.receipt_verifier,
    )


def test_bdd_fee_allocation_purchase_and_burn_close_one_atomic_obligation() -> None:
    fixture, candidate = _candidate()

    pending = prepare_zdex_atomic_buyback_v1(candidate)

    assert isinstance(pending, ZDEXAtomicBuybackPendingV1)
    assert pending.pending_terminal_obligations_root != ZERO_ROOT_V1
    assert pending.post_state.tokenomics.supply_state.live_supply_atoms == 889
    assert (
        pending.post_state.fee_state_for(candidate.purchase_journal.quote_asset_id)
        .destination_balances[0]
        .allocation_atoms
        == 0
    )
    accepted = finalize_zdex_atomic_buyback_v1(pending, _verify_burn(fixture, pending))
    assert isinstance(accepted, ZDEXAtomicBuybackAcceptedV1)
    assert accepted.terminal_obligations_root == ZERO_ROOT_V1
    assert accepted.burn.journal.burned_zdex_atoms == 111
    assert (
        sum(
            -row.delta_atoms
            for row in accepted.effects.rows
            if row.kind is EconomicEffectKindV1.BURN
        )
        == 111
    )


def test_atomic_effects_uniquely_project_and_refine_the_global_post_state() -> None:
    fixture, candidate = _candidate()
    pending = prepare_zdex_atomic_buyback_v1(candidate)
    assert isinstance(pending, ZDEXAtomicBuybackPendingV1)
    accepted = finalize_zdex_atomic_buyback_v1(pending, _verify_burn(fixture, pending))
    assert isinstance(accepted, ZDEXAtomicBuybackAcceptedV1)

    post_state = project_single_occurrence_global_effects_v1(
        fixture.candidate.global_pre_state,
        accepted.effects,
        fixture.candidate.occurrence,
    )
    route_journal = RouteCompositionJournalV1(
        chain_id=candidate.occurrence.chain_id,
        deployment_root=candidate.occurrence.deployment_root,
        profile_root=candidate.occurrence.profile_root,
        writer_epoch=fixture.candidate.profile.authority_epoch,
        route_release_id=candidate.route.route_release_id,
        command_occurrence_id=candidate.occurrence.occurrence_id,
        ordered_lane_journal_roots=(
            candidate.purchase_journal.journal_root,
            accepted.burn.journal.journal_root,
        ),
        pre_state_root=fixture.candidate.global_pre_state.state_root,
        post_state_root=post_state.state_root,
        effect_plan_root=accepted.effects.effect_plan_root,
        terminal_obligations_root=ZERO_ROOT_V1,
    )
    refinement = refine_route_global_economic_state_effects_v1(
        GlobalEconomicStateEffectRefinementCandidateV1(
            fixture.candidate.global_pre_state,
            post_state,
            accepted.effects,
            (candidate.occurrence,),
            (route_journal,),
        )
    )

    assert refinement.pre_state_root == fixture.candidate.global_pre_state.state_root
    assert refinement.post_state_root == post_state.state_root
    assert {row.asset: row.amount_atoms for row in post_state.supplies}[
        candidate.purchase_journal.zdex_asset_id
    ] == 889


def test_purchase_amount_substitution_rejects_as_exact_noop() -> None:
    _, candidate = _candidate()
    substituted = replace(
        candidate.purchase_journal,
        purchased_zdex_atoms=39,
        zdex_pool_post_atoms=961,
        burn_bucket_post_atoms=39,
    )
    result = prepare_zdex_atomic_buyback_v1(replace(candidate, purchase_journal=substituted))
    assert isinstance(result, ZDEXAtomicBuybackRejectedV1)
    assert result.code is ZDEXAtomicBuybackRejectCodeV1.PURCHASE_MISMATCH
    assert result.pre_state is result.post_state
    assert result.effects.is_empty


def test_legacy_caller_selected_purchase_witness_cannot_enter_atomic_route() -> None:
    from src.core.zdex_purchase_burn_receipt_verification_v1 import (
        verify_zdex_amm_purchase_receipt_v1,
    )

    fixture, candidate = _candidate()
    legacy = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1(
            fixture.route,
            fixture.spot_release,
            fixture.candidate.occurrence,
            candidate.purchase_journal,
            candidate.purchase_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"legacy"),
        ),
        fixture.backend,
    )
    result = prepare_zdex_atomic_buyback_v1(replace(candidate, verified_purchase=legacy))
    assert isinstance(result, ZDEXAtomicBuybackRejectedV1)
    assert result.code is ZDEXAtomicBuybackRejectCodeV1.PURCHASE_WITNESS_MISMATCH
    assert result.pre_state is result.post_state


def test_different_current_authority_generation_cannot_mix_with_safety_witness() -> None:
    fixture, candidate = _candidate()
    other_head = replace(fixture.authority_head, generation=1)
    other_purchase = verify_governed_zdex_amm_purchase_receipt_shadow_v1(
        ZDEXPurchaseReceiptCandidateV1(
            fixture.route,
            fixture.spot_release,
            fixture.candidate.occurrence,
            candidate.purchase_journal,
            candidate.purchase_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"other-generation"),
        ),
        profile=fixture.candidate.profile,
        authority_head=other_head,
        receipt_verifier=fixture.receipt_verifier,
    )

    result = prepare_zdex_atomic_buyback_v1(replace(candidate, verified_purchase=other_purchase))

    assert isinstance(result, ZDEXAtomicBuybackRejectedV1)
    assert result.code is ZDEXAtomicBuybackRejectCodeV1.PURCHASE_WITNESS_MISMATCH
    assert result.pre_state is result.post_state


def test_wrong_burn_witness_rejects_without_exposing_post_state() -> None:
    fixture, candidate = _candidate()
    pending = prepare_zdex_atomic_buyback_v1(candidate)
    assert isinstance(pending, ZDEXAtomicBuybackPendingV1)
    burn = _verify_burn(fixture, pending)
    tampered_pending = replace(pending, pending_terminal_obligations_root="0x" + "77" * 32)

    result = finalize_zdex_atomic_buyback_v1(tampered_pending, burn)

    assert isinstance(result, ZDEXAtomicBuybackRejectedV1)
    assert result.code is ZDEXAtomicBuybackRejectCodeV1.BURN_WITNESS_MISMATCH
    assert result.pre_state is result.post_state
    assert result.effects.is_empty


def test_legacy_caller_selected_burn_witness_cannot_close_obligation() -> None:
    from src.core.zdex_purchase_burn_receipt_verification_v1 import (
        verify_zdex_burn_receipt_v1,
    )

    fixture, candidate = _candidate()
    pending = prepare_zdex_atomic_buyback_v1(candidate)
    assert isinstance(pending, ZDEXAtomicBuybackPendingV1)
    tokenomics_release = fixture.candidate.profile.lane_registry.release_for(
        pending.route.ordered_lanes[1]
    )
    legacy = verify_zdex_burn_receipt_v1(
        ZDEXBurnReceiptCandidateV1(
            fixture.route,
            tokenomics_release,
            fixture.candidate.occurrence,
            pending.burn.journal,
            burn_effects_v1(pending.burn.journal),
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"legacy-burn"),
        ),
        fixture.backend,
    )

    result = finalize_zdex_atomic_buyback_v1(pending, legacy)

    assert isinstance(result, ZDEXAtomicBuybackRejectedV1)
    assert result.code is ZDEXAtomicBuybackRejectCodeV1.BURN_WITNESS_MISMATCH
    assert result.pre_state is result.post_state
    assert result.effects.is_empty
