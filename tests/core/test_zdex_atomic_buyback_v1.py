"""End-to-end and adversarial evidence for same-occurrence ZDEX buy-and-burn."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_effect_projector_v1 import (
    project_single_occurrence_global_effects_v1,
)
from src.core.global_economic_proof_v1 import ReceiptKindV1, RouteCompositionJournalV1
from src.core.global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementCandidateV1,
    refine_route_global_economic_state_effects_v1,
)
from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicEffectKindV1,
    EconomicPolicyRegistryV1,
    GlobalEconomicEffectPlanV1,
    ReleaseStatusV1,
)
from src.core.zdex_atomic_buyback_v1 import (
    ZDEXAtomicBuybackAcceptedV1,
    ZDEXAtomicBuybackCandidateV1,
    ZDEXAtomicBuybackPendingV1,
    ZDEXAtomicBuybackRejectCodeV1,
    ZDEXAtomicBuybackRejectedV1,
    finalize_zdex_atomic_buyback_v1,
    prepare_zdex_atomic_buyback_v1,
    zdex_atomic_buyback_lane_coordination_obligation_root_v1,
)
from src.core.zdex_buyback_price_safety_v1 import (
    ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1,
)
from src.core.zdex_hyperdeflation_types_v1 import ZDEXHyperdeflationPolicyV1
from src.core.zdex_purchase_burn_effects_v1 import (
    burn_effects_v1,
    purchase_effects_v1,
    purchase_effects_v2,
)
from src.core.zdex_purchase_burn_receipt_verification_v1 import (
    GovernedVerifiedZDEXAMMPurchaseV2,
    ZDEXBurnReceiptCandidateV1,
    ZDEXLaneReceiptEnvelopeV1,
    ZDEXPurchaseReceiptCandidateV1,
    ZDEXPurchaseReceiptCandidateV2,
    verify_governed_zdex_amm_purchase_receipt_shadow_v2,
    verify_governed_zdex_burn_receipt_shadow_v1,
    verify_zdex_amm_purchase_receipt_v2,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    ZDEXAMMPurchaseJournalV1,
    ZDEXAMMPurchaseJournalV2,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)
from src.core.zdex_verified_buyback_spend_v1 import (
    VerifiedZDEXBuybackSpendV1,
    transition_verified_zdex_buyback_spend_shadow_v1,
)
from tests.core.test_zdex_buyback_spot_safety_receipt_v1 import (
    _Fixture,
    _fixture,
    _price_occurrence,
    _verify,
)


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
    purchase = _purchase_journal_v2(fixture, _purchase_journal(fixture, spend))
    effects = purchase_effects_v2(purchase)
    verified_purchase = verify_governed_zdex_amm_purchase_receipt_shadow_v2(
        ZDEXPurchaseReceiptCandidateV2(
            route_release=fixture.route,
            module_release=fixture.spot_release,
            occurrence=fixture.candidate.occurrence,
            pre_state=fixture.candidate.global_pre_state,
            execution_policy=fixture.candidate.buyback_policy,
            price_policy=fixture.candidate.price_policy,
            price_occurrence=_price_occurrence(fixture),
            journal=purchase,
            effects=effects,
            receipt=ZDEXLaneReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"purchase-v2-receipt",
            ),
        ),
        profile=fixture.candidate.profile,
        policy_registry=fixture.candidate.policy_registry,
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


def _purchase_journal_v2(
    fixture: _Fixture,
    purchase: ZDEXAMMPurchaseJournalV1,
) -> ZDEXAMMPurchaseJournalV2:
    safety = fixture.candidate.journal
    draft = ZDEXAMMPurchaseJournalV2(
        **{
            field_name: getattr(purchase, field_name)
            for field_name in purchase.__dataclass_fields__
        },
        buyback_execution_policy_root=fixture.candidate.buyback_policy.policy_root,
        price_safety_policy_root=fixture.candidate.price_policy.policy_root,
        oracle_occurrence_root=safety.oracle_occurrence_root,
        oracle_observed_height=safety.oracle_observed_height,
        oracle_quote_numerator_atoms=safety.oracle_quote_numerator_atoms,
        oracle_zdex_denominator_atoms=safety.oracle_zdex_denominator_atoms,
        route_safe_quote_limit_atoms=safety.route_safe_quote_limit_atoms,
        minimum_output_atoms=safety.minimum_output_atoms,
    )
    effects = purchase_effects_v2(draft)
    return replace(draft, effect_plan_root=effects.effect_plan_root)


def test_v2_purchase_receipt_binds_exact_price_authority_before_callback() -> None:
    # Arrange
    fixture, candidate = _candidate()

    # Act
    verified = candidate.verified_purchase

    # Assert
    assert verified.price_authority_root != ZERO_ROOT_V1
    assert verified.price_safety_policy_root == fixture.candidate.price_policy.policy_root
    assert verified.authority_head_root == fixture.authority_head.authority_root
    assert verified.verifier_binding_root == fixture.receipt_verifier.binding_root
    assert verified.policy_registry_root == fixture.candidate.policy_registry.registry_root
    assert verified.leaf_binding_root == verified.verified_leaf.binding_root
    assert verified.binding_root != verified.leaf_binding_root
    assert verified.verified_leaf.authority_head_root == ZERO_ROOT_V1
    assert verified.verified_leaf.verifier_binding_root == ZERO_ROOT_V1
    assert verified.leaf_binding_root == (
        "0x4c28917c9a832f1402e19a18575ad6c2d1b689adcb99f598978d2138b10e0466"
    )


def test_governed_v2_purchase_witness_cannot_be_caller_constructed() -> None:
    with pytest.raises(TypeError, match="verifier-constructed"):
        GovernedVerifiedZDEXAMMPurchaseV2(object(), object())


def test_governed_v2_purchase_rejects_substituted_execution_policy_before_callback() -> (
    None
):
    # Arrange
    fixture, candidate = _candidate()
    substituted_policy = replace(
        fixture.candidate.buyback_policy,
        pool_definition_root="0x" + "ab" * 32,
    )
    journal = replace(
        candidate.purchase_journal,
        buyback_execution_policy_root=substituted_policy.policy_root,
    )
    effects = purchase_effects_v2(journal)
    calls_before = len(fixture.backend.calls)

    # Act / Assert
    with pytest.raises(ValueError, match="execution policy binding mismatch"):
        verify_governed_zdex_amm_purchase_receipt_shadow_v2(
            ZDEXPurchaseReceiptCandidateV2(
                route_release=fixture.route,
                module_release=fixture.spot_release,
                occurrence=fixture.candidate.occurrence,
                pre_state=fixture.candidate.global_pre_state,
                execution_policy=substituted_policy,
                price_policy=fixture.candidate.price_policy,
                price_occurrence=_price_occurrence(fixture),
                journal=journal,
                effects=effects,
                receipt=ZDEXLaneReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"substituted-execution-policy",
                ),
            ),
            profile=fixture.candidate.profile,
            policy_registry=fixture.candidate.policy_registry,
            authority_head=fixture.authority_head,
            receipt_verifier=fixture.receipt_verifier,
        )
    assert len(fixture.backend.calls) == calls_before


def test_governed_v2_purchase_rejects_profile_mismatched_registry_before_callback() -> (
    None
):
    # Arrange
    fixture, candidate = _candidate()
    journal = candidate.purchase_journal
    effects = purchase_effects_v2(journal)
    first, *remaining = fixture.candidate.policy_registry.bindings
    mismatched_registry = EconomicPolicyRegistryV1(
        tuple(
            sorted(
                (replace(first, policy_root="0x" + "ac" * 32), *remaining),
                key=lambda binding: (binding.policy_kind, binding.command_kind),
            )
        )
    )
    calls_before = len(fixture.backend.calls)

    # Act / Assert
    with pytest.raises(ValueError, match="economic policy registry mismatch"):
        verify_governed_zdex_amm_purchase_receipt_shadow_v2(
            ZDEXPurchaseReceiptCandidateV2(
                route_release=fixture.route,
                module_release=fixture.spot_release,
                occurrence=fixture.candidate.occurrence,
                pre_state=fixture.candidate.global_pre_state,
                execution_policy=fixture.candidate.buyback_policy,
                price_policy=fixture.candidate.price_policy,
                price_occurrence=_price_occurrence(fixture),
                journal=journal,
                effects=effects,
                receipt=ZDEXLaneReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"mismatched-policy-registry",
                ),
            ),
            profile=fixture.candidate.profile,
            policy_registry=mismatched_registry,
            authority_head=fixture.authority_head,
            receipt_verifier=fixture.receipt_verifier,
        )
    assert len(fixture.backend.calls) == calls_before


def test_governed_v2_purchase_rejects_substituted_price_policy_before_callback() -> (
    None
):
    # Arrange
    fixture, candidate = _candidate()
    journal = candidate.purchase_journal
    effects = purchase_effects_v2(journal)
    assert any(
        binding.policy_kind == ZDEX_BUYBACK_PRICE_SAFETY_POLICY_KIND_V1
        for binding in fixture.candidate.policy_registry.bindings
    )
    substituted_price_policy = replace(
        fixture.candidate.price_policy,
        maximum_oracle_age_blocks=2,
    )
    calls_before = len(fixture.backend.calls)

    # Act / Assert
    with pytest.raises(ValueError, match="price policy binding mismatch"):
        verify_governed_zdex_amm_purchase_receipt_shadow_v2(
            ZDEXPurchaseReceiptCandidateV2(
                route_release=fixture.route,
                module_release=fixture.spot_release,
                occurrence=fixture.candidate.occurrence,
                pre_state=fixture.candidate.global_pre_state,
                execution_policy=fixture.candidate.buyback_policy,
                price_policy=substituted_price_policy,
                price_occurrence=_price_occurrence(fixture),
                journal=journal,
                effects=effects,
                receipt=ZDEXLaneReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"unregistered-price-policy",
                ),
            ),
            profile=fixture.candidate.profile,
            policy_registry=fixture.candidate.policy_registry,
            authority_head=fixture.authority_head,
            receipt_verifier=fixture.receipt_verifier,
        )
    assert len(fixture.backend.calls) == calls_before


def test_v2_purchase_policy_root_mutant_rejects_before_callback() -> None:
    # Arrange
    fixture, candidate = _candidate()
    journal = candidate.purchase_journal
    journal = replace(journal, price_safety_policy_root="0x" + "aa" * 32)
    effects = purchase_effects_v2(journal)
    calls_before = len(fixture.backend.calls)

    # Act / Assert
    with pytest.raises(ValueError, match="journal or effects"):
        verify_zdex_amm_purchase_receipt_v2(
            ZDEXPurchaseReceiptCandidateV2(
                route_release=fixture.route,
                module_release=fixture.spot_release,
                occurrence=fixture.candidate.occurrence,
                pre_state=fixture.candidate.global_pre_state,
                execution_policy=fixture.candidate.buyback_policy,
                price_policy=fixture.candidate.price_policy,
                price_occurrence=_price_occurrence(fixture),
                journal=journal,
                effects=effects,
                receipt=ZDEXLaneReceiptEnvelopeV1(
                    ReceiptKindV1.SUCCINCT,
                    b"purchase-v2-mutant",
                ),
            ),
            fixture.backend,
        )
    assert len(fixture.backend.calls) == calls_before


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


def test_bdd_fee_allocation_purchase_and_burn_retains_lane_coordination_obligation() -> (
    None
):
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
    assert accepted.terminal_obligations_root == (
        zdex_atomic_buyback_lane_coordination_obligation_root_v1(
            accepted.post_state,
            accepted.effects,
            accepted.burn,
        )
    )
    assert accepted.terminal_obligations_root != ZERO_ROOT_V1
    assert accepted.burn.journal.burned_zdex_atoms == 111
    assert (
        sum(
            -row.delta_atoms
            for row in accepted.effects.rows
            if row.kind is EconomicEffectKindV1.BURN
        )
        == 111
    )


def test_zero_terminal_root_cannot_be_forged_before_lane_coordination() -> None:
    fixture, candidate = _candidate()
    pending = prepare_zdex_atomic_buyback_v1(candidate)
    assert isinstance(pending, ZDEXAtomicBuybackPendingV1)
    accepted = finalize_zdex_atomic_buyback_v1(pending, _verify_burn(fixture, pending))
    assert isinstance(accepted, ZDEXAtomicBuybackAcceptedV1)

    with pytest.raises(TypeError, match="verifier-constructed"):
        ZDEXAtomicBuybackAcceptedV1(object(), object())  # type: ignore[arg-type]


def test_direct_accepted_construction_cannot_hide_empty_effects_or_missing_receipt() -> None:
    fixture, candidate = _candidate()
    pending = prepare_zdex_atomic_buyback_v1(candidate)
    assert isinstance(pending, ZDEXAtomicBuybackPendingV1)

    with pytest.raises(TypeError):
        ZDEXAtomicBuybackAcceptedV1(
            post_state=pending.post_state,
            effects=GlobalEconomicEffectPlanV1.empty(),
            burn=pending.burn,
            terminal_obligations_root=zdex_atomic_buyback_lane_coordination_obligation_root_v1(
                pending.post_state,
                GlobalEconomicEffectPlanV1.empty(),
                pending.burn,
            ),
        )

    verified_burn = _verify_burn(fixture, pending)
    accepted = finalize_zdex_atomic_buyback_v1(pending, verified_burn)
    assert isinstance(accepted, ZDEXAtomicBuybackAcceptedV1)
    assert accepted.verified_burn_binding_root == verified_burn.binding_root
    assert accepted.pending_binding_root != ZERO_ROOT_V1


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
        terminal_obligations_root=accepted.terminal_obligations_root,
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
    assert route_journal.terminal_obligations_root != ZERO_ROOT_V1
    assert {row.asset: row.amount_atoms for row in post_state.supplies}[
        candidate.purchase_journal.zdex_asset_id
    ] == 889
    quote_pool_rows = tuple(
        row
        for row in post_state.custody
        if row.asset == candidate.purchase_journal.quote_asset_id
        and row.custody_domain == AMM_POOL_CUSTODY_DOMAIN_V1
    )
    assert tuple((row.owner, row.amount_atoms) for row in quote_pool_rows) == (
        (candidate.purchase_journal.quote_pool_bucket_id, 1_125),
    )


def test_purchase_amount_substitution_rejects_as_exact_noop() -> None:
    _, candidate = _candidate()
    substituted = replace(
        candidate.purchase_journal,
        purchased_zdex_atoms=110,
        zdex_pool_post_atoms=890,
        burn_bucket_post_atoms=110,
    )
    result = prepare_zdex_atomic_buyback_v1(replace(candidate, purchase_journal=substituted))
    assert isinstance(result, ZDEXAtomicBuybackRejectedV1)
    assert result.code is ZDEXAtomicBuybackRejectCodeV1.PURCHASE_MISMATCH
    assert result.pre_state is result.post_state
    assert result.effects.is_empty


def test_substituted_pool_principal_rejects_as_exact_noop() -> None:
    _, candidate = _candidate()
    substituted = replace(
        candidate.purchase_journal,
        quote_pool_bucket_id="0x" + "ab" * 32,
    )
    substituted_effects = purchase_effects_v2(substituted)

    result = prepare_zdex_atomic_buyback_v1(
        replace(
            candidate,
            purchase_journal=substituted,
            purchase_effects=substituted_effects,
        )
    )

    assert isinstance(result, ZDEXAtomicBuybackRejectedV1)
    assert result.code is ZDEXAtomicBuybackRejectCodeV1.PURCHASE_MISMATCH
    assert result.pre_state is result.post_state
    assert result.effects.is_empty


def test_verify_only_route_status_rejects_as_exact_noop() -> None:
    _, candidate = _candidate()
    substituted_route = replace(candidate.route, status=ReleaseStatusV1.VERIFY_ONLY)

    result = prepare_zdex_atomic_buyback_v1(
        replace(candidate, route=substituted_route)
    )

    assert isinstance(result, ZDEXAtomicBuybackRejectedV1)
    assert result.code is ZDEXAtomicBuybackRejectCodeV1.ROUTE_MISMATCH
    assert result.pre_state is result.post_state
    assert result.effects.is_empty


def test_nonempty_consumed_objects_reject_as_exact_noop() -> None:
    _, candidate = _candidate()
    substituted_occurrence = replace(
        candidate.occurrence,
        consumed_object_ids=("legacy-budget",),
    )

    result = prepare_zdex_atomic_buyback_v1(
        replace(candidate, occurrence=substituted_occurrence)
    )

    assert isinstance(result, ZDEXAtomicBuybackRejectedV1)
    assert result.code is ZDEXAtomicBuybackRejectCodeV1.ROUTE_MISMATCH
    assert result.pre_state is result.post_state
    assert result.effects.is_empty


def test_legacy_caller_selected_purchase_witness_cannot_enter_atomic_route() -> None:
    from src.core.zdex_purchase_burn_receipt_verification_v1 import (
        verify_zdex_amm_purchase_receipt_v1,
    )

    fixture, candidate = _candidate()
    legacy_journal = _purchase_journal(fixture, candidate.verified_spend)
    legacy_effects = purchase_effects_v1(legacy_journal)
    legacy = verify_zdex_amm_purchase_receipt_v1(
        ZDEXPurchaseReceiptCandidateV1(
            fixture.route,
            fixture.spot_release,
            fixture.candidate.occurrence,
            legacy_journal,
            legacy_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"legacy"),
        ),
        fixture.backend,
    )
    with pytest.raises(TypeError, match="exact typed data"):
        replace(candidate, verified_purchase=legacy)


def test_different_current_authority_generation_cannot_mix_with_safety_witness() -> None:
    fixture, candidate = _candidate()
    other_head = replace(fixture.authority_head, generation=1)
    other_purchase = verify_governed_zdex_amm_purchase_receipt_shadow_v2(
        ZDEXPurchaseReceiptCandidateV2(
            route_release=fixture.route,
            module_release=fixture.spot_release,
            occurrence=fixture.candidate.occurrence,
            pre_state=fixture.candidate.global_pre_state,
            execution_policy=fixture.candidate.buyback_policy,
            price_policy=fixture.candidate.price_policy,
            price_occurrence=_price_occurrence(fixture),
            journal=candidate.purchase_journal,
            effects=candidate.purchase_effects,
            receipt=ZDEXLaneReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"other-generation",
            ),
        ),
        profile=fixture.candidate.profile,
        policy_registry=fixture.candidate.policy_registry,
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
