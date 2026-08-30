"""End-to-end and adversarial evidence for governed buy-and-burn V3 composition."""

from __future__ import annotations

from dataclasses import dataclass, replace

import pytest

from src.core.economic_receipt_verifier_deployment_v1 import (
    BoundEconomicReceiptVerifierV1,
    bind_economic_receipt_verifier_deployment_v1,
)
from src.core.economic_receipt_verifier_registry_v1 import (
    EconomicReceiptVerifierRegistryV1,
    EconomicReceiptVerifierReleaseV1,
    EconomicReceiptVerifierSelectionPurposeV1,
)
from src.core.global_economic_authority_head_v1 import (
    GlobalEconomicAuthorityHeadV1,
    GlobalEconomicAuthorityStatusV1,
)
from src.core.global_economic_proof_v1 import (
    EconomicCommandOccurrenceV1,
    ReceiptKindV1,
)
from src.core.global_settlement_types_v1 import (
    AssetSupplyV1,
    EconomicAmountV1,
    GlobalEconomicStateV1,
    LaneIdV1,
    LaneStateRootV1,
    OracleOccurrenceStateV1,
    ReleaseStatusV1,
)
from src.core.zdex_buyback_price_safety_v1 import (
    ZDEXBuybackOraclePriceOccurrenceV1,
    ZDEXBuybackPriceSafetyPolicyV1,
)
from src.core.zdex_fee_allocation_v1 import candidate_zdex_fee_allocation_policy_v1
from src.core.zdex_purchase_burn_contract_v2 import (
    ZDEXPurchaseBurnRouteAcceptedV2,
    ZDEXPurchaseBurnRouteCandidateV2,
    ZDEXPurchaseBurnRouteCompositionJournalV3,
)
from src.core.zdex_purchase_burn_effects_v1 import (
    burn_effects_v1,
    purchase_effects_v2,
)
from src.core.zdex_purchase_burn_profile_v2 import (
    bind_zdex_purchase_burn_shadow_profile_v2,
)
from src.core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXBurnReceiptCandidateV1,
    ZDEXLaneReceiptEnvelopeV1,
    ZDEXPurchaseReceiptCandidateV2,
    verify_governed_zdex_amm_purchase_receipt_shadow_v2,
    verify_governed_zdex_burn_receipt_shadow_v1,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
    ZDEXAMMPurchaseJournalV2,
    ZDEXBuybackExecutionPolicyV1,
    ZDEXPurchaseBurnRouteRejectCodeV1,
    zdex_occurrence_burn_port_v1,
    zdex_pool_reserve_principal_v1,
)
from src.core.zdex_purchase_burn_route_v1 import ZDEXPurchaseBurnRouteRejectedV1
from src.core.zdex_purchase_burn_route_v2 import compose_zdex_purchase_burn_route_v2
from tests.core.test_zdex_buyback_spot_safety_receipt_v1 import (
    _VERIFIER_ARTIFACT,
    _VERIFIER_EVIDENCE,
    _RecordingVerifier,
    _verifier_manifest,
)
from tests.core.test_zdex_purchase_burn_route_v1 import (
    _allocation_route_release,
    _burn_journal,
    _buyback_budget,
    _governed_shadow_profile,
    _lane_release,
    _purchase_journal,
    _root,
    _route_release,
)


@dataclass(frozen=True, slots=True)
class _RouteFixtureV2:
    candidate: ZDEXPurchaseBurnRouteCandidateV2
    backend: _RecordingVerifier


def _verifier_release() -> EconomicReceiptVerifierReleaseV1:
    manifest = _verifier_manifest()
    return EconomicReceiptVerifierReleaseV1.build(
        semantic_version="3.0.6-shadow-buyback-route-v3-test",
        proof_system=manifest.proof_system,
        implementation_root=manifest.implementation_root,
        receipt_schema_root=manifest.receipt_schema_root,
        journal_schema_root=manifest.journal_schema_root,
        root_image_id=manifest.root_image_id,
        specification_root=manifest.specification_root,
        source_root=manifest.source_root,
        toolchain_root=manifest.toolchain_root,
        evidence_manifest_root=manifest.manifest_root,
        backend_protocol_root=manifest.backend_protocol_root,
        max_receipt_bytes=manifest.max_receipt_bytes,
        max_journal_bytes=manifest.max_journal_bytes,
        status=ReleaseStatusV1.SHADOW,
        accepts_new_receipts=False,
        evidence_statuses=_VERIFIER_EVIDENCE,
    )
def _authority(
    *,
    profile,
    deployment_root: str,
    verifier_registry: EconomicReceiptVerifierRegistryV1,
    verifier_release: EconomicReceiptVerifierReleaseV1,
    backend: _RecordingVerifier,
) -> tuple[GlobalEconomicAuthorityHeadV1, BoundEconomicReceiptVerifierV1]:
    manifest = _verifier_manifest()
    bound = bind_economic_receipt_verifier_deployment_v1(
        profile=profile,
        verifier_registry=verifier_registry,
        selection_purpose=EconomicReceiptVerifierSelectionPurposeV1.RESEARCH_SHADOW,
        evidence_manifest=manifest,
        measured_artifact_bytes=_VERIFIER_ARTIFACT,
        deployment_root=deployment_root,
        backend=backend,
    )
    head = GlobalEconomicAuthorityHeadV1(
        generation=0,
        activation_id=_root(9_930),
        chain_id="zenodex-shadow",
        deployment_root=deployment_root,
        epoch_store_root=_root(9_931),
        profile_root=profile.profile_id,
        writer_epoch=profile.authority_epoch,
        verifier_registry_root=verifier_registry.registry_root,
        verifier_release_id=verifier_release.release_id,
        verifier_binding_root=bound.binding_root,
        root_image_id=profile.root_image_id,
        status=GlobalEconomicAuthorityStatusV1.ACTIVE,
    )
    return head, bound


def _global_pre_state(*, profile, execution_policy, price_occurrence) -> GlobalEconomicStateV1:
    quote_pool = zdex_pool_reserve_principal_v1(
        pool_id=execution_policy.pool_id,
        asset_id=execution_policy.quote_asset_id,
    )
    zdex_pool = zdex_pool_reserve_principal_v1(
        pool_id=execution_policy.pool_id,
        asset_id=execution_policy.zdex_asset_id,
    )
    custody = tuple(
        sorted(
            (
                EconomicAmountV1(
                    quote_pool,
                    execution_policy.quote_asset_id,
                    AMM_POOL_CUSTODY_DOMAIN_V1,
                    1_000,
                ),
                EconomicAmountV1(
                    zdex_pool,
                    execution_policy.zdex_asset_id,
                    AMM_POOL_CUSTODY_DOMAIN_V1,
                    1_000,
                ),
                EconomicAmountV1(
                    "account:quote-holder",
                    execution_policy.quote_asset_id,
                    "zenoledger:account",
                    9_000,
                ),
            ),
            key=lambda row: row.key,
        )
    )
    return GlobalEconomicStateV1(
        chain_id="zenodex-shadow",
        deployment_root=_root(1),
        writer_epoch=profile.authority_epoch,
        height=76,
        profile_root=profile.profile_id,
        lane_roots=tuple(
            LaneStateRootV1(release.lane_id, release.release_id, False, _root(8_000 + i))
            for i, release in enumerate(profile.lane_registry.releases, start=1)
        ),
        custody=custody,
        supplies=tuple(
            sorted(
                (
                    AssetSupplyV1(execution_policy.quote_asset_id, 10_000),
                    AssetSupplyV1(execution_policy.zdex_asset_id, 1_000),
                ),
                key=lambda row: row.asset,
            )
        ),
        oracle_occurrences=(
            OracleOccurrenceStateV1(
                price_occurrence.oracle_id,
                price_occurrence.occurrence_root,
                price_occurrence.observed_height,
                True,
            ),
        ),
    )


def _fixture_v2(
    *,
    quote_atoms: int = 125,
    purchased_atoms: int = 111,
    minimum_output_atoms: int = 109,
    include_budget_consumption: bool = True,
    consumed_object_ids_override: tuple[str, ...] | None = None,
) -> _RouteFixtureV2:
    spot_release = _lane_release(LaneIdV1.SPOT_LIQUIDITY, 1)
    burn_release = _lane_release(LaneIdV1.ZDEX_TOKENOMICS, 2)
    execution_policy = ZDEXBuybackExecutionPolicyV1(
        pool_id=_root(602),
        pool_definition_root=_root(603),
        quote_asset_id=_root(600),
        zdex_asset_id=_root(601),
    )
    price_policy = ZDEXBuybackPriceSafetyPolicyV1(
        oracle_id="zdex-buyback-oracle",
        maximum_oracle_age_blocks=3,
        minimum_quote_reserve_atoms=500,
        minimum_zdex_reserve_atoms=500,
        maximum_pool_oracle_deviation_bps=500,
        maximum_execution_impact_bps=1_300,
        maximum_oracle_execution_deviation_bps=1_500,
        maximum_quote_reserve_spend_bps=2_000,
    )
    route = _route_release(
        spot_release,
        burn_release,
        oracle_policy_root=price_policy.policy_root,
    )
    allocation_route = _allocation_route_release(burn_release)
    fee_policy = candidate_zdex_fee_allocation_policy_v1()
    verifier_release = _verifier_release()
    verifier_registry = EconomicReceiptVerifierRegistryV1((verifier_release,))
    manifest = _verifier_manifest()
    profile, policy_registry = _governed_shadow_profile(
        spot_release=spot_release,
        tokenomics_release=burn_release,
        buyback_route=route,
        allocation_route=allocation_route,
        policy_root=fee_policy.policy_root,
        buyback_execution_policy_root=execution_policy.policy_root,
        price_safety_policy_root=price_policy.policy_root,
        verifier_registry_root=verifier_registry.registry_root,
        root_image_id=manifest.root_image_id,
    )
    price_occurrence = ZDEXBuybackOraclePriceOccurrenceV1(
        price_policy.oracle_id,
        execution_policy.quote_asset_id,
        execution_policy.zdex_asset_id,
        1,
        1,
        76,
    )
    pre_state = _global_pre_state(
        profile=profile,
        execution_policy=execution_policy,
        price_occurrence=price_occurrence,
    )
    occurrence = EconomicCommandOccurrenceV1(
        chain_id=pre_state.chain_id,
        deployment_root=pre_state.deployment_root,
        height=77,
        tx_index=2,
        op_index=1,
        command_kind=PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1,
        command_body_hash=_root(3),
        route_release_id=route.route_release_id,
        subject_id="protocol-buyback-controller",
        grant_root=_root(2),
        nonce=9,
        profile_root=profile.profile_id,
        pre_state_root=pre_state.state_root,
        consumed_object_ids=(),
    )
    legacy_purchase = _purchase_journal(
        route=route,
        spot_release=spot_release,
        occurrence=occurrence,
        buyback_pool_id=execution_policy.pool_id,
        quote_atoms=quote_atoms,
        purchased_atoms=purchased_atoms,
        quote_pool_pre_atoms=1_000,
        zdex_pool_pre_atoms=1_000,
    )
    budget, verified_budget, budget_candidate = _buyback_budget(
        profile=profile,
        policy_registry=policy_registry,
        policy=fee_policy,
        allocation_route=allocation_route,
        route=route,
        burn_release=burn_release,
        occurrence=occurrence,
        purchase=legacy_purchase,
    )
    consumed_object_ids: list[str] = []
    if consumed_object_ids_override is not None:
        consumed_object_ids.extend(consumed_object_ids_override)
    elif include_budget_consumption:
        consumed_object_ids.append(budget.occurrence_root)
    occurrence = replace(
        occurrence,
        consumed_object_ids=tuple(sorted(consumed_object_ids)),
    )
    legacy_purchase = replace(
        legacy_purchase,
        command_occurrence_id=occurrence.occurrence_id,
        buyback_budget_occurrence_root=budget.occurrence_root,
        burn_bucket_id=zdex_occurrence_burn_port_v1(
            profile_root=occurrence.profile_root,
            route_release_id=route.route_release_id,
            command_occurrence_id=occurrence.occurrence_id,
        ),
    )
    purchase = ZDEXAMMPurchaseJournalV2(
        **{
            name: getattr(legacy_purchase, name)
            for name in legacy_purchase.__dataclass_fields__
        },
        buyback_execution_policy_root=execution_policy.policy_root,
        price_safety_policy_root=price_policy.policy_root,
        oracle_occurrence_root=price_occurrence.occurrence_root,
        oracle_observed_height=price_occurrence.observed_height,
        oracle_quote_numerator_atoms=price_occurrence.quote_numerator_atoms,
        oracle_zdex_denominator_atoms=price_occurrence.zdex_denominator_atoms,
        route_safe_quote_limit_atoms=200,
        minimum_output_atoms=minimum_output_atoms,
    )
    purchase_effects = purchase_effects_v2(purchase)
    purchase = replace(purchase, effect_plan_root=purchase_effects.effect_plan_root)
    purchase_effects = purchase_effects_v2(purchase)
    backend = _RecordingVerifier()
    authority_head, receipt_verifier = _authority(
        profile=profile,
        deployment_root=pre_state.deployment_root,
        verifier_registry=verifier_registry,
        verifier_release=verifier_release,
        backend=backend,
    )
    verified_purchase = verify_governed_zdex_amm_purchase_receipt_shadow_v2(
        ZDEXPurchaseReceiptCandidateV2(
            route,
            spot_release,
            occurrence,
            pre_state,
            execution_policy,
            price_policy,
            price_occurrence,
            purchase,
            purchase_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"purchase-v3"),
        ),
        profile=profile,
        policy_registry=policy_registry,
        authority_head=authority_head,
        receipt_verifier=receipt_verifier,
    )
    burn = _burn_journal(
        route=route,
        burn_release=burn_release,
        occurrence=occurrence,
        purchase=purchase,
    )
    burn_effects = burn_effects_v1(burn)
    burn = replace(burn, effect_plan_root=burn_effects.effect_plan_root)
    burn_effects = burn_effects_v1(burn)
    verified_burn = verify_governed_zdex_burn_receipt_shadow_v1(
        ZDEXBurnReceiptCandidateV1(
            route,
            burn_release,
            occurrence,
            burn,
            burn_effects,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"burn-v3"),
        ),
        profile=profile,
        authority_head=authority_head,
        receipt_verifier=receipt_verifier,
    )
    governed = bind_zdex_purchase_burn_shadow_profile_v2(
        expected_profile_id=profile.profile_id,
        expected_authority_epoch=profile.authority_epoch,
        profile=profile,
        policy_registry=policy_registry,
        buyback_execution_policy=execution_policy,
        price_safety_policy=price_policy,
    )
    return _RouteFixtureV2(
        ZDEXPurchaseBurnRouteCandidateV2(
            governed,
            route,
            occurrence,
            budget,
            verified_budget,
            budget_candidate.policy,
            budget_candidate.pre_state,
            purchase,
            purchase_effects,
            verified_purchase,
            burn,
            burn_effects,
            verified_burn,
        ),
        backend,
    )


def test_bdd_governed_v3_route_accepts_one_same_occurrence_purchase_and_burn() -> None:
    fixture = _fixture_v2()

    result = compose_zdex_purchase_burn_route_v2(fixture.candidate)

    assert type(result) is ZDEXPurchaseBurnRouteAcceptedV2
    assert result.ordered_lane_journal_roots == (
        fixture.candidate.purchase_journal.journal_root,
        fixture.candidate.burn_journal.journal_root,
    )
    assert result.ordered_verified_binding_roots[1] == (
        fixture.candidate.verified_burn.leaf_binding_root
    )
    assert fixture.candidate.verified_burn.leaf_binding_root == (
        "0xc9f114b40b73a9e79b4f352e1c939b6685c3155595ce25a9ec9a54b6f48c6a36"
    )
    assert fixture.candidate.verified_burn.leaf_binding_root != (
        fixture.candidate.verified_burn.binding_root
    )
    assert result.price_authority_root == fixture.candidate.verified_purchase.price_authority_root
    assert result.effects.occurrence_consumptions == (
        fixture.candidate.occurrence.occurrence_id,
    )
    assert len(result.effects.lane_writes) == 1
    assert result.effects.external_outbox_enqueue == ()


def test_one_atom_purchase_and_burn_boundary_accepts_without_residue() -> None:
    fixture = _fixture_v2(
        quote_atoms=1,
        purchased_atoms=1,
        minimum_output_atoms=1,
    )

    result = compose_zdex_purchase_burn_route_v2(fixture.candidate)

    assert type(result) is ZDEXPurchaseBurnRouteAcceptedV2
    assert fixture.candidate.burn_journal.burned_zdex_atoms == 1
    assert fixture.candidate.burn_journal.burn_bucket_post_atoms == 0


@pytest.mark.parametrize(
    "consumed_object_ids",
    (
        (),
        (_root(9_901),),
        (_root(9_901), _root(9_902), _root(9_903)),
    ),
)
def test_consumed_budget_set_mutants_reject_without_effects(
    consumed_object_ids: tuple[str, ...],
) -> None:
    fixture = _fixture_v2()
    candidate = replace(
        fixture.candidate,
        occurrence=replace(
            fixture.candidate.occurrence,
            consumed_object_ids=consumed_object_ids,
        ),
    )

    result = compose_zdex_purchase_burn_route_v2(candidate)

    assert type(result) is ZDEXPurchaseBurnRouteRejectedV1
    assert result.code is ZDEXPurchaseBurnRouteRejectCodeV1.OCCURRENCE_MISMATCH
    assert result.effects.is_empty


def test_missing_budget_consumption_rejects_after_fresh_leaf_authentication() -> None:
    fixture = _fixture_v2(include_budget_consumption=False)

    result = compose_zdex_purchase_burn_route_v2(fixture.candidate)

    assert type(result) is ZDEXPurchaseBurnRouteRejectedV1
    assert result.code is ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    assert result.effects.is_empty


def test_foreign_budget_consumption_rejects_after_fresh_leaf_authentication() -> None:
    fixture = _fixture_v2(consumed_object_ids_override=(_root(9_901),))

    result = compose_zdex_purchase_burn_route_v2(fixture.candidate)

    assert type(result) is ZDEXPurchaseBurnRouteRejectedV1
    assert result.code is ZDEXPurchaseBurnRouteRejectCodeV1.BUYBACK_BUDGET_MISMATCH
    assert result.effects.is_empty


def test_profile_selected_price_policy_cannot_be_substituted() -> None:
    fixture = _fixture_v2()
    fields = fixture.candidate.governed_profile._fields
    substituted = replace(fields.price_safety_policy, maximum_oracle_age_blocks=2)

    with pytest.raises(ValueError, match="price policy binding mismatch"):
        bind_zdex_purchase_burn_shadow_profile_v2(
            expected_profile_id=fields.profile.profile_id,
            expected_authority_epoch=fields.profile.authority_epoch,
            profile=fields.profile,
            policy_registry=fields.policy_registry,
            buyback_execution_policy=fields.buyback_execution_policy,
            price_safety_policy=substituted,
        )


def test_raw_purchase_leaf_cannot_substitute_for_governed_admission() -> None:
    fixture = _fixture_v2()

    with pytest.raises(TypeError, match="exact typed data"):
        replace(
            fixture.candidate,
            verified_purchase=fixture.candidate.verified_purchase.verified_leaf,  # type: ignore[arg-type]
        )


def test_duplicate_consumed_objects_are_unrepresentable() -> None:
    fixture = _fixture_v2()
    object_id = fixture.candidate.occurrence.consumed_object_ids[0]

    with pytest.raises(ValueError, match="sorted and unique"):
        replace(
            fixture.candidate.occurrence,
            consumed_object_ids=(object_id, object_id),
        )


def test_v3_composition_journal_matches_rust_golden_vector() -> None:
    journal = ZDEXPurchaseBurnRouteCompositionJournalV3(
        route_release_id=_root(1),
        command_occurrence_id=_root(2),
        profile_root=_root(3),
        writer_epoch=4,
        ordered_lane_journal_roots=(_root(5), _root(6)),
        ordered_verified_binding_roots=(_root(7), _root(8)),
        verified_budget_binding_root=_root(9),
        buyback_execution_policy_root=_root(10),
        price_safety_policy_root=_root(11),
        price_authority_root=_root(12),
        effect_plan_root=_root(13),
        terminal_obligations_root=_root(14),
    )

    assert journal.journal_root == (
        "0x8cb4b069d009ba9d2adbcb64e549ae1d3fb0f3986c805ba0eefbc148e178a9e3"
    )
