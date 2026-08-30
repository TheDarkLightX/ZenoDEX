"""End-to-end state and binding evidence for the SHADOW buyback route."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import ReceiptKindV1
from src.core.global_economic_state_effect_refinement_v1 import (
    GlobalEconomicStateEffectRefinementCandidateV1,
    refine_route_global_economic_state_effects_v1,
)
from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicEffectKindV1,
    LaneIdV1,
)
from src.core.zdex_atomic_buyback_lane_coordinator_v2 import (
    ZDEXBuybackLaneCompositionAcceptedV2,
    ZDEXSpotBuybackLaneCandidateV2,
    ZDEXTokenomicsBuybackLaneCandidateV2,
    compose_zdex_spot_buyback_lane_shadow_v2,
    compose_zdex_tokenomics_buyback_lane_shadow_v2,
)
from src.core.zdex_atomic_buyback_lane_receipt_v2 import (
    VerifiedZDEXBuybackLaneCompositionV2,
    ZDEXBuybackLaneCoordinatorReceiptCandidateV2,
    verify_zdex_buyback_lane_coordinator_receipt_shadow_v2,
)
from src.core.zdex_atomic_buyback_route_composition_v2 import (
    ZDEXAtomicBuybackRouteAcceptedV2,
    ZDEXAtomicBuybackRouteCandidateV2,
    ZDEXAtomicBuybackRouteRejectCodeV2,
    ZDEXAtomicBuybackRouteRejectedV2,
    compose_zdex_atomic_buyback_route_shadow_v2,
)
from src.core.zdex_fee_allocation_types_v1 import FEE_BUYBACK_PRINCIPAL_V1
from src.core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXLaneReceiptEnvelopeV1,
)
from src.core.zdex_purchase_burn_route_types_v1 import (
    AMM_POOL_CUSTODY_DOMAIN_V1,
    PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    zdex_pool_reserve_principal_v1,
)
from tests.core.test_zdex_atomic_buyback_receipt_verification_v2 import (
    _Fixture,
    _fixture,
    _verify_pair,
)


def _verified_route_candidate() -> tuple[
    _Fixture,
    ZDEXAtomicBuybackRouteCandidateV2,
]:
    fixture = _fixture()
    spot_leaf, tokenomics_leaf = _verify_pair(fixture)
    spot_composition = compose_zdex_spot_buyback_lane_shadow_v2(
        ZDEXSpotBuybackLaneCandidateV2(
            fixture.profile,
            fixture.occurrence,
            spot_leaf,
        )
    )
    tokenomics_composition = compose_zdex_tokenomics_buyback_lane_shadow_v2(
        ZDEXTokenomicsBuybackLaneCandidateV2(
            fixture.profile,
            fixture.occurrence,
            tokenomics_leaf,
        )
    )
    assert type(spot_composition) is ZDEXBuybackLaneCompositionAcceptedV2
    assert type(tokenomics_composition) is ZDEXBuybackLaneCompositionAcceptedV2
    spot_lane = verify_zdex_buyback_lane_coordinator_receipt_shadow_v2(
        ZDEXBuybackLaneCoordinatorReceiptCandidateV2(
            fixture.profile,
            spot_composition,
            spot_leaf,
            ZDEXLaneReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"spot-coordinator-route",
            ),
        ),
        authority_head=fixture.authority_head,
        receipt_verifier=fixture.receipt_verifier,
    )
    tokenomics_lane = verify_zdex_buyback_lane_coordinator_receipt_shadow_v2(
        ZDEXBuybackLaneCoordinatorReceiptCandidateV2(
            fixture.profile,
            tokenomics_composition,
            tokenomics_leaf,
            ZDEXLaneReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"tokenomics-coordinator-route",
            ),
        ),
        authority_head=fixture.authority_head,
        receipt_verifier=fixture.receipt_verifier,
    )
    return fixture, ZDEXAtomicBuybackRouteCandidateV2(
        fixture.profile,
        fixture.route,
        fixture.occurrence,
        fixture.global_pre_state,
        fixture.authority_head,
        spot_leaf,
        tokenomics_leaf,
        spot_lane,
        tokenomics_lane,
    )


def _custody_amount(
    accepted: ZDEXAtomicBuybackRouteAcceptedV2,
    principal: str,
    asset: str,
    domain: str,
) -> int:
    return next(
        (
            row.amount_atoms
            for row in accepted.post_state.custody
            if row.owner == principal
            and row.asset == asset
            and row.custody_domain == domain
        ),
        0,
    )


def test_authenticated_route_projects_one_conserved_global_state() -> None:
    # Arrange
    fixture, candidate = _verified_route_candidate()

    # Act
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)

    # Assert
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    quote_asset = fixture.tokenomics.journal.quote_asset_id
    zdex_asset = fixture.tokenomics.journal.zdex_asset_id
    pool_id = fixture.tokenomics.journal.selected_pool_id
    assert result.post_state.height == fixture.occurrence.height
    assert result.post_state.supplies[0].amount_atoms == 10_000
    assert result.post_state.supplies[1].amount_atoms == 889
    assert _custody_amount(
        result,
        FEE_BUYBACK_PRINCIPAL_V1,
        quote_asset,
        PROTOCOL_BUYBACK_CUSTODY_DOMAIN_V1,
    ) == 0
    assert _custody_amount(
        result,
        zdex_pool_reserve_principal_v1(pool_id=pool_id, asset_id=quote_asset),
        quote_asset,
        AMM_POOL_CUSTODY_DOMAIN_V1,
    ) == 1_125
    assert _custody_amount(
        result,
        zdex_pool_reserve_principal_v1(pool_id=pool_id, asset_id=zdex_asset),
        zdex_asset,
        AMM_POOL_CUSTODY_DOMAIN_V1,
    ) == 889
    assert result.effects.occurrence_consumptions == (fixture.occurrence.occurrence_id,)
    assert tuple(write.lane_id for write in result.effects.lane_writes) == (
        LaneIdV1.SPOT_LIQUIDITY,
        LaneIdV1.ZDEX_TOKENOMICS,
    )
    assert result.route_journal.terminal_obligations_root == ZERO_ROOT_V1
    assert result.state_delta_root != ZERO_ROOT_V1
    assert result.fee_disposition_root != ZERO_ROOT_V1
    assert len(result.post_state.replay_state) == 1


def test_route_closes_the_same_terminal_and_burns_every_purchased_atom() -> None:
    # Arrange
    fixture, candidate = _verified_route_candidate()

    # Act
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)

    # Assert
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2
    burned = sum(
        -row.delta_atoms
        for row in result.effects.rows
        if row.kind is EconomicEffectKindV1.BURN
    )
    assert burned == fixture.spot.journal.purchased_zdex_atoms
    assert burned == fixture.tokenomics.journal.burned_zdex_atoms
    assert result.post_state.terminal_obligations == fixture.global_pre_state.terminal_obligations


def test_generic_static_fee_mirror_stays_fail_closed_for_temporal_spend() -> None:
    # Arrange
    fixture, candidate = _verified_route_candidate()
    result = compose_zdex_atomic_buyback_route_shadow_v2(candidate)
    assert type(result) is ZDEXAtomicBuybackRouteAcceptedV2

    # Act / Assert
    with pytest.raises(ValueError, match="fee allocation is not mirrored"):
        refine_route_global_economic_state_effects_v1(
            GlobalEconomicStateEffectRefinementCandidateV1(
                fixture.global_pre_state,
                result.post_state,
                result.effects,
                (fixture.occurrence,),
                (result.route_journal,),
            )
        )


def test_changed_authority_head_rejects_as_an_exact_no_op() -> None:
    # Arrange
    fixture, candidate = _verified_route_candidate()
    changed = replace(
        candidate,
        authority_head=replace(
            fixture.authority_head,
            generation=fixture.authority_head.generation + 1,
        ),
    )

    # Act
    result = compose_zdex_atomic_buyback_route_shadow_v2(changed)

    # Assert
    assert type(result) is ZDEXAtomicBuybackRouteRejectedV2
    assert result.code is ZDEXAtomicBuybackRouteRejectCodeV2.AUTHORITY_MISMATCH
    assert result.pre_state is result.post_state
    assert result.effects.is_empty


def test_changed_occurrence_rejects_before_any_effect_projection() -> None:
    # Arrange
    _, candidate = _verified_route_candidate()
    changed = replace(
        candidate,
        occurrence=replace(candidate.occurrence, nonce=candidate.occurrence.nonce + 1),
    )

    # Act
    result = compose_zdex_atomic_buyback_route_shadow_v2(changed)

    # Assert
    assert type(result) is ZDEXAtomicBuybackRouteRejectedV2
    assert result.code is ZDEXAtomicBuybackRouteRejectCodeV2.RECEIPT_BINDING_MISMATCH
    assert result.pre_state is result.post_state
    assert result.effects.is_empty


def test_unregistered_lane_handle_cannot_supply_route_authority() -> None:
    # Arrange
    _, candidate = _verified_route_candidate()
    forged = object.__new__(VerifiedZDEXBuybackLaneCompositionV2)
    changed = replace(candidate, verified_spot_lane=forged)

    # Act / Assert
    with pytest.raises(TypeError, match="not registered"):
        compose_zdex_atomic_buyback_route_shadow_v2(changed)
