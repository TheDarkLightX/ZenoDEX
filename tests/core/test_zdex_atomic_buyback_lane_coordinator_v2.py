"""Accounting and binding evidence for the buyback successor coordinators."""

from __future__ import annotations

from dataclasses import replace

from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicEffectKindV1,
    LaneIdV1,
)
from src.core.zdex_atomic_buyback_lane_coordinator_v2 import (
    ZDEXBuybackLaneCompositionAcceptedV2,
    ZDEXBuybackLaneCompositionRejectedV2,
    ZDEXBuybackLaneCoordinatorRejectCodeV2,
    ZDEXSpotBuybackLaneCandidateV2,
    ZDEXTokenomicsBuybackLaneCandidateV2,
    compose_zdex_spot_buyback_lane_shadow_v2,
    compose_zdex_tokenomics_buyback_lane_shadow_v2,
)
from src.core.zdex_fee_allocation_v1 import FEE_BUYBACK_PRINCIPAL_V1
from tests.core.test_zdex_atomic_buyback_receipt_verification_v2 import (
    _fixture,
    _verify_pair,
)


def _coordinated_pair() -> tuple[
    ZDEXBuybackLaneCompositionAcceptedV2,
    ZDEXBuybackLaneCompositionAcceptedV2,
]:
    fixture = _fixture()
    verified_spot, verified_tokenomics = _verify_pair(fixture)
    spot = compose_zdex_spot_buyback_lane_shadow_v2(
        ZDEXSpotBuybackLaneCandidateV2(
            fixture.profile,
            fixture.occurrence,
            verified_spot,
        )
    )
    tokenomics = compose_zdex_tokenomics_buyback_lane_shadow_v2(
        ZDEXTokenomicsBuybackLaneCandidateV2(
            fixture.profile,
            fixture.occurrence,
            verified_tokenomics,
        )
    )
    assert type(spot) is ZDEXBuybackLaneCompositionAcceptedV2
    assert type(tokenomics) is ZDEXBuybackLaneCompositionAcceptedV2
    return spot, tokenomics


def test_profile_selected_coordinators_bind_exact_leaf_journals_and_lanes() -> None:
    # Arrange / Act
    spot, tokenomics = _coordinated_pair()

    # Assert
    assert spot.lane_journal.lane_id is LaneIdV1.SPOT_LIQUIDITY
    assert tokenomics.lane_journal.lane_id is LaneIdV1.ZDEX_TOKENOMICS
    assert len(spot.lane_journal.ordered_module_journal_roots) == 1
    assert len(tokenomics.lane_journal.ordered_module_journal_roots) == 1
    assert spot.lane_journal.terminal_obligations_root != ZERO_ROOT_V1
    assert tokenomics.lane_journal.terminal_obligations_root == ZERO_ROOT_V1
    assert spot.outstanding_terminal_obligations == (
        tokenomics.discharged_terminal_obligations[0],
    )


def test_spot_pool_reserve_changes_are_materialized_as_custody() -> None:
    # Arrange / Act
    spot, _ = _coordinated_pair()

    # Assert
    assert len(spot.effects.rows) == 2
    assert all(row.kind is EconomicEffectKindV1.CUSTODY for row in spot.effects.rows)


def test_tokenomics_materializes_every_fee_allocation_as_owned_value() -> None:
    # Arrange
    _, tokenomics = _coordinated_pair()
    allocations = tuple(
        row
        for row in tokenomics.effects.rows
        if row.kind is EconomicEffectKindV1.FEE_ALLOCATION
    )
    custody = {
        (row.principal, row.asset, row.custody_domain): row.delta_atoms
        for row in tokenomics.effects.rows
        if row.kind is EconomicEffectKindV1.CUSTODY
    }

    # Act / Assert
    assert allocations
    for row in allocations:
        expected = row.delta_atoms
        if row.principal == FEE_BUYBACK_PRINCIPAL_V1:
            expected -= 125
        assert custody[(row.principal, row.asset, row.custody_domain)] == expected


def test_combined_quote_value_delta_is_zero_without_issue_or_burn() -> None:
    # Arrange
    spot, tokenomics = _coordinated_pair()
    quote_asset = tokenomics.effects.fee_conservation[0].asset
    state_bearing = {
        EconomicEffectKindV1.ACCOUNT_MOVEMENT,
        EconomicEffectKindV1.CUSTODY,
        EconomicEffectKindV1.LIABILITY,
        EconomicEffectKindV1.RESERVE,
    }

    # Act
    delta = sum(
        row.delta_atoms
        for plan in (spot.effects, tokenomics.effects)
        for row in plan.rows
        if row.asset == quote_asset and row.kind in state_bearing
    )

    # Assert
    assert delta == 0


def test_changed_occurrence_rejects_without_coordinated_effects() -> None:
    # Arrange
    fixture = _fixture()
    verified_spot, _ = _verify_pair(fixture)
    changed = replace(fixture.occurrence, nonce=fixture.occurrence.nonce + 1)

    # Act
    result = compose_zdex_spot_buyback_lane_shadow_v2(
        ZDEXSpotBuybackLaneCandidateV2(
            fixture.profile,
            changed,
            verified_spot,
        )
    )

    # Assert
    assert type(result) is ZDEXBuybackLaneCompositionRejectedV2
    assert result.code is ZDEXBuybackLaneCoordinatorRejectCodeV2.OCCURRENCE_MISMATCH
    assert result.effects.is_empty
