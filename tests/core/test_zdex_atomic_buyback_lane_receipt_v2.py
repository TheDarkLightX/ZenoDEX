"""Authenticated receipt evidence for the buyback lane coordinators."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import ReceiptKindV1
from src.core.global_settlement_types_v1 import LaneIdV1, canonical_global_bytes_v1
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
    _coordinator_statement_v2,
    snapshot_verified_zdex_buyback_lane_composition_v2,
    verify_zdex_buyback_lane_coordinator_receipt_shadow_v2,
)
from src.core.zdex_atomic_buyback_receipt_verification_v2 import (
    VerifiedZDEXSpotBuybackLeafV2,
    VerifiedZDEXTokenomicsBuybackLeafV2,
)
from src.core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXLaneReceiptEnvelopeV1,
)
from tests.core.test_zdex_atomic_buyback_receipt_verification_v2 import (
    _Fixture,
    _fixture,
    _verify_pair,
)


def _compositions() -> tuple[
    _Fixture,
    VerifiedZDEXSpotBuybackLeafV2,
    VerifiedZDEXTokenomicsBuybackLeafV2,
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
    return fixture, verified_spot, verified_tokenomics, spot, tokenomics


def test_profile_selected_coordinator_receipts_bind_exact_journal_bytes() -> None:
    # Arrange
    fixture, spot_leaf, tokenomics_leaf, spot, tokenomics = _compositions()

    # Act
    verified_spot = verify_zdex_buyback_lane_coordinator_receipt_shadow_v2(
        ZDEXBuybackLaneCoordinatorReceiptCandidateV2(
            fixture.profile,
            spot,
            spot_leaf,
            ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"spot-coordinator"),
        ),
        authority_head=fixture.authority_head,
        receipt_verifier=fixture.receipt_verifier,
    )
    verified_tokenomics = verify_zdex_buyback_lane_coordinator_receipt_shadow_v2(
        ZDEXBuybackLaneCoordinatorReceiptCandidateV2(
            fixture.profile,
            tokenomics,
            tokenomics_leaf,
            ZDEXLaneReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"tokenomics-coordinator",
            ),
        ),
        authority_head=fixture.authority_head,
        receipt_verifier=fixture.receipt_verifier,
    )

    # Assert
    assert verified_spot.lane_id is LaneIdV1.SPOT_LIQUIDITY
    assert verified_tokenomics.lane_id is LaneIdV1.ZDEX_TOKENOMICS
    assert verified_spot.route_occurrence_id == verified_tokenomics.route_occurrence_id
    assert verified_spot.authority_head_root == fixture.authority_head.authority_root
    assert (
        verified_tokenomics.authority_head_root
        == fixture.authority_head.authority_root
    )
    spot_release = fixture.profile.lane_coordinator_registry.release_for(
        LaneIdV1.SPOT_LIQUIDITY
    )
    tokenomics_release = fixture.profile.lane_coordinator_registry.release_for(
        LaneIdV1.ZDEX_TOKENOMICS
    )
    assert fixture.backend.calls[-2:] == [
        (
            b"spot-coordinator",
            spot_release.guest_image_id,
            canonical_global_bytes_v1(_coordinator_statement_v2(spot)),
        ),
        (
            b"tokenomics-coordinator",
            tokenomics_release.guest_image_id,
            canonical_global_bytes_v1(_coordinator_statement_v2(tokenomics)),
        ),
    ]
    assert (
        snapshot_verified_zdex_buyback_lane_composition_v2(verified_spot)
        == spot
    )
    assert (
        snapshot_verified_zdex_buyback_lane_composition_v2(verified_tokenomics)
        == tokenomics
    )


def test_non_succinct_coordinator_rejects_before_backend_callback() -> None:
    # Arrange
    fixture, spot_leaf, _, spot, _ = _compositions()
    calls_before = len(fixture.backend.calls)

    # Act / Assert
    with pytest.raises(ValueError, match="succinct receipt"):
        verify_zdex_buyback_lane_coordinator_receipt_shadow_v2(
            ZDEXBuybackLaneCoordinatorReceiptCandidateV2(
                fixture.profile,
                spot,
                spot_leaf,
                ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.FAKE, b"fake"),
            ),
            authority_head=fixture.authority_head,
            receipt_verifier=fixture.receipt_verifier,
        )
    assert len(fixture.backend.calls) == calls_before


def test_coordinator_rejects_substituted_leaf_assumption_before_backend() -> None:
    # Arrange
    fixture, spot_leaf, _, spot, _ = _compositions()
    forged = replace(spot, leaf_assumption_root="0x" + "f" * 64)
    calls_before = len(fixture.backend.calls)

    # Act / Assert
    with pytest.raises(ValueError, match="leaf lineage mismatch"):
        verify_zdex_buyback_lane_coordinator_receipt_shadow_v2(
            ZDEXBuybackLaneCoordinatorReceiptCandidateV2(
                fixture.profile,
                forged,
                spot_leaf,
                ZDEXLaneReceiptEnvelopeV1(ReceiptKindV1.SUCCINCT, b"forged"),
            ),
            authority_head=fixture.authority_head,
            receipt_verifier=fixture.receipt_verifier,
        )
    assert len(fixture.backend.calls) == calls_before


def test_object_new_cannot_forge_coordinator_receipt_authority() -> None:
    # Arrange
    forged = object.__new__(VerifiedZDEXBuybackLaneCompositionV2)

    # Act / Assert
    with pytest.raises(TypeError, match="not registered"):
        _ = forged.binding_root
