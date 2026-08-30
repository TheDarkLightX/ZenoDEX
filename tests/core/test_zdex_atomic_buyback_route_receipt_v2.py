"""Authenticated receipt evidence for the SHADOW buyback route composer."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_economic_proof_v1 import ReceiptKindV1
from src.core.global_settlement_types_v1 import canonical_global_bytes_v1
from src.core.zdex_atomic_buyback_route_composition_v2 import (
    ZDEXAtomicBuybackRouteAcceptedV2,
    compose_zdex_atomic_buyback_route_shadow_v2,
)
from src.core.zdex_atomic_buyback_route_receipt_v2 import (
    VerifiedZDEXAtomicBuybackRouteV2,
    ZDEXAtomicBuybackRouteReceiptCandidateV2,
    _route_statement_v2,
    snapshot_verified_zdex_atomic_buyback_route_v2,
    verify_zdex_atomic_buyback_route_receipt_shadow_v2,
)
from src.core.zdex_purchase_burn_receipt_verification_v1 import (
    ZDEXLaneReceiptEnvelopeV1,
)
from tests.core.test_zdex_atomic_buyback_route_composition_v2 import (
    _verified_route_candidate,
)


def _accepted_route():
    fixture, candidate = _verified_route_candidate()
    accepted = compose_zdex_atomic_buyback_route_shadow_v2(candidate)
    assert type(accepted) is ZDEXAtomicBuybackRouteAcceptedV2
    return fixture, accepted


def test_profile_selected_route_receipt_binds_exact_journal_bytes() -> None:
    # Arrange
    fixture, accepted = _accepted_route()

    # Act
    verified = verify_zdex_atomic_buyback_route_receipt_shadow_v2(
        ZDEXAtomicBuybackRouteReceiptCandidateV2(
            fixture.profile,
            accepted,
            ZDEXLaneReceiptEnvelopeV1(
                ReceiptKindV1.SUCCINCT,
                b"route-composer-receipt",
            ),
        ),
        authority_head=fixture.authority_head,
        receipt_verifier=fixture.receipt_verifier,
    )

    # Assert
    assert fixture.backend.calls[-1] == (
        b"route-composer-receipt",
        fixture.route.guest_image_id,
        canonical_global_bytes_v1(_route_statement_v2(accepted)),
    )
    assert verified.profile_root == fixture.profile.profile_id
    assert verified.route_release_id == fixture.route.route_release_id
    assert verified.command_occurrence_id == fixture.occurrence.occurrence_id
    assert verified.pre_state_root == fixture.global_pre_state.state_root
    assert verified.post_state_root == accepted.post_state.state_root
    assert verified.authority_head_root == fixture.authority_head.authority_root
    assert verified.verifier_binding_root == fixture.receipt_verifier.binding_root
    assert snapshot_verified_zdex_atomic_buyback_route_v2(verified) == accepted


@pytest.mark.parametrize(
    ("field_name", "replacement"),
    (
        ("ordered_leaf_binding_roots", ("0x" + "a" * 64, "0x" + "b" * 64)),
        ("ordered_lane_assumption_roots", ("0x" + "c" * 64, "0x" + "d" * 64)),
        ("ordered_lane_binding_roots", ("0x" + "e" * 64, "0x" + "f" * 64)),
        ("state_delta_root", "0x" + "1" * 64),
        ("fee_disposition_root", "0x" + "2" * 64),
    ),
)
def test_route_receipt_statement_commits_every_authority_bearing_root(
    field_name: str,
    replacement: object,
) -> None:
    # Arrange
    _, accepted = _accepted_route()
    baseline = canonical_global_bytes_v1(_route_statement_v2(accepted))

    # Act
    mutated = replace(accepted, **{field_name: replacement})
    changed = canonical_global_bytes_v1(_route_statement_v2(mutated))

    # Assert
    assert changed != baseline


@pytest.mark.parametrize(
    "receipt_kind",
    (
        ReceiptKindV1.COMPOSITE,
        ReceiptKindV1.CONDITIONAL,
        ReceiptKindV1.FAKE,
        ReceiptKindV1.DEVELOPMENT,
    ),
)
def test_non_succinct_route_receipt_rejects_before_backend(
    receipt_kind: ReceiptKindV1,
) -> None:
    # Arrange
    fixture, accepted = _accepted_route()
    calls_before = len(fixture.backend.calls)

    # Act / Assert
    with pytest.raises(ValueError, match="succinct receipt"):
        verify_zdex_atomic_buyback_route_receipt_shadow_v2(
            ZDEXAtomicBuybackRouteReceiptCandidateV2(
                fixture.profile,
                accepted,
                ZDEXLaneReceiptEnvelopeV1(receipt_kind, b"invalid"),
            ),
            authority_head=fixture.authority_head,
            receipt_verifier=fixture.receipt_verifier,
        )
    assert len(fixture.backend.calls) == calls_before


def test_object_new_cannot_forge_route_receipt_authority() -> None:
    # Arrange
    forged = object.__new__(VerifiedZDEXAtomicBuybackRouteV2)

    # Act / Assert
    with pytest.raises(TypeError, match="not registered"):
        _ = forged.binding_root
