"""Receipt-bound evidence for governed same-occurrence buyback spending."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v1 import LaneIdV1
from src.core.zdex_buyback_spend_v1 import (
    ZDEXBuybackSpendPolicyV1,
    ZDEXBuybackSpendRejectCodeV1,
    ZDEXBuybackSpendRejectedV1,
    ZDEXBuybackSpendStateV1,
)
from src.core.zdex_buyback_spot_safety_receipt_v1 import (
    verify_zdex_buyback_spot_safety_receipt_shadow_v1,
)
from src.core.zdex_fee_allocation_types_v1 import (
    ZDEX_FEE_DESTINATIONS_V1,
    ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1,
    ZDEXFeeDestinationAmountV1,
    ZDEXFeeDestinationV1,
    ZDEXFeeStateV1,
    candidate_zdex_fee_allocation_policy_v1,
)
from src.core.zdex_verified_buyback_spend_v1 import (
    VerifiedZDEXBuybackSpendV1,
    transition_verified_zdex_buyback_spend_shadow_v1,
)
from tests.core.test_zdex_buyback_spot_safety_receipt_v1 import (
    _fixture as _safety_fixture,
)
from tests.core.test_zdex_buyback_spot_safety_receipt_v1 import (
    _RecordingVerifier,
)


def _inputs() -> tuple[object, ...]:
    fixture = _safety_fixture()
    safety = verify_zdex_buyback_spot_safety_receipt_shadow_v1(
        fixture.candidate,
        _RecordingVerifier(),
    )
    journal = safety.journal
    fee_policy = candidate_zdex_fee_allocation_policy_v1()
    spend_policy = ZDEXBuybackSpendPolicyV1(
        journal.quote_asset_id,
        1,
        journal.route_safe_quote_limit_atoms,
        1,
    )
    cadence = ZDEXBuybackSpendStateV1(
        journal.quote_asset_id,
        spend_policy.policy_root,
        None,
    )
    destination_balances = tuple(
        ZDEXFeeDestinationAmountV1(
            destination,
            100 if destination is ZDEXFeeDestinationV1.BUYBACK else 0,
        )
        for destination in ZDEX_FEE_DESTINATIONS_V1
    )
    fee_state = ZDEXFeeStateV1(
        journal.quote_asset_id,
        fee_policy.policy_root,
        125,
        0,
        destination_balances,
        10_000,
        10_000,
    )
    occurrence = fixture.candidate.occurrence
    tokenomics_release = fixture.candidate.profile.lane_registry.release_for(
        LaneIdV1.ZDEX_TOKENOMICS
    )
    fee_context = ZDEXFeeAllocationContextV1(
        occurrence.chain_id,
        occurrence.deployment_root,
        occurrence.profile_root,
        journal.writer_epoch,
        occurrence.route_release_id,
        occurrence.route_release_id,
        tokenomics_release.release_id,
        occurrence.occurrence_id,
        fee_policy.policy_root,
    )
    return (
        spend_policy,
        cadence,
        fee_policy,
        fee_state,
        fee_context,
        ZDEXFeeAllocationCommandV1(125),
        occurrence,
        safety,
    )


def _run(values: tuple[object, ...]) -> object:
    return transition_verified_zdex_buyback_spend_shadow_v1(*values)  # type: ignore[arg-type]


def test_authenticated_safety_receipt_supplies_height_limit_and_exact_spend() -> None:
    result = _run(_inputs())

    assert isinstance(result, VerifiedZDEXBuybackSpendV1)
    accepted = result.accepted
    assert accepted.context.current_height == 77
    assert accepted.context.route_safe_quote_limit_atoms == 200
    assert accepted.intent.quote_spend_atoms == 125
    assert accepted.intent.safety_limit_binding_root == result.safety_receipt_binding_root
    assert accepted.fee_post_state.destination_balances[0].allocation_atoms == 0


def test_authenticated_purchase_amount_must_equal_selected_canonical_spend() -> None:
    values = list(_inputs())
    fixture = _safety_fixture()
    candidate = replace(
        fixture.candidate,
        journal=replace(fixture.candidate.journal, quote_amount_in_atoms=124),
    )
    values[7] = verify_zdex_buyback_spot_safety_receipt_shadow_v1(
        candidate,
        _RecordingVerifier(),
    )

    result = _run(tuple(values))

    assert isinstance(result, ZDEXBuybackSpendRejectedV1)
    assert result.code is ZDEXBuybackSpendRejectCodeV1.VERIFIED_SAFETY_MISMATCH
    assert result.effects.is_empty
    assert result.fee_post_state is result.fee_pre_state
    assert result.cadence_post_state is result.cadence_pre_state


@pytest.mark.parametrize("field", ("nonce", "route_release_id", "pre_state_root"))
def test_foreign_occurrence_coordinates_reject_without_effect(field: str) -> None:
    values = list(_inputs())
    occurrence = values[6]
    if field == "nonce":
        values[6] = replace(occurrence, nonce=occurrence.nonce + 1)  # type: ignore[union-attr]
    else:
        values[6] = replace(occurrence, **{field: "0x" + "99" * 32})

    result = _run(tuple(values))

    assert isinstance(result, ZDEXBuybackSpendRejectedV1)
    assert result.code is ZDEXBuybackSpendRejectCodeV1.VERIFIED_SAFETY_MISMATCH
    assert result.effects.is_empty


def test_foreign_fee_chain_or_writer_epoch_rejects_without_effect() -> None:
    for replacement in ({"chain_id": "foreign-chain"}, {"writer_epoch": 12}):
        values = list(_inputs())
        values[4] = replace(values[4], **replacement)

        result = _run(tuple(values))

        assert isinstance(result, ZDEXBuybackSpendRejectedV1)
        assert result.code is ZDEXBuybackSpendRejectCodeV1.VERIFIED_SAFETY_MISMATCH
        assert result.effects.is_empty


def test_verified_spend_witness_cannot_be_constructed_or_rebound_by_callers() -> None:
    with pytest.raises(TypeError, match="adapter-constructed"):
        VerifiedZDEXBuybackSpendV1(object(), object())  # type: ignore[arg-type]

    result = _run(_inputs())
    assert isinstance(result, VerifiedZDEXBuybackSpendV1)
    with pytest.raises(AttributeError, match="immutable"):
        result._fields = object()  # type: ignore[misc]
