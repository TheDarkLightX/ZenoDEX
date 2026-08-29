"""Receipt-bound evidence for governed same-occurrence buyback spending."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.zdex_buyback_spend_v1 import (
    ZDEXBuybackSpendRejectCodeV1,
    ZDEXBuybackSpendRejectedV1,
)
from src.core.zdex_verified_buyback_spend_v1 import (
    VerifiedZDEXBuybackSpendV1,
    transition_verified_zdex_buyback_spend_shadow_v1,
)
from tests.core.test_zdex_buyback_spot_safety_receipt_v1 import (
    _fixture as _safety_fixture,
)
from tests.core.test_zdex_buyback_spot_safety_receipt_v1 import (
    _verify as _verify_safety,
)


def _inputs() -> tuple[object, ...]:
    fixture = _safety_fixture()
    safety = _verify_safety(fixture)
    return (fixture.candidate.occurrence, safety)


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
    assert result.tokenomics_pre_state.state_root != result.tokenomics_post_state.state_root
    assert (
        result.tokenomics_post_state.cadence_state_for(
            accepted.intent.quote_asset_id
        ).last_execution_height
        == 77
    )


def test_authenticated_purchase_amount_must_equal_selected_canonical_spend() -> None:
    values = list(_inputs())
    fixture = _safety_fixture()
    candidate = replace(
        fixture.candidate,
        journal=replace(fixture.candidate.journal, quote_amount_in_atoms=124),
    )
    values[1] = _verify_safety(fixture, candidate)

    result = _run(tuple(values))

    assert isinstance(result, ZDEXBuybackSpendRejectedV1)
    assert result.code is ZDEXBuybackSpendRejectCodeV1.VERIFIED_SAFETY_MISMATCH
    assert result.effects.is_empty
    assert result.fee_post_state is result.fee_pre_state
    assert result.cadence_post_state is result.cadence_pre_state


@pytest.mark.parametrize("field", ("nonce", "route_release_id", "pre_state_root"))
def test_foreign_occurrence_coordinates_reject_without_effect(field: str) -> None:
    values = list(_inputs())
    occurrence = values[0]
    if field == "nonce":
        values[0] = replace(occurrence, nonce=occurrence.nonce + 1)  # type: ignore[union-attr]
    else:
        values[0] = replace(occurrence, **{field: "0x" + "99" * 32})

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
