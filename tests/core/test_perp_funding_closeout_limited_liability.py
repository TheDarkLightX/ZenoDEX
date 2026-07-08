from __future__ import annotations

import pytest

from src.core.perp_funding_closeout_limited_liability import (
    ALLOCATION_SCHEMA,
    LimitedLiabilityAllocationVerdict,
    build_limited_liability_funding_closeout_allocation,
    limited_liability_allocation_from_payload,
    limited_liability_allocation_to_payload,
    verify_limited_liability_allocation_payload,
)


def _payload(**overrides: object) -> dict[str, object]:
    allocation = build_limited_liability_funding_closeout_allocation(
        closed_due_quote=10,
        payer_available_quote=3,
        sink_capacity_quote=4,
    )
    payload = limited_liability_allocation_to_payload(allocation)
    payload.update(overrides)
    return payload


def test_underfunded_closeout_allocates_explicit_receiver_haircut() -> None:
    allocation = build_limited_liability_funding_closeout_allocation(
        closed_due_quote=10,
        payer_available_quote=3,
        sink_capacity_quote=4,
    )

    assert allocation.payer_debit_quote == 3
    assert allocation.sink_draw_quote == 4
    assert allocation.subrogated_claim_quote == 4
    assert allocation.receiver_haircut_quote == 3
    assert allocation.paid_to_receiver_quote == 7
    assert (
        allocation.payer_debit_quote
        + allocation.sink_draw_quote
        + allocation.receiver_haircut_quote
        == allocation.closed_due_quote
    )


def test_payer_fully_covers_closed_due_without_sink_or_haircut() -> None:
    allocation = build_limited_liability_funding_closeout_allocation(
        closed_due_quote=10,
        payer_available_quote=15,
        sink_capacity_quote=4,
    )

    assert allocation.payer_debit_quote == 10
    assert allocation.sink_draw_quote == 0
    assert allocation.receiver_haircut_quote == 0
    assert allocation.paid_to_receiver_quote == 10


def test_sink_covers_residual_after_payer_collateral() -> None:
    allocation = build_limited_liability_funding_closeout_allocation(
        closed_due_quote=10,
        payer_available_quote=3,
        sink_capacity_quote=20,
    )

    assert allocation.payer_debit_quote == 3
    assert allocation.sink_draw_quote == 7
    assert allocation.subrogated_claim_quote == 7
    assert allocation.receiver_haircut_quote == 0
    assert allocation.paid_to_receiver_quote == 10


def test_payload_round_trips_valid_allocation() -> None:
    allocation = build_limited_liability_funding_closeout_allocation(
        closed_due_quote=10,
        payer_available_quote=3,
        sink_capacity_quote=4,
    )
    payload = limited_liability_allocation_to_payload(allocation)

    assert verify_limited_liability_allocation_payload(payload) == LimitedLiabilityAllocationVerdict(
        True,
        None,
    )
    assert limited_liability_allocation_from_payload(payload) == allocation


def test_payload_rejects_no_haircut_when_collateral_and_sink_are_insufficient() -> None:
    verdict = verify_limited_liability_allocation_payload(
        _payload(receiver_haircut_quote=0, paid_to_receiver_quote=7)
    )

    assert verdict == LimitedLiabilityAllocationVerdict(
        False,
        "limited-liability conservation mismatch",
    )


def test_payload_rejects_sink_overdraw() -> None:
    verdict = verify_limited_liability_allocation_payload(
        _payload(sink_draw_quote=7, subrogated_claim_quote=7, receiver_haircut_quote=0)
    )

    assert verdict == LimitedLiabilityAllocationVerdict(
        False,
        "sink_draw_quote exceeds sink_capacity_quote",
    )


def test_payload_rejects_sink_draw_without_subrogation() -> None:
    verdict = verify_limited_liability_allocation_payload(
        _payload(subrogated_claim_quote=0)
    )

    assert verdict == LimitedLiabilityAllocationVerdict(
        False,
        "sink draw must create matching subrogated claim",
    )


def test_payload_rejects_noncanonical_payer_debit() -> None:
    verdict = verify_limited_liability_allocation_payload(
        _payload(
            payer_debit_quote=2,
            sink_draw_quote=4,
            subrogated_claim_quote=4,
            receiver_haircut_quote=4,
            paid_to_receiver_quote=6,
        )
    )

    assert verdict == LimitedLiabilityAllocationVerdict(
        False,
        "payer_debit_quote is not canonical",
    )


def test_payload_rejects_noncanonical_sink_draw() -> None:
    verdict = verify_limited_liability_allocation_payload(
        _payload(
            sink_draw_quote=3,
            subrogated_claim_quote=3,
            receiver_haircut_quote=4,
            paid_to_receiver_quote=6,
        )
    )

    assert verdict == LimitedLiabilityAllocationVerdict(
        False,
        "sink_draw_quote is not canonical",
    )


def test_payload_rejects_bool_integer_fields() -> None:
    verdict = verify_limited_liability_allocation_payload(
        _payload(payer_available_quote=True)
    )

    assert verdict == LimitedLiabilityAllocationVerdict(
        False,
        "payer_available_quote must be an int",
    )


def test_payload_rejects_wrong_schema() -> None:
    verdict = verify_limited_liability_allocation_payload(
        _payload(schema=ALLOCATION_SCHEMA + ".v0")
    )

    assert verdict == LimitedLiabilityAllocationVerdict(False, "invalid allocation schema")


def test_direct_invalid_dataclass_construction_raises() -> None:
    payload = _payload(receiver_haircut_quote=0)

    with pytest.raises(ValueError, match="limited-liability conservation mismatch"):
        limited_liability_allocation_from_payload(payload)
