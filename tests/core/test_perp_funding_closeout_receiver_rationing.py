from __future__ import annotations

import pytest

from src.core.perp_funding_closeout_receiver_rationing import (
    RATIONING_SCHEMA,
    ReceiverClaimRow,
    ReceiverHaircutRationingVerdict,
    build_receiver_haircut_rationing,
    receiver_haircut_rationing_from_payload,
    receiver_haircut_rationing_to_payload,
    verify_receiver_haircut_rationing_payload,
)


def _claims() -> tuple[ReceiverClaimRow, ...]:
    return (
        ReceiverClaimRow("bb" * 48, 40_000),
        ReceiverClaimRow("aa" * 48, 60_000),
    )


def _payload(**overrides: object) -> dict[str, object]:
    rationing = build_receiver_haircut_rationing(
        _claims(),
        total_haircut_quote=30_000,
    )
    payload = receiver_haircut_rationing_to_payload(rationing)
    payload.update(overrides)
    return payload


def test_two_receiver_exact_quota_split() -> None:
    rationing = build_receiver_haircut_rationing(
        _claims(),
        total_haircut_quote=30_000,
    )

    rows = {row.account_pubkey: row for row in rationing.receiver_rows}
    assert rationing.total_claim_quote == 100_000
    assert rationing.quota_denominator_quote == 100_000
    assert rows["aa" * 48].haircut_quote == 18_000
    assert rows["aa" * 48].payable_quote == 42_000
    assert rows["bb" * 48].haircut_quote == 12_000
    assert rows["bb" * 48].payable_quote == 28_000
    assert sum(row.haircut_quote for row in rationing.receiver_rows) == 30_000
    assert sum(row.payable_quote for row in rationing.receiver_rows) == 70_000


def test_largest_remainder_assigns_leftover_unit() -> None:
    rationing = build_receiver_haircut_rationing(
        (
            ReceiverClaimRow("alice", 5),
            ReceiverClaimRow("bob", 3),
            ReceiverClaimRow("carol", 2),
        ),
        total_haircut_quote=4,
    )

    assert tuple(
        (row.account_pubkey, row.haircut_quote, row.payable_quote)
        for row in rationing.receiver_rows
    ) == (
        ("alice", 2, 3),
        ("bob", 1, 2),
        ("carol", 1, 1),
    )


def test_same_remainder_tie_breaks_by_account() -> None:
    rationing = build_receiver_haircut_rationing(
        (
            ReceiverClaimRow("carol", 1),
            ReceiverClaimRow("alice", 1),
            ReceiverClaimRow("bob", 1),
        ),
        total_haircut_quote=1,
    )

    assert tuple((row.account_pubkey, row.haircut_quote) for row in rationing.receiver_rows) == (
        ("alice", 1),
        ("bob", 0),
        ("carol", 0),
    )


def test_total_haircut_equals_total_claim_zeroes_payable() -> None:
    rationing = build_receiver_haircut_rationing(
        _claims(),
        total_haircut_quote=100_000,
    )

    assert all(row.payable_quote == 0 for row in rationing.receiver_rows)
    assert sum(row.haircut_quote for row in rationing.receiver_rows) == 100_000


def test_one_receiver_reduces_to_v2_runtime_witness() -> None:
    rationing = build_receiver_haircut_rationing(
        (ReceiverClaimRow("receiver", 100_000),),
        total_haircut_quote=30_000,
    )

    assert rationing.receiver_rows[0].haircut_quote == 30_000
    assert rationing.receiver_rows[0].payable_quote == 70_000


def test_payload_round_trips_valid_rationing() -> None:
    rationing = build_receiver_haircut_rationing(
        _claims(),
        total_haircut_quote=30_000,
    )
    payload = receiver_haircut_rationing_to_payload(rationing)

    assert verify_receiver_haircut_rationing_payload(payload) == ReceiverHaircutRationingVerdict(
        True,
        None,
    )
    assert receiver_haircut_rationing_from_payload(payload) == rationing


def test_payload_rejects_noncanonical_priority_haircut() -> None:
    payload = _payload()
    rows = list(payload["receiver_rows"])
    first = dict(rows[0])
    second = dict(rows[1])
    first["haircut_quote"] = 30_000
    first["payable_quote"] = 30_000
    second["haircut_quote"] = 0
    second["payable_quote"] = 40_000
    payload["receiver_rows"] = [first, second]

    assert verify_receiver_haircut_rationing_payload(payload) == ReceiverHaircutRationingVerdict(
        False,
        "haircut_quote is not canonical",
    )


def test_payload_rejects_payable_mismatch() -> None:
    payload = _payload()
    rows = list(payload["receiver_rows"])
    first = dict(rows[0])
    first["payable_quote"] -= 1
    rows[0] = first
    payload["receiver_rows"] = rows

    assert verify_receiver_haircut_rationing_payload(payload) == ReceiverHaircutRationingVerdict(
        False,
        "payable_quote mismatch",
    )


def test_payload_rejects_quota_floor_mutation() -> None:
    payload = _payload()
    rows = list(payload["receiver_rows"])
    first = dict(rows[0])
    first["quota_floor_quote"] += 1
    rows[0] = first
    payload["receiver_rows"] = rows

    assert verify_receiver_haircut_rationing_payload(payload) == ReceiverHaircutRationingVerdict(
        False,
        "quota_floor_quote mismatch",
    )


def test_payload_rejects_quota_remainder_mutation() -> None:
    payload = _payload()
    rows = list(payload["receiver_rows"])
    first = dict(rows[0])
    first["quota_remainder_numerator"] += 1
    rows[0] = first
    payload["receiver_rows"] = rows

    assert verify_receiver_haircut_rationing_payload(payload) == ReceiverHaircutRationingVerdict(
        False,
        "quota_remainder_numerator mismatch",
    )


def test_payload_rejects_unsorted_rows() -> None:
    payload = _payload()
    payload["receiver_rows"] = list(reversed(payload["receiver_rows"]))

    assert verify_receiver_haircut_rationing_payload(payload) == ReceiverHaircutRationingVerdict(
        False,
        "receiver_rows must be sorted by account_pubkey",
    )


def test_payload_rejects_duplicate_accounts() -> None:
    payload = _payload()
    rows = list(payload["receiver_rows"])
    duplicate = dict(rows[0])
    rows[1] = duplicate
    payload["receiver_rows"] = rows

    assert verify_receiver_haircut_rationing_payload(payload) == ReceiverHaircutRationingVerdict(
        False,
        "duplicate receiver account",
    )


def test_builder_rejects_haircut_above_total_claim() -> None:
    with pytest.raises(ValueError, match="total_haircut_quote exceeds total_claim_quote"):
        build_receiver_haircut_rationing(
            _claims(),
            total_haircut_quote=100_001,
        )


def test_builder_rejects_duplicate_claim_accounts() -> None:
    with pytest.raises(ValueError, match="duplicate receiver claim account"):
        build_receiver_haircut_rationing(
            (
                ReceiverClaimRow("alice", 10),
                ReceiverClaimRow("alice", 5),
            ),
            total_haircut_quote=3,
        )


def test_payload_rejects_bool_integer_fields() -> None:
    assert verify_receiver_haircut_rationing_payload(
        _payload(total_haircut_quote=True)
    ) == ReceiverHaircutRationingVerdict(False, "total_haircut_quote must be an int")


def test_payload_rejects_wrong_schema() -> None:
    assert verify_receiver_haircut_rationing_payload(
        _payload(schema=RATIONING_SCHEMA + ".bad")
    ) == ReceiverHaircutRationingVerdict(False, "invalid rationing schema")


def test_exact_count() -> None:
    tests = [
        name
        for name, value in globals().items()
        if name.startswith("test_") and callable(value) and name != "test_exact_count"
    ]
    assert len(tests) == 16
