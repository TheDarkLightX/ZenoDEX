from __future__ import annotations

import pytest

from src.core.perp_clearinghouse_phase import clearinghouse_position_update_allowed


@pytest.mark.parametrize(
    ("now_epoch", "clearing_price_epoch", "oracle_last_update_epoch", "allowed"),
    [
        (0, 0, 0, True),
        (1, 0, 0, True),
        (1, 1, 0, False),
        (1, 1, 1, True),
        (2, 1, 1, True),
    ],
)
def test_position_update_phase_table(
    now_epoch: int,
    clearing_price_epoch: int,
    oracle_last_update_epoch: int,
    allowed: bool,
) -> None:
    state = {
        "now_epoch": now_epoch,
        "clearing_price_epoch": clearing_price_epoch,
        "oracle_last_update_epoch": oracle_last_update_epoch,
    }
    assert clearinghouse_position_update_allowed(state) is allowed


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("now_epoch", True),
        ("clearing_price_epoch", "1"),
        ("oracle_last_update_epoch", -1),
    ],
)
def test_position_update_phase_rejects_malformed_markers(
    field: str,
    value: object,
) -> None:
    state: dict[str, object] = {
        "now_epoch": 1,
        "clearing_price_epoch": 1,
        "oracle_last_update_epoch": 0,
    }
    state[field] = value

    with pytest.raises((TypeError, ValueError)):
        clearinghouse_position_update_allowed(state)


@pytest.mark.parametrize(
    "state",
    [
        {"now_epoch": 1, "clearing_price_epoch": 2, "oracle_last_update_epoch": 0},
        {"now_epoch": 1, "clearing_price_epoch": 1, "oracle_last_update_epoch": 2},
        {"now_epoch": 2, "clearing_price_epoch": 1, "oracle_last_update_epoch": 2},
    ],
)
def test_position_update_phase_rejects_inconsistent_epoch_order(
    state: dict[str, object],
) -> None:
    with pytest.raises(ValueError):
        clearinghouse_position_update_allowed(state)
