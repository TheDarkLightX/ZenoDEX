"""Strict state-boundary regressions for src/core/perp_v2/state.py."""

from __future__ import annotations

import pytest

from src.core.perp_v2.state import (
    STATE_VAR_NAMES,
    initial_state,
    state_from_dict,
    state_to_dict,
)

BOOL_STATE_FIELDS = frozenset(
    {
        "breaker_active",
        "clearing_price_seen",
        "oracle_seen",
        "liquidated_this_step",
    }
)


@pytest.mark.parametrize(
    "field",
    [name for name in STATE_VAR_NAMES if name not in BOOL_STATE_FIELDS and name != "epoch_phase"],
)
def test_state_from_dict_rejects_bool_for_integer_state_fields(field: str) -> None:
    payload = state_to_dict(initial_state())
    payload[field] = True

    with pytest.raises(TypeError, match=field):
        state_from_dict(payload)


@pytest.mark.parametrize("field", sorted(BOOL_STATE_FIELDS))
@pytest.mark.parametrize("value", (0, 1))
def test_state_from_dict_rejects_zero_one_int_for_bool_state_fields(
    field: str,
    value: int,
) -> None:
    payload = state_to_dict(initial_state())
    payload[field] = value

    with pytest.raises(TypeError, match=field):
        state_from_dict(payload)


@pytest.mark.parametrize("field", sorted(BOOL_STATE_FIELDS))
def test_state_from_dict_rejects_non_bit_int_for_bool_state_fields(field: str) -> None:
    payload = state_to_dict(initial_state())
    payload[field] = 2

    with pytest.raises(TypeError, match=field):
        state_from_dict(payload)
