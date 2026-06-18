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
def test_state_from_dict_normalizes_bool_state_fields_from_zero_one(field: str) -> None:
    payload = state_to_dict(initial_state())
    payload[field] = 1
    true_state = state_from_dict(payload)
    assert getattr(true_state, field) is True

    payload[field] = 0
    false_state = state_from_dict(payload)
    assert getattr(false_state, field) is False


@pytest.mark.parametrize("field", sorted(BOOL_STATE_FIELDS))
def test_state_from_dict_rejects_non_bit_int_for_bool_state_fields(field: str) -> None:
    payload = state_to_dict(initial_state())
    payload[field] = 2

    with pytest.raises(TypeError, match=field):
        state_from_dict(payload)
