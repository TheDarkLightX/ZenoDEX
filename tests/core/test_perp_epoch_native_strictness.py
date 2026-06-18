"""Strict native wrapper parsing regressions for perp_epoch.py."""

from __future__ import annotations

from src.core.perp_epoch import (
    perp_epoch_isolated_v3_native_apply,
    perp_epoch_isolated_v3_native_initial_state,
)


def _initial_state() -> dict:
    return perp_epoch_isolated_v3_native_initial_state()


def test_native_apply_rejects_numeric_string_action_param() -> None:
    result = perp_epoch_isolated_v3_native_apply(
        state=_initial_state(),
        action="advance_epoch",
        params={"delta": "1"},
    )

    assert result.ok is False
    assert result.code == "ParamType"
    assert result.error == "delta must be an int"


def test_native_apply_rejects_bool_action_param() -> None:
    result = perp_epoch_isolated_v3_native_apply(
        state=_initial_state(),
        action="advance_epoch",
        params={"delta": True},
    )

    assert result.ok is False
    assert result.code == "ParamType"
    assert result.error == "delta must be an int"


def test_native_apply_rejects_integer_auth_param() -> None:
    result = perp_epoch_isolated_v3_native_apply(
        state=_initial_state(),
        action="deposit_collateral",
        params={"amount": 10, "auth_ok": 1},
    )

    assert result.ok is False
    assert result.code == "ParamType"
    assert result.error == "auth_ok must be a bool"
