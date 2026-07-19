"""Strict pre-state numeric regressions for the N-party perps matcher."""

from __future__ import annotations

import pytest

from src.nonproduction.perp_np_matching import E8, Intent, MatchParams, match_intents


def _params() -> MatchParams:
    return MatchParams(initial_margin_bps=1000, max_position_abs=1_000_000)


def _intents() -> list[Intent]:
    return [
        Intent("alice", target_base=1, nonce=1),
        Intent("bob", target_base=-1, nonce=1),
    ]


def test_match_intents_rejects_bool_current_position() -> None:
    with pytest.raises(TypeError, match=r"current_positions\[alice\]"):
        match_intents(
            _intents(),
            current_positions={"alice": True},
            collaterals={"alice": 10**12, "bob": 10**12},
            last_nonces={},
            clearing_price_e8=100 * E8,
            now_epoch=1,
            params=_params(),
        )


def test_match_intents_rejects_numeric_string_collateral() -> None:
    with pytest.raises(TypeError, match=r"collaterals\[alice\]"):
        match_intents(
            _intents(),
            current_positions={},
            collaterals={"alice": "1000000000000", "bob": 10**12},  # type: ignore[dict-item]
            last_nonces={},
            clearing_price_e8=100 * E8,
            now_epoch=1,
            params=_params(),
        )


def test_match_intents_rejects_bool_last_nonce() -> None:
    with pytest.raises(TypeError, match=r"last_nonces\[alice\]"):
        match_intents(
            _intents(),
            current_positions={},
            collaterals={"alice": 10**12, "bob": 10**12},
            last_nonces={"alice": False},
            clearing_price_e8=100 * E8,
            now_epoch=1,
            params=_params(),
        )


@pytest.mark.parametrize("field", ["clearing_price_e8", "now_epoch"])
def test_match_intents_rejects_bool_top_level_numeric_controls(field: str) -> None:
    kwargs = {
        "clearing_price_e8": 100 * E8,
        "now_epoch": 1,
    }
    kwargs[field] = True

    with pytest.raises(TypeError, match=field):
        match_intents(
            _intents(),
            current_positions={},
            collaterals={"alice": 10**12, "bob": 10**12},
            last_nonces={},
            params=_params(),
            **kwargs,
        )
