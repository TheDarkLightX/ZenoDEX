from __future__ import annotations

from src.integration.api_server_dex_dispatch import DexRequestContext
from src.integration.dex_dispatch_slippage_handlers import (
    _handle_pokayoke_swap_suggest,
    _handle_pokayoke_swap_suggest_heavy,
    _handle_slippage_advice,
)


def _ctx() -> DexRequestContext:
    return DexRequestContext(server=object(), cors_origin=None, raw_body=None)


def test_slippage_advice_handler_rejects_bool_amount() -> None:
    status, body = _handle_slippage_advice(
        {"reserve_in": 1_000, "reserve_out": 1_000, "amount_in": True},
        _ctx(),
    )

    assert status == 400
    assert body == {"ok": False, "error": "slippage_advice_error", "details": "request failed"}


def test_pokayoke_suggest_handler_rejects_bool_amount() -> None:
    status, body = _handle_pokayoke_swap_suggest(
        {"reserve_in": 1_000, "reserve_out": 1_000, "amount_in": True},
        _ctx(),
    )

    assert status == 400
    assert body == {"ok": False, "error": "pokayoke_swap_suggest_error", "details": "request failed"}


def test_pokayoke_heavy_handler_rejects_bool_numeric_fields() -> None:
    status, body = _handle_pokayoke_swap_suggest_heavy(
        {
            "reserve_in": 1_000,
            "reserve_out": 1_000,
            "amount_in": 100,
            "user_slippage_bps": True,
        },
        _ctx(),
    )

    assert status == 400
    assert body == {
        "ok": False,
        "error": "pokayoke_swap_suggest_heavy_error",
        "details": "request failed",
    }
