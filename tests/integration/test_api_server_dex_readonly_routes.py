from __future__ import annotations

from typing import Any

from src.integration.api_server_dex_readonly_routes import maybe_handle_dex_readonly_route


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def test_impact_preview_route_returns_current_payload_shape() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_dex_readonly_route(
        path="/api/dex/impact_preview",
        obj={
            "reserve_in": 10_000,
            "reserve_out": 20_000,
            "amount_in": 100,
            "fee_bps": 30,
            "pending_volume_same_direction": 50,
            "confidence_bps": 9500,
        },
        write_json=write_json,
    )

    assert handled is True
    assert len(writes) == 1
    status, payload = writes[0]
    assert status == 200
    assert isinstance(payload, dict)
    assert payload["ok"] is True
    preview = payload["preview"]
    assert set(preview) == {
        "amount_out_isolated",
        "fee_amount",
        "price_impact_bps",
        "effective_price_e8",
        "spot_price_e8",
        "amount_out_best_case",
        "amount_out_worst_case",
        "recommended_min_out",
        "pending_volume_same_direction",
        "confidence_bps",
        "pending_volume_at_confidence",
        "amount_out_at_confidence",
    }


def test_slippage_advice_route_returns_pokayoke_when_user_slippage_is_present() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_dex_readonly_route(
        path="/api/dex/slippage_advice",
        obj={
            "reserve_in": 10_000,
            "reserve_out": 20_000,
            "amount_in": 100,
            "fee_bps": 30,
            "pending_volume_same_direction": 50,
            "confidence_bps": 9500,
            "max_attacker_amount_in": 200,
            "user_slippage_bps": 100,
            "slippage_options_bps": [50, "100", "bad"],
        },
        write_json=write_json,
    )

    assert handled is True
    assert len(writes) == 1
    status, payload = writes[0]
    assert status == 200
    assert isinstance(payload, dict)
    assert payload["ok"] is True
    advice = payload["advice"]
    assert advice["pokayoke"] is not None
    assert {option["slippage_bps"] for option in advice["options"]} == {50, 100}


def test_readonly_route_reports_request_failure_without_leaking_exception_details() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_dex_readonly_route(
        path="/api/dex/impact_preview",
        obj={"reserve_in": "not-an-int"},
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {"ok": False, "error": "impact_preview_error", "details": "request failed"},
        )
    ]


def test_unknown_readonly_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_dex_readonly_route(
        path="/api/dex/pokayoke_swap_suggest",
        obj={},
        write_json=write_json,
    )

    assert handled is False
    assert writes == []
