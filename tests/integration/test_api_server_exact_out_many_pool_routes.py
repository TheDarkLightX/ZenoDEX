from __future__ import annotations

from typing import Any

from src.integration.api_server_exact_out_many_pool_routes import (
    maybe_handle_exact_out_many_pool_contract_route,
)


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _minimal_request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "asset_in": "A",
        "asset_out": "B",
        "amount_out_total": 6,
        "max_legs": 3,
        "max_candidate_pools": 3,
        "max_enumerated_candidates": 2_000,
    }
    request.update(overrides)
    return request


def test_unknown_many_pool_contract_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_out_many_pool_contract_route(
        path="/api/dex/quote_exact_out_many_pool",
        obj=_minimal_request(),
        parse_pools=lambda: {},
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_many_pool_contract_route_rejects_bool_integer_field_after_pool_parse() -> None:
    writes, write_json = _capture()
    parse_called = False

    def parse_pools() -> dict[str, object]:
        nonlocal parse_called
        parse_called = True
        return {"pool_a": object()}

    handled = maybe_handle_exact_out_many_pool_contract_route(
        path="/api/dex/build_exact_out_many_pool_candidate_domain_contract",
        obj=_minimal_request(max_legs=True),
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is True
    assert writes == [(400, {"ok": False, "error": "bad_max_legs"})]


def test_many_pool_contract_route_preserves_pool_parse_error_precedence() -> None:
    writes, write_json = _capture()

    def parse_pools() -> dict[str, object]:
        raise ValueError("bad pools")

    handled = maybe_handle_exact_out_many_pool_contract_route(
        path="/api/dex/build_exact_out_many_pool_candidate_domain_contract",
        obj=_minimal_request(max_legs=True),
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "build_exact_out_many_pool_candidate_domain_contract_error",
                "details": "request failed",
            },
        )
    ]
