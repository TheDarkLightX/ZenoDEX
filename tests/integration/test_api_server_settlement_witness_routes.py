from __future__ import annotations

from typing import Callable

from src.integration import api_server_settlement_witness_routes as witness_routes


def _valid_structural_request() -> dict[str, object]:
    return {
        "intents": [{}],
        "balances": [],
        "block_timestamp": 0,
        "settlement": {},
        "price_packet": {},
    }


def _capture_write_json() -> tuple[list[tuple[int, object]], Callable[[int, object], None]]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def test_settlement_witness_route_preserves_expected_validation_detail(monkeypatch) -> None:
    writes, write_json = _capture_write_json()

    def _bad_context(**_kwargs):
        raise ValueError("bad witness field")

    monkeypatch.setattr(witness_routes, "_load_request_context", _bad_context)

    handled = witness_routes.maybe_handle_settlement_witness_lifecycle_route(
        path="/api/dex/build_settlement_witness_lifecycle_packet",
        obj=_valid_structural_request(),
        write_json=write_json,
        parse_pools=lambda: {},
        parse_settlement_proof_flags_payload=lambda _obj: None,
        parse_price_history_payload=lambda _obj: (0, 0, 0),
        parse_settlement_feature_extension_inputs_payload=lambda _obj: None,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "build_settlement_witness_lifecycle_packet_error",
                "details": "bad witness field",
            },
        )
    ]


def test_settlement_witness_route_sanitizes_unexpected_internal_fault(monkeypatch) -> None:
    writes, write_json = _capture_write_json()

    def _faulting_context(**_kwargs):
        raise RuntimeError("do not leak witness route internals")

    monkeypatch.setattr(witness_routes, "_load_request_context", _faulting_context)

    handled = witness_routes.maybe_handle_settlement_witness_lifecycle_route(
        path="/api/dex/build_settlement_witness_lifecycle_packet",
        obj=_valid_structural_request(),
        write_json=write_json,
        parse_pools=lambda: {},
        parse_settlement_proof_flags_payload=lambda _obj: None,
        parse_price_history_payload=lambda _obj: (0, 0, 0),
        parse_settlement_feature_extension_inputs_payload=lambda _obj: None,
    )

    assert handled is True
    assert writes == [(500, {"ok": False, "error": "internal_error", "detail": "RuntimeError"})]
    assert "do not leak" not in str(writes)
