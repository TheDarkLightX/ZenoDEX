from __future__ import annotations

from typing import Any

from src.integration.exact_out_route_certificate import (
    EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA,
    EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA,
)
from src.integration.api_server_exact_out_many_pool_routes import (
    maybe_handle_exact_out_many_pool_route,
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


def _project_quote_path(payload: object) -> list[list[object]] | None:
    return None


class _FakePacket:
    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "packet-controlled-schema",
            "repaired_quote": None,
            "repaired_matches_full_canonical": False,
            "full_domain_candidate_count": 2,
            "full_domain_feasible_pool_ids": ["pool_a"],
            "full_domain_canonical_quote": {"legs": [], "amount_in_total": 0},
            "repaired_packet": {"runtime_quote": {"legs": [], "amount_in_total": 0}},
        }


class _FakeBoundedPacket:
    def to_dict(self) -> dict[str, object]:
        return {
            "schema": "packet-controlled-bounded-schema",
            "advisory_quote": None,
            "quote_source": None,
            "repaired_advisory_available": False,
            "quote_matches_runtime": False,
            "quote_matches_repaired_advisory": False,
            "workaround_packet": {
                "oracle_contract": {
                    "audit": {
                        "runtime_quote": {"legs": [], "amount_in_total": 0},
                        "projection_cover_audit": None,
                    }
                },
                "repaired_packet": {"projection_cover_audit": None},
            },
        }


def test_unknown_many_pool_contract_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/quote_exact_out_many_pool_unknown",
        obj=_minimal_request(),
        parse_pools=lambda: {},
        project_quote_path=_project_quote_path,
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

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/build_exact_out_many_pool_candidate_domain_contract",
        obj=_minimal_request(max_legs=True),
        parse_pools=parse_pools,
        project_quote_path=_project_quote_path,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is True
    assert writes == [(400, {"ok": False, "error": "bad_max_legs"})]


def test_many_pool_contract_route_preserves_pool_parse_error_precedence() -> None:
    writes, write_json = _capture()

    def parse_pools() -> dict[str, object]:
        raise ValueError("bad pools")

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/build_exact_out_many_pool_candidate_domain_contract",
        obj=_minimal_request(max_legs=True),
        parse_pools=parse_pools,
        project_quote_path=_project_quote_path,
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


def test_many_pool_quote_route_rejects_bool_integer_field_after_pool_parse() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/quote_exact_out_many_pool_repaired_selected_domain",
        obj=_minimal_request(max_iters=False),
        parse_pools=lambda: {"pool_a": object()},
        project_quote_path=_project_quote_path,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_max_iters"})]


def test_many_pool_advisory_quote_route_rejects_bool_integer_field_after_pool_parse() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/quote_exact_out_many_pool_repaired_advisory",
        obj=_minimal_request(max_candidates=True),
        parse_pools=lambda: {"pool_a": object()},
        project_quote_path=_project_quote_path,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_max_candidates"})]


def test_many_pool_full_domain_certified_route_rejects_bool_integer_field_after_pool_parse() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/quote_exact_out_many_pool_repaired_full_domain_certified",
        obj=_minimal_request(max_full_domain_pools=True),
        parse_pools=lambda: {"pool_a": object()},
        project_quote_path=_project_quote_path,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_max_full_domain_pools"})]


def test_many_pool_full_domain_certified_route_failure_payload_contract(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def quote_rejects(*_args: object, **_kwargs: object) -> tuple[None, str, _FakePacket]:
        return None, "full_domain_mismatch", _FakePacket()

    monkeypatch.setattr(
        "src.integration.exact_out_route_certificate.quote_exact_out_many_pool_repaired_full_domain_certified",
        quote_rejects,
    )

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/quote_exact_out_many_pool_repaired_full_domain_certified",
        obj=_minimal_request(),
        parse_pools=lambda: {"pool_a": object()},
        project_quote_path=_project_quote_path,
        write_json=write_json,
    )

    assert handled is True
    assert len(writes) == 1
    status, payload = writes[0]
    assert status == 200
    assert isinstance(payload, dict)
    assert payload["ok"] is False
    assert payload["packet_schema"] == EXACT_OUT_MANY_POOL_REPAIRED_FULL_DOMAIN_CERTIFIED_PACKET_SCHEMA
    assert payload["packet"]["schema"] == "packet-controlled-schema"
    assert payload["runtime_quote"] == {"legs": [], "amount_in_total": 0}
    assert payload["error"] == "full_domain_mismatch"
    assert "quote" not in payload


def test_many_pool_bounded_advisory_route_rejects_bool_integer_field_after_pool_parse() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/quote_exact_out_many_pool_bounded_advisory",
        obj=_minimal_request(brute_force_max=False),
        parse_pools=lambda: {"pool_a": object()},
        project_quote_path=_project_quote_path,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_brute_force_max"})]


def test_many_pool_bounded_advisory_route_rejects_oversized_search_cap_after_pool_parse() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/quote_exact_out_many_pool_bounded_advisory",
        obj=_minimal_request(max_enumerated_candidates=50_001),
        parse_pools=lambda: {"pool_a": object()},
        project_quote_path=_project_quote_path,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_max_enumerated_candidates"})]


def test_many_pool_bounded_advisory_route_failure_payload_contract(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def quote_rejects(*_args: object, **_kwargs: object) -> tuple[None, str, _FakeBoundedPacket]:
        return None, "bounded_unavailable", _FakeBoundedPacket()

    monkeypatch.setattr(
        "src.integration.exact_out_route_certificate.quote_exact_out_many_pool_bounded_advisory",
        quote_rejects,
    )

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/quote_exact_out_many_pool_bounded_advisory",
        obj=_minimal_request(),
        parse_pools=lambda: {"pool_a": object()},
        project_quote_path=_project_quote_path,
        write_json=write_json,
    )

    assert handled is True
    assert len(writes) == 1
    status, payload = writes[0]
    assert status == 200
    assert isinstance(payload, dict)
    assert payload["ok"] is False
    assert payload["packet_schema"] == EXACT_OUT_MANY_POOL_BOUNDED_ADVISORY_QUOTE_PACKET_SCHEMA
    assert payload["packet"]["schema"] == "packet-controlled-bounded-schema"
    assert payload["runtime_quote"] == {"legs": [], "amount_in_total": 0}
    assert payload["effective_projection_cover_side"] is None
    assert payload["error"] == "bounded_unavailable"
    assert "quote" not in payload


def test_many_pool_default_quote_route_rejects_bool_integer_field_after_pool_parse() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_out_many_pool_route(
        path="/api/dex/quote_exact_out_many_pool",
        obj=_minimal_request(max_legs=True),
        parse_pools=lambda: {"pool_a": object()},
        project_quote_path=_project_quote_path,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_max_legs"})]
