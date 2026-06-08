from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_exact_out_audit_routes import (
    maybe_handle_exact_out_audit_route,
)


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _parse_two_pools() -> dict[str, object]:
    return {"pool_b": object(), "pool_a": object()}


def _parse_three_pools() -> dict[str, object]:
    return {"pool_b": object(), "pool_a": object(), "pool_c": object()}


class _FakeAudit:
    def __init__(self, schema: str = "fake-audit") -> None:
        self.schema = schema

    def to_dict(self) -> dict[str, object]:
        return {"schema": self.schema, "runtime_matches_canonical": True}


def _fail_on_exact_out_certificate_import(monkeypatch: Any) -> None:
    real_import = builtins.__import__

    def guarded_import(
        name: str,
        globals: Any = None,
        locals: Any = None,
        fromlist: Any = (),
        level: int = 0,
    ) -> object:
        if name == "src.integration.exact_out_route_certificate":
            raise AssertionError("audit module imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def _audit_request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "asset_in": "A",
        "asset_out": "B",
        "amount_out_total": 5,
    }
    request.update(overrides)
    return request


def test_unknown_exact_out_audit_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_unknown",
        obj={},
        parse_pools=_parse_two_pools,
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_two_pool_audit_parse_failure_uses_legacy_generic_error() -> None:
    writes, write_json = _capture()

    def parse_pools() -> dict[str, object]:
        raise ValueError("pool parse detail must not leak")

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_two_pool_canonicality",
        obj=_audit_request(),
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "audit_exact_out_two_pool_canonicality_error",
                "details": "request failed",
            },
        )
    ]


def test_two_pool_audit_rejects_wrong_pool_count_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_out_certificate_import(monkeypatch)

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_two_pool_canonicality",
        obj=_audit_request(),
        parse_pools=lambda: {"only_pool": object()},
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "expected_exactly_two_pools"})]


def test_two_pool_audit_rejects_bad_assets_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_out_certificate_import(monkeypatch)

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_two_pool_canonicality",
        obj=_audit_request(asset_out="A"),
        parse_pools=_parse_two_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_assets"})]


def test_two_pool_audit_rejects_bool_amount_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_out_certificate_import(monkeypatch)

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_two_pool_canonicality",
        obj=_audit_request(amount_out_total=True),
        parse_pools=_parse_two_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_amount_out_total"})]


def test_two_pool_audit_success_payload_and_argument_order(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}

    def audit(pool0: object, pool1: object, **kwargs: object) -> _FakeAudit:
        captured["pool0"] = pool0
        captured["pool1"] = pool1
        captured["kwargs"] = dict(kwargs)
        return _FakeAudit("two-pool-audit")

    monkeypatch.setattr(
        "src.integration.exact_out_route_certificate.audit_exact_out_two_pool_runtime_canonicality",
        audit,
    )
    pools_by_id = _parse_two_pools()

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_two_pool_canonicality",
        obj=_audit_request(brute_force_max=9),
        parse_pools=lambda: pools_by_id,
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "pool0": pools_by_id["pool_b"],
        "pool1": pools_by_id["pool_a"],
        "kwargs": {
            "asset_in": "A",
            "asset_out": "B",
            "amount_out_total": 5,
            "brute_force_max": 9,
        },
    }
    assert writes == [
        (
            200,
            {
                "ok": True,
                "audit": {"schema": "two-pool-audit", "runtime_matches_canonical": True},
            },
        )
    ]


def test_many_pool_audit_parse_failure_uses_legacy_generic_error() -> None:
    writes, write_json = _capture()

    def parse_pools() -> dict[str, object]:
        raise ValueError("pool parse detail must not leak")

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_many_pool_canonicality",
        obj=_audit_request(),
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "audit_exact_out_many_pool_canonicality_error",
                "details": "request failed",
            },
        )
    ]


def test_many_pool_audit_rejects_bad_assets_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_out_certificate_import(monkeypatch)

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_many_pool_canonicality",
        obj=_audit_request(asset_in=""),
        parse_pools=_parse_three_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_assets"})]


def test_many_pool_audit_rejects_bad_integer_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_out_certificate_import(monkeypatch)

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_many_pool_canonicality",
        obj=_audit_request(max_enumerated_candidates=0),
        parse_pools=_parse_three_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_max_enumerated_candidates"})]


def test_many_pool_audit_rejects_bool_integer_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    _fail_on_exact_out_certificate_import(monkeypatch)

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_many_pool_canonicality",
        obj=_audit_request(window=True),
        parse_pools=_parse_three_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_window"})]


def test_many_pool_audit_success_payload_defaults_and_pool_order(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    captured: dict[str, object] = {}

    def audit(pools: list[object], **kwargs: object) -> _FakeAudit:
        captured["pools"] = list(pools)
        captured["kwargs"] = dict(kwargs)
        return _FakeAudit("many-pool-audit")

    monkeypatch.setattr(
        "src.integration.exact_out_route_certificate.audit_exact_out_many_pool_runtime_canonicality",
        audit,
    )
    pools_by_id = _parse_three_pools()

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_many_pool_canonicality",
        obj=_audit_request(max_legs=2, window=0),
        parse_pools=lambda: pools_by_id,
        write_json=write_json,
    )

    assert handled is True
    assert captured == {
        "pools": list(pools_by_id.values()),
        "kwargs": {
            "asset_in": "A",
            "asset_out": "B",
            "amount_out_total": 5,
            "max_legs": 2,
            "max_candidate_pools": 5,
            "max_candidates": 12,
            "max_iters": 4096,
            "window": 0,
            "brute_force_max": 512,
            "max_full_domain_pools": 8,
            "max_enumerated_candidates": 20_000,
        },
    }
    assert writes == [
        (
            200,
            {
                "ok": True,
                "audit": {"schema": "many-pool-audit", "runtime_matches_canonical": True},
            },
        )
    ]


def test_many_pool_audit_exception_payload(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def audit(_pools: list[object], **_kwargs: object) -> _FakeAudit:
        raise RuntimeError("internal detail must not leak")

    monkeypatch.setattr(
        "src.integration.exact_out_route_certificate.audit_exact_out_many_pool_runtime_canonicality",
        audit,
    )

    handled = maybe_handle_exact_out_audit_route(
        path="/api/dex/audit_exact_out_many_pool_canonicality",
        obj=_audit_request(),
        parse_pools=_parse_three_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [
        (
            400,
            {
                "ok": False,
                "error": "audit_exact_out_many_pool_canonicality_error",
                "details": "request failed",
            },
        )
    ]
