from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_quote_routes import maybe_handle_quote_route


class _Server:
    pass


class _Quote:
    def __init__(self, label: str) -> None:
        self.label = label


class _FastRouter:
    def __init__(
        self,
        *,
        exact_in: object | None = None,
        exact_out: object | None = None,
        raise_exact_in: bool = False,
        raise_exact_out: bool = False,
    ) -> None:
        self.exact_in = exact_in
        self.exact_out = exact_out
        self.raise_exact_in = raise_exact_in
        self.raise_exact_out = raise_exact_out
        self.calls: list[tuple[str, dict[str, object]]] = []

    def quote_exact_in_2hop_fast_v1(self, **kwargs: object) -> object | None:
        self.calls.append(("exact_in", dict(kwargs)))
        if self.raise_exact_in:
            raise RuntimeError("fast exact-in failed")
        return self.exact_in

    def quote_exact_out_2hop_fast_v1(self, **kwargs: object) -> object | None:
        self.calls.append(("exact_out", dict(kwargs)))
        if self.raise_exact_out:
            raise RuntimeError("fast exact-out failed")
        return self.exact_out


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _parse_pools() -> dict[str, object]:
    return {"pool_a": object(), "pool_b": object()}


def _quote_to_dict(quote: object) -> dict[str, object]:
    return {"quote": getattr(quote, "label", "unknown")}


def _request(**overrides: object) -> dict[str, object]:
    request: dict[str, object] = {
        "kind": "exact_in",
        "asset_in": "A",
        "asset_out": "B",
        "amount_in": 10,
    }
    request.update(overrides)
    return request


def _fail_on_quote_imports(monkeypatch: Any) -> None:
    real_import = builtins.__import__

    def guarded_import(
        name: str,
        globals: Any = None,
        locals: Any = None,
        fromlist: Any = (),
        level: int = 0,
    ) -> object:
        if name in {
            "src.core.quote_receipts",
            "src.core.routing",
            "src.integration.fast_quote_router_v1",
        }:
            raise AssertionError("quote dependency imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def _install_receipt(monkeypatch: Any, calls: list[dict[str, object]]) -> None:
    def make_route_quote_receipt(**kwargs: object) -> dict[str, object]:
        calls.append(dict(kwargs))
        return {"receipt_hash": "fake-receipt", "quote_epoch": kwargs.get("quote_epoch")}

    monkeypatch.setattr(
        "src.core.quote_receipts.make_route_quote_receipt",
        make_route_quote_receipt,
    )


def test_unknown_quote_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_quote_route(
        path="/api/dex/not_quote",
        obj={},
        server=_Server(),
        parse_pools=_parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_quote_rejects_bad_kind_before_parse_or_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    parse_called = False
    _fail_on_quote_imports(monkeypatch)

    def parse_pools() -> dict[str, object]:
        nonlocal parse_called
        parse_called = True
        return {}

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(kind="unknown"),
        server=_Server(),
        parse_pools=parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is False
    assert writes == [(400, {"ok": False, "error": "bad_kind"})]


def test_quote_rejects_bad_routing_mode_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    parse_called = False
    _fail_on_quote_imports(monkeypatch)

    def parse_pools() -> dict[str, object]:
        nonlocal parse_called
        parse_called = True
        return {}

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(routing_mode="approx"),
        server=_Server(),
        parse_pools=parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is False
    assert writes == [(400, {"ok": False, "error": "bad_routing_mode"})]


def test_quote_rejects_bad_assets_before_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    parse_called = False
    _fail_on_quote_imports(monkeypatch)

    def parse_pools() -> dict[str, object]:
        nonlocal parse_called
        parse_called = True
        return {}

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(asset_out="A"),
        server=_Server(),
        parse_pools=parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is False
    assert writes == [(400, {"ok": False, "error": "bad_assets"})]


def test_quote_maps_pool_parse_error_to_bad_pools() -> None:
    writes, write_json = _capture()

    def parse_pools() -> dict[str, object]:
        raise ValueError("pools must be a non-empty list")

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(),
        server=_Server(),
        parse_pools=parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_pools", "details": "request failed"})]


def test_quote_exact_in_success_payload_and_receipt_args(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    routing_calls: list[dict[str, object]] = []
    receipt_calls: list[dict[str, object]] = []
    quote = _Quote("exact-in")

    def best_route_exact_in_2hop(**kwargs: object) -> object:
        routing_calls.append(dict(kwargs))
        return quote

    monkeypatch.setattr("src.core.routing.best_route_exact_in_2hop", best_route_exact_in_2hop)
    _install_receipt(monkeypatch, receipt_calls)
    pools_by_id = _parse_pools()

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(quote_epoch=7),
        server=_Server(),
        parse_pools=lambda: pools_by_id,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert routing_calls == [
        {
            "pools_by_id": pools_by_id,
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 10,
        }
    ]
    assert receipt_calls == [
        {
            "kind": "exact_in",
            "quote": quote,
            "pools_by_id": pools_by_id,
            "quote_epoch": 7,
        }
    ]
    assert writes == [
        (
            200,
            {
                "ok": True,
                "kind": "exact_in",
                "routing_mode": "exact",
                "quote": {"quote": "exact-in"},
                "receipt": {"receipt_hash": "fake-receipt", "quote_epoch": 7},
            },
        )
    ]


def test_quote_exact_out_success_passes_two_hop_gate(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    routing_calls: list[dict[str, object]] = []
    receipt_calls: list[dict[str, object]] = []
    quote = _Quote("exact-out")

    def best_route_exact_out_2hop(**kwargs: object) -> object:
        routing_calls.append(dict(kwargs))
        return quote

    monkeypatch.setattr("src.core.routing.best_route_exact_out_2hop", best_route_exact_out_2hop)
    _install_receipt(monkeypatch, receipt_calls)

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(kind="exact_out", amount_out=6, apply_two_hop_gate=True),
        server=_Server(),
        parse_pools=_parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert routing_calls[0]["amount_out"] == 6
    assert routing_calls[0]["apply_two_hop_gate"] is True
    assert receipt_calls[0]["kind"] == "exact_out"
    assert writes[0][1] == {
        "ok": True,
        "kind": "exact_out",
        "routing_mode": "exact",
        "quote": {"quote": "exact-out"},
        "receipt": {"receipt_hash": "fake-receipt", "quote_epoch": None},
    }


def test_quote_no_route_precedes_quote_epoch_validation(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def best_route_exact_in_2hop(**_kwargs: object) -> None:
        return None

    monkeypatch.setattr("src.core.routing.best_route_exact_in_2hop", best_route_exact_in_2hop)

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(quote_epoch=True),
        server=_Server(),
        parse_pools=_parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "no_route"})]


def test_quote_rejects_bad_quote_epoch_after_route(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def best_route_exact_in_2hop(**_kwargs: object) -> object:
        return _Quote("route")

    monkeypatch.setattr("src.core.routing.best_route_exact_in_2hop", best_route_exact_in_2hop)

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(quote_epoch=True),
        server=_Server(),
        parse_pools=_parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "bad_quote_epoch"})]


def test_quote_fast_exact_in_uses_server_cache_and_fast_mode(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    receipt_calls: list[dict[str, object]] = []
    fast_quote = _Quote("fast-in")
    router = _FastRouter(exact_in=fast_quote)

    def router_factory(*, max_cache_pairs: int) -> _FastRouter:
        assert max_cache_pairs == 32
        return router

    monkeypatch.setattr("src.integration.fast_quote_router_v1.FastQuoteRouterV1", router_factory)
    _install_receipt(monkeypatch, receipt_calls)
    server = _Server()

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(routing_mode="fast_v1", fast_topk_max=9),
        server=server,
        parse_pools=_parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert getattr(server, "fast_quote_router_v1") is router
    assert router.calls[0][0] == "exact_in"
    assert router.calls[0][1]["topk_max"] == 9
    assert receipt_calls[0]["quote"] is fast_quote
    assert writes[0][1]["routing_mode"] == "fast_v1"  # type: ignore[index]


def test_quote_fast_exact_in_reuses_existing_server_cache(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    receipt_calls: list[dict[str, object]] = []
    fast_quote = _Quote("cached-fast-in")
    router = _FastRouter(exact_in=fast_quote)

    def router_factory(*, max_cache_pairs: int) -> _FastRouter:
        raise AssertionError(f"unexpected router construction: {max_cache_pairs}")

    monkeypatch.setattr("src.integration.fast_quote_router_v1.FastQuoteRouterV1", router_factory)
    _install_receipt(monkeypatch, receipt_calls)
    server = _Server()
    server.fast_quote_router_v1 = router

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(routing_mode="fast_v1", fast_topk_max=5),
        server=server,
        parse_pools=_parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert getattr(server, "fast_quote_router_v1") is router
    assert router.calls[0][1]["topk_max"] == 5
    assert receipt_calls[0]["quote"] is fast_quote
    assert writes[0][1]["routing_mode"] == "fast_v1"  # type: ignore[index]


def test_quote_fast_exact_in_exception_falls_back_to_exact(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    receipt_calls: list[dict[str, object]] = []
    exact_quote = _Quote("fallback-in")
    router = _FastRouter(raise_exact_in=True)
    exact_calls: list[dict[str, object]] = []

    def router_factory(*, max_cache_pairs: int) -> _FastRouter:
        assert max_cache_pairs == 32
        return router

    def best_route_exact_in_2hop(**kwargs: object) -> object:
        exact_calls.append(dict(kwargs))
        return exact_quote

    monkeypatch.setattr("src.integration.fast_quote_router_v1.FastQuoteRouterV1", router_factory)
    monkeypatch.setattr("src.core.routing.best_route_exact_in_2hop", best_route_exact_in_2hop)
    _install_receipt(monkeypatch, receipt_calls)

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(routing_mode="fast_v1", fast_topk_max=13),
        server=_Server(),
        parse_pools=_parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert router.calls[0][1]["topk_max"] == 13
    assert exact_calls[0]["amount_in"] == 10
    assert receipt_calls[0]["quote"] is exact_quote
    assert writes[0][1]["routing_mode"] == "exact"  # type: ignore[index]


def test_quote_fast_exact_out_falls_back_to_exact(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    receipt_calls: list[dict[str, object]] = []
    exact_quote = _Quote("fallback-out")
    router = _FastRouter(exact_out=None)
    exact_calls: list[dict[str, object]] = []

    def router_factory(*, max_cache_pairs: int) -> _FastRouter:
        assert max_cache_pairs == 32
        return router

    def best_route_exact_out_2hop(**kwargs: object) -> object:
        exact_calls.append(dict(kwargs))
        return exact_quote

    monkeypatch.setattr("src.integration.fast_quote_router_v1.FastQuoteRouterV1", router_factory)
    monkeypatch.setattr("src.core.routing.best_route_exact_out_2hop", best_route_exact_out_2hop)
    _install_receipt(monkeypatch, receipt_calls)

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(
            kind="exact_out",
            routing_mode="fast_v1",
            amount_out=6,
            fast_topk_max=11,
            apply_two_hop_gate=True,
        ),
        server=_Server(),
        parse_pools=_parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert router.calls[0][0] == "exact_out"
    assert router.calls[0][1]["topk_max"] == 11
    assert router.calls[0][1]["apply_two_hop_gate"] is True
    assert exact_calls[0]["apply_two_hop_gate"] is True
    assert receipt_calls[0]["quote"] is exact_quote
    assert writes[0][1]["routing_mode"] == "exact"  # type: ignore[index]


def test_quote_fast_exact_out_exception_falls_back_to_exact(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    receipt_calls: list[dict[str, object]] = []
    exact_quote = _Quote("fallback-out-exception")
    router = _FastRouter(raise_exact_out=True)
    exact_calls: list[dict[str, object]] = []

    def router_factory(*, max_cache_pairs: int) -> _FastRouter:
        assert max_cache_pairs == 32
        return router

    def best_route_exact_out_2hop(**kwargs: object) -> object:
        exact_calls.append(dict(kwargs))
        return exact_quote

    monkeypatch.setattr("src.integration.fast_quote_router_v1.FastQuoteRouterV1", router_factory)
    monkeypatch.setattr("src.core.routing.best_route_exact_out_2hop", best_route_exact_out_2hop)
    _install_receipt(monkeypatch, receipt_calls)

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(
            kind="exact_out",
            routing_mode="fast_v1",
            amount_out=8,
            fast_topk_max=17,
            apply_two_hop_gate=True,
        ),
        server=_Server(),
        parse_pools=_parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert router.calls[0][1]["topk_max"] == 17
    assert exact_calls[0]["amount_out"] == 8
    assert exact_calls[0]["apply_two_hop_gate"] is True
    assert receipt_calls[0]["quote"] is exact_quote
    assert writes[0][1]["routing_mode"] == "exact"  # type: ignore[index]


def test_quote_receipt_exception_maps_to_quote_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def best_route_exact_in_2hop(**_kwargs: object) -> object:
        return _Quote("route")

    def make_route_quote_receipt(**_kwargs: object) -> dict[str, object]:
        raise RuntimeError("receipt construction failed")

    monkeypatch.setattr("src.core.routing.best_route_exact_in_2hop", best_route_exact_in_2hop)
    monkeypatch.setattr(
        "src.core.quote_receipts.make_route_quote_receipt",
        make_route_quote_receipt,
    )

    handled = maybe_handle_quote_route(
        path="/api/dex/quote",
        obj=_request(),
        server=_Server(),
        parse_pools=_parse_pools,
        quote_to_dict=_quote_to_dict,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "quote_error", "details": "request failed"})]
