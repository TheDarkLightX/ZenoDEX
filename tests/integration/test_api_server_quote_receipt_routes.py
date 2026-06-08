from __future__ import annotations

import builtins
from typing import Any

from src.integration.api_server_quote_receipt_routes import maybe_handle_quote_receipt_route


def _capture() -> tuple[list[tuple[int, object]], Any]:
    writes: list[tuple[int, object]] = []

    def write_json(status: int, payload: object) -> None:
        writes.append((status, payload))

    return writes, write_json


def _parse_pools() -> dict[str, object]:
    return {"pool_a": object()}


def _receipt() -> dict[str, object]:
    return {"body": {"kind": "exact_in"}, "receipt_hash": "fake"}


def _fail_on_quote_receipt_import(monkeypatch: Any) -> None:
    real_import = builtins.__import__

    def guarded_import(
        name: str,
        globals: Any = None,
        locals: Any = None,
        fromlist: Any = (),
        level: int = 0,
    ) -> object:
        if name == "src.core.quote_receipts":
            raise AssertionError("quote receipt verifier imported before cheap validation")
        return real_import(name, globals, locals, fromlist, level)

    monkeypatch.setattr(builtins, "__import__", guarded_import)


def test_unknown_quote_receipt_route_is_not_handled() -> None:
    writes, write_json = _capture()

    handled = maybe_handle_quote_receipt_route(
        path="/api/dex/not_verify_quote_receipt",
        obj={},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is False
    assert writes == []


def test_quote_receipt_rejects_bad_receipt_before_parse_or_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    parse_called = False
    _fail_on_quote_receipt_import(monkeypatch)

    def parse_pools() -> dict[str, object]:
        nonlocal parse_called
        parse_called = True
        return {}

    handled = maybe_handle_quote_receipt_route(
        path="/api/dex/verify_quote_receipt",
        obj={"receipt": []},
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is False
    assert writes == [(400, {"ok": False, "error": "bad_receipt"})]


def test_quote_receipt_rejects_bad_expected_epoch_before_parse_or_import(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    parse_called = False
    _fail_on_quote_receipt_import(monkeypatch)

    def parse_pools() -> dict[str, object]:
        nonlocal parse_called
        parse_called = True
        return {}

    handled = maybe_handle_quote_receipt_route(
        path="/api/dex/verify_quote_receipt",
        obj={"receipt": _receipt(), "expected_quote_epoch": True},
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert parse_called is False
    assert writes == [(400, {"ok": False, "error": "bad_expected_quote_epoch"})]


def test_quote_receipt_parse_failure_uses_legacy_verify_error() -> None:
    writes, write_json = _capture()

    def parse_pools() -> dict[str, object]:
        raise ValueError("pools must be a non-empty list")

    handled = maybe_handle_quote_receipt_route(
        path="/api/dex/verify_quote_receipt",
        obj={"receipt": _receipt()},
        parse_pools=parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "verify_error", "details": "request failed"})]


def test_quote_receipt_success_payload_and_verifier_args(monkeypatch: Any) -> None:
    writes, write_json = _capture()
    verifier_calls: list[dict[str, object]] = []

    def verify_route_quote_receipt(
        receipt: dict[str, object],
        *,
        pools_by_id: dict[str, object],
        expected_quote_epoch: int | None,
    ) -> tuple[bool, str]:
        verifier_calls.append(
            {
                "receipt": receipt,
                "pools_by_id": pools_by_id,
                "expected_quote_epoch": expected_quote_epoch,
            }
        )
        return True, "ok"

    monkeypatch.setattr(
        "src.core.quote_receipts.verify_route_quote_receipt",
        verify_route_quote_receipt,
    )
    pools_by_id = _parse_pools()
    receipt = _receipt()

    handled = maybe_handle_quote_receipt_route(
        path="/api/dex/verify_quote_receipt",
        obj={"receipt": receipt, "expected_quote_epoch": 7},
        parse_pools=lambda: pools_by_id,
        write_json=write_json,
    )

    assert handled is True
    assert verifier_calls == [
        {
            "receipt": receipt,
            "pools_by_id": pools_by_id,
            "expected_quote_epoch": 7,
        }
    ]
    assert writes == [(200, {"ok": True, "error": "ok"})]


def test_quote_receipt_false_none_error_is_stringified(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify_route_quote_receipt(
        _receipt: dict[str, object],
        *,
        pools_by_id: dict[str, object],
        expected_quote_epoch: int | None,
    ) -> tuple[bool, None]:
        assert pools_by_id
        assert expected_quote_epoch is None
        return False, None

    monkeypatch.setattr(
        "src.core.quote_receipts.verify_route_quote_receipt",
        verify_route_quote_receipt,
    )

    handled = maybe_handle_quote_receipt_route(
        path="/api/dex/verify_quote_receipt",
        obj={"receipt": _receipt()},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(200, {"ok": False, "error": "None"})]


def test_quote_receipt_verifier_exception_uses_legacy_verify_error(monkeypatch: Any) -> None:
    writes, write_json = _capture()

    def verify_route_quote_receipt(
        _receipt: dict[str, object],
        *,
        pools_by_id: dict[str, object],
        expected_quote_epoch: int | None,
    ) -> tuple[bool, str]:
        raise RuntimeError("internal detail must not leak")

    monkeypatch.setattr(
        "src.core.quote_receipts.verify_route_quote_receipt",
        verify_route_quote_receipt,
    )

    handled = maybe_handle_quote_receipt_route(
        path="/api/dex/verify_quote_receipt",
        obj={"receipt": _receipt()},
        parse_pools=_parse_pools,
        write_json=write_json,
    )

    assert handled is True
    assert writes == [(400, {"ok": False, "error": "verify_error", "details": "request failed"})]
