from __future__ import annotations

from typing import Any, Callable


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]

_VERIFY_QUOTE_RECEIPT_ENDPOINT = "/api/dex/verify_quote_receipt"


class _BadRequest(Exception):
    def __init__(self, error: str) -> None:
        super().__init__(error)
        self.error = error


def _expected_quote_epoch(obj: dict[str, object]) -> int | None:
    expected_quote_epoch = obj.get("expected_quote_epoch")
    if expected_quote_epoch is None:
        return None
    if (
        not isinstance(expected_quote_epoch, int)
        or isinstance(expected_quote_epoch, bool)
        or expected_quote_epoch < 0
    ):
        raise _BadRequest("bad_expected_quote_epoch")
    return int(expected_quote_epoch)


def _handle_verify_quote_receipt(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    receipt = obj.get("receipt")
    if not isinstance(receipt, dict):
        write_json(400, {"ok": False, "error": "bad_receipt"})
        return
    try:
        expected_quote_epoch = _expected_quote_epoch(obj)
    except _BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
        return
    try:
        pools_by_id = parse_pools()
        from src.core.quote_receipts import verify_route_quote_receipt  # pylint: disable=import-outside-toplevel

        ok, err = verify_route_quote_receipt(
            receipt,
            pools_by_id=pools_by_id,
            expected_quote_epoch=expected_quote_epoch,
        )
        write_json(200, {"ok": bool(ok), "error": str(err)})
    except Exception:
        write_json(400, {"ok": False, "error": "verify_error", "details": "request failed"})


def maybe_handle_quote_receipt_route(
    *,
    path: str,
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> bool:
    if path != _VERIFY_QUOTE_RECEIPT_ENDPOINT:
        return False
    _handle_verify_quote_receipt(obj, parse_pools, write_json)
    return True
