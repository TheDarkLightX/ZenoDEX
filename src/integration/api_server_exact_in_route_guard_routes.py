from __future__ import annotations

from typing import Any, Callable

from src.integration.api_server_exact_in_route_common import (
    BadRequest,
    parse_exact_in_route_request,
)


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]

_GUARD_EXACT_IN_ROUTE_ENDPOINT = "/api/dex/guard_exact_in_route_canonicality"


def _handle_guard_exact_in_route(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        pools_by_id = parse_pools()
        req = parse_exact_in_route_request(obj)
        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            guard_exact_in_route_runtime_canonicality,
        )

        ok, err, contract = guard_exact_in_route_runtime_canonicality(
            pools_by_id=pools_by_id,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_in=req.amount_in,
            split_search_profile=req.split_search_profile,
            enable_mixed_direct_twohop_split=req.enable_mixed_direct_twohop_split,
            binding_ok=req.binding_ok,
        )
        write_json(200, {"ok": bool(ok), "contract": contract.to_dict(), "error": err})
    except BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "guard_exact_in_route_canonicality_error", "details": "request failed"},
        )


def maybe_handle_exact_in_route_guard_route(
    *,
    path: str,
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> bool:
    if path != _GUARD_EXACT_IN_ROUTE_ENDPOINT:
        return False
    _handle_guard_exact_in_route(obj, parse_pools, write_json)
    return True
