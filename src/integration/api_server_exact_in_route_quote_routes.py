from __future__ import annotations

from typing import Any, Callable

from src.integration.api_server_exact_in_route_common import (
    BadRequest,
    parse_exact_in_route_request,
)


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]
CheckOracleBridge = Callable[..., str | None]

_QUOTE_EXACT_IN_ROUTE_ENDPOINT = "/api/dex/quote_exact_in_route_guarded"


def _handle_quote_exact_in_route_guarded(
    obj: dict[str, object],
    parse_pools: ParsePools,
    check_oracle_bridge: CheckOracleBridge,
    write_json: WriteJson,
) -> None:
    try:
        pools_by_id = parse_pools()
        req = parse_exact_in_route_request(obj)
        bridge_err = check_oracle_bridge(
            body=obj,
            path=_QUOTE_EXACT_IN_ROUTE_ENDPOINT,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_in=req.amount_in,
            split_search_profile=req.split_search_profile,
            enable_mixed_direct_twohop_split=req.enable_mixed_direct_twohop_split,
            binding_ok=req.binding_ok,
        )
        if bridge_err is not None:
            write_json(400, {"ok": False, "error": "rejected", "detail": bridge_err})
            return

        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            quote_exact_in_route_guarded,
        )

        quote, err, contract = quote_exact_in_route_guarded(
            pools_by_id=pools_by_id,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_in=req.amount_in,
            split_search_profile=req.split_search_profile,
            enable_mixed_direct_twohop_split=req.enable_mixed_direct_twohop_split,
            binding_ok=req.binding_ok,
        )
        response = {"ok": quote is not None, "contract": contract.to_dict(), "error": err}
        if quote is not None:
            response["quote"] = contract.to_dict()["runtime_quote"]
        write_json(200, response)
    except BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "quote_exact_in_route_guarded_error", "details": "request failed"},
        )


def maybe_handle_exact_in_route_quote_route(
    *,
    path: str,
    obj: dict[str, object],
    parse_pools: ParsePools,
    check_oracle_bridge: CheckOracleBridge,
    write_json: WriteJson,
) -> bool:
    if path != _QUOTE_EXACT_IN_ROUTE_ENDPOINT:
        return False
    _handle_quote_exact_in_route_guarded(obj, parse_pools, check_oracle_bridge, write_json)
    return True
