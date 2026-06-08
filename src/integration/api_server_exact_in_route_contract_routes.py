from __future__ import annotations

from typing import Any, Callable

from src.integration.api_server_exact_in_route_common import (
    BadRequest,
    parse_exact_in_route_request,
)


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]

_BUILD_ORACLE_CONTRACT_ENDPOINT = "/api/dex/build_exact_in_route_oracle_contract"
_VERIFY_ORACLE_CONTRACT_ENDPOINT = "/api/dex/verify_exact_in_route_oracle_contract"
_ORACLE_CONTRACT_SCHEMA = "zenodex/exact-in-route-oracle-contract/v1"


def _write_build_success(write_json: WriteJson, contract: object) -> None:
    write_json(
        200,
        {
            "ok": True,
            "contract_schema": _ORACLE_CONTRACT_SCHEMA,
            "verify_contract_endpoint": _VERIFY_ORACLE_CONTRACT_ENDPOINT,
            "contract": contract.to_dict(),
        },
    )


def _handle_build_oracle_contract(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        pools_by_id = parse_pools()
        req = parse_exact_in_route_request(obj)
        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_in_route_oracle_contract,
        )

        contract = build_exact_in_route_oracle_contract(
            pools_by_id=pools_by_id,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_in=req.amount_in,
            split_search_profile=req.split_search_profile,
            enable_mixed_direct_twohop_split=req.enable_mixed_direct_twohop_split,
            binding_ok=req.binding_ok,
        )
        _write_build_success(write_json, contract)
    except BadRequest as exc:
        write_json(400, {"ok": False, "error": exc.error})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "build_exact_in_route_oracle_contract_error", "details": "request failed"},
        )


def _handle_verify_oracle_contract(obj: dict[str, object], write_json: WriteJson) -> None:
    contract = obj.get("contract")
    if not isinstance(contract, dict):
        write_json(400, {"ok": False, "error": "bad_contract"})
        return
    try:
        from src.integration.exact_in_route_certificate import (  # pylint: disable=import-outside-toplevel
            verify_exact_in_route_oracle_contract_payload,
        )

        ok, err = verify_exact_in_route_oracle_contract_payload(contract)
        write_json(200, {"ok": bool(ok), "error": err})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "verify_exact_in_route_oracle_contract_error", "details": "request failed"},
        )


def maybe_handle_exact_in_route_contract_route(
    *,
    path: str,
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> bool:
    if path == _BUILD_ORACLE_CONTRACT_ENDPOINT:
        _handle_build_oracle_contract(obj, parse_pools, write_json)
        return True
    if path == _VERIFY_ORACLE_CONTRACT_ENDPOINT:
        _handle_verify_oracle_contract(obj, write_json)
        return True
    return False
