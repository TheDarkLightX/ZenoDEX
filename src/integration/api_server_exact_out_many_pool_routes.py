from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable


WriteJson = Callable[[int, object], None]
ParsePools = Callable[[], dict[str, Any]]
RouteHandler = Callable[[dict[str, object], ParsePools, WriteJson], None]

_CANDIDATE_DOMAIN_ENDPOINT = "/api/dex/build_exact_out_many_pool_candidate_domain_contract"
_PREFILTER_ENDPOINT = "/api/dex/build_exact_out_many_pool_prefilter_contract"
_REPAIRED_PREFILTER_ENDPOINT = "/api/dex/build_exact_out_many_pool_repaired_prefilter_contract"
_REPAIRED_SELECTED_DOMAIN_ENDPOINT = (
    "/api/dex/build_exact_out_many_pool_repaired_selected_domain_oracle_contract"
)
_REPAIRED_SELECTED_DOMAIN_QUOTE_ENDPOINT = "/api/dex/quote_exact_out_many_pool_repaired_selected_domain"

_DEFAULTS = {
    "max_legs": 3,
    "max_candidate_pools": 5,
    "max_candidates": 12,
    "max_iters": 4096,
    "window": 64,
    "brute_force_max": 512,
    "max_full_domain_pools": 8,
    "max_enumerated_candidates": 20_000,
}

_MIN_VALUES = {
    "amount_out_total": 1,
    "max_legs": 1,
    "max_candidate_pools": 1,
    "max_candidates": 1,
    "max_iters": 1,
    "window": 0,
    "brute_force_max": 0,
    "max_full_domain_pools": 1,
    "max_enumerated_candidates": 1,
}


class _BadRequest(ValueError):
    def __init__(self, error: str) -> None:
        super().__init__(error)
        self.error = error


@dataclass(frozen=True)
class _ExactOutManyPoolRequest:
    pools: list[Any]
    asset_in: str
    asset_out: str
    values: dict[str, int]


def _require_asset_pair(obj: dict[str, object]) -> tuple[str, str]:
    asset_in = str(obj.get("asset_in", "")).strip()
    asset_out = str(obj.get("asset_out", "")).strip()
    if not asset_in or not asset_out or asset_in == asset_out:
        raise _BadRequest("bad_assets")
    return asset_in, asset_out


def _require_int(obj: dict[str, object], name: str) -> int:
    value = obj.get(name, _DEFAULTS.get(name))
    if not isinstance(value, int) or isinstance(value, bool) or value < _MIN_VALUES[name]:
        raise _BadRequest(f"bad_{name}")
    return int(value)


def _parse_request(
    obj: dict[str, object],
    parse_pools: ParsePools,
    field_names: tuple[str, ...],
) -> _ExactOutManyPoolRequest:
    pools = list(parse_pools().values())
    asset_in, asset_out = _require_asset_pair(obj)
    values = {name: _require_int(obj, name) for name in field_names}
    return _ExactOutManyPoolRequest(
        pools=pools,
        asset_in=asset_in,
        asset_out=asset_out,
        values=values,
    )


def _write_bad_request(write_json: WriteJson, exc: _BadRequest) -> None:
    write_json(400, {"ok": False, "error": exc.error})


def _handle_candidate_domain_contract(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        req = _parse_request(
            obj, parse_pools, ("amount_out_total", "max_legs", "max_candidate_pools", "max_enumerated_candidates")
        )
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA,
            build_exact_out_many_pool_candidate_domain_contract,
        )

        contract = build_exact_out_many_pool_candidate_domain_contract(
            req.pools,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_out_total=req.values["amount_out_total"],
            max_legs=req.values["max_legs"],
            max_candidate_pools=req.values["max_candidate_pools"],
            max_enumerated_candidates=req.values["max_enumerated_candidates"],
        )
        write_json(
            200,
            {
                "ok": True,
                "contract": contract.to_dict(),
                "contract_schema": EXACT_OUT_MANY_POOL_CANDIDATE_DOMAIN_CONTRACT_SCHEMA,
                "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_candidate_domain_contract",
            },
        )
    except _BadRequest as exc:
        _write_bad_request(write_json, exc)
    except Exception:
        write_json(
            400,
            {
                "ok": False,
                "error": "build_exact_out_many_pool_candidate_domain_contract_error",
                "details": "request failed",
            },
        )


def _handle_prefilter_contract(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        req = _parse_request(obj, parse_pools, ("amount_out_total", "max_legs", "max_candidate_pools"))
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA,
            build_exact_out_many_pool_prefilter_contract,
        )

        contract = build_exact_out_many_pool_prefilter_contract(
            req.pools,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_out_total=req.values["amount_out_total"],
            max_legs=req.values["max_legs"],
            max_candidate_pools=req.values["max_candidate_pools"],
        )
        write_json(
            200,
            {
                "ok": True,
                "contract": contract.to_dict(),
                "contract_schema": EXACT_OUT_MANY_POOL_PREFILTER_CONTRACT_SCHEMA,
                "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_prefilter_contract",
            },
        )
    except _BadRequest as exc:
        _write_bad_request(write_json, exc)
    except Exception:
        write_json(400, {"ok": False, "error": "build_exact_out_many_pool_prefilter_contract_error", "details": "request failed"})


def _handle_repaired_prefilter_contract(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        req = _parse_request(
            obj,
            parse_pools,
            (
                "amount_out_total",
                "max_legs",
                "max_candidate_pools",
                "max_full_domain_pools",
                "max_enumerated_candidates",
            ),
        )
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA,
            build_exact_out_many_pool_repaired_prefilter_contract,
        )

        contract = build_exact_out_many_pool_repaired_prefilter_contract(
            req.pools,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            amount_out_total=req.values["amount_out_total"],
            max_legs=req.values["max_legs"],
            max_candidate_pools=req.values["max_candidate_pools"],
            max_full_domain_pools=req.values["max_full_domain_pools"],
            max_enumerated_candidates=req.values["max_enumerated_candidates"],
        )
        write_json(
            200,
            {
                "ok": True,
                "contract": contract.to_dict(),
                "contract_schema": EXACT_OUT_MANY_POOL_REPAIRED_PREFILTER_CONTRACT_SCHEMA,
                "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_prefilter_contract",
            },
        )
    except _BadRequest as exc:
        _write_bad_request(write_json, exc)
    except Exception:
        write_json(
            400,
            {
                "ok": False,
                "error": "build_exact_out_many_pool_repaired_prefilter_contract_error",
                "details": "request failed",
            },
        )


def _handle_repaired_selected_domain_contract(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        req = _parse_request(obj, parse_pools, tuple(_MIN_VALUES))
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA,
            build_exact_out_many_pool_repaired_selected_domain_oracle_contract,
        )

        contract = build_exact_out_many_pool_repaired_selected_domain_oracle_contract(
            req.pools,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            **req.values,
        )
        write_json(
            200,
            {
                "ok": True,
                "contract": contract.to_dict(),
                "contract_schema": EXACT_OUT_MANY_POOL_REPAIRED_SELECTED_DOMAIN_ORACLE_CONTRACT_SCHEMA,
                "quote_endpoint": "/api/dex/quote_exact_out_many_pool_repaired_selected_domain",
                "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract",
            },
        )
    except _BadRequest as exc:
        _write_bad_request(write_json, exc)
    except Exception:
        write_json(
            400,
            {
                "ok": False,
                "error": "build_exact_out_many_pool_repaired_selected_domain_oracle_contract_error",
                "details": "request failed",
            },
        )


def _repaired_selected_domain_quote_payload(
    *,
    quote: object,
    err: object,
    contract_payload: dict[str, object],
) -> dict[str, object]:
    payload = {
        "ok": bool(quote is not None),
        "quote_policy": "repaired_selected_domain_v1",
        "contract": contract_payload,
        "contract_schema": contract_payload["schema"],
        "build_contract_endpoint": "/api/dex/build_exact_out_many_pool_repaired_selected_domain_oracle_contract",
        "verify_contract_endpoint": "/api/dex/verify_exact_out_many_pool_repaired_selected_domain_oracle_contract",
        "repaired_selected_pool_ids": contract_payload["repaired_selected_pool_ids"],
        "repaired_selected_domain_matches_full_canonical": contract_payload[
            "repaired_selected_domain_matches_full_canonical"
        ],
        "audit_pool_ids_match_repaired_selected_pool_ids": contract_payload[
            "audit_pool_ids_match_repaired_selected_pool_ids"
        ],
        "repaired_selected_domain_runtime_quote": contract_payload["repaired_selected_domain_runtime_quote"],
        "repaired_selected_domain_runtime_projected_path": contract_payload[
            "repaired_selected_domain_runtime_projected_path"
        ],
        "repaired_selected_domain_canonical_projected_path": contract_payload[
            "repaired_selected_domain_canonical_projected_path"
        ],
        "repaired_selected_domain_runtime_matches_canonical": contract_payload[
            "repaired_selected_domain_runtime_matches_canonical"
        ],
        "repaired_projection_cover_available": contract_payload["repaired_projection_cover_available"],
        "repaired_projection_cover_holds": contract_payload["repaired_projection_cover_holds"],
        "replacement_quote_matches_full_canonical": contract_payload["replacement_quote_matches_full_canonical"],
    }
    if quote is not None:
        payload["quote"] = contract_payload["repaired_selected_domain_runtime_quote"]
    else:
        payload["error"] = str(err or "many_pool_repaired_selected_domain_unavailable")
    return payload


def _handle_repaired_selected_domain_quote(
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> None:
    try:
        req = _parse_request(obj, parse_pools, tuple(_MIN_VALUES))
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            quote_exact_out_many_pool_repaired_selected_domain,
        )

        quote, err, contract = quote_exact_out_many_pool_repaired_selected_domain(
            req.pools,
            asset_in=req.asset_in,
            asset_out=req.asset_out,
            **req.values,
        )
        payload = _repaired_selected_domain_quote_payload(
            quote=quote,
            err=err,
            contract_payload=contract.to_dict(),
        )
        write_json(200, payload)
    except _BadRequest as exc:
        _write_bad_request(write_json, exc)
    except Exception:
        write_json(
            400,
            {
                "ok": False,
                "error": "quote_exact_out_many_pool_repaired_selected_domain_error",
                "details": "request failed",
            },
        )


def maybe_handle_exact_out_many_pool_route(
    *,
    path: str,
    obj: dict[str, object],
    parse_pools: ParsePools,
    write_json: WriteJson,
) -> bool:
    handler = _ROUTE_HANDLERS.get(path)
    if handler is None:
        return False
    handler(obj, parse_pools, write_json)
    return True


_ROUTE_HANDLERS: dict[str, RouteHandler] = {
    _CANDIDATE_DOMAIN_ENDPOINT: _handle_candidate_domain_contract,
    _PREFILTER_ENDPOINT: _handle_prefilter_contract,
    _REPAIRED_PREFILTER_ENDPOINT: _handle_repaired_prefilter_contract,
    _REPAIRED_SELECTED_DOMAIN_ENDPOINT: _handle_repaired_selected_domain_contract,
    _REPAIRED_SELECTED_DOMAIN_QUOTE_ENDPOINT: _handle_repaired_selected_domain_quote,
}
